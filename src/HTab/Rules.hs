module HTab.Rules
(
Rule(..),BranchModification(..),
applicableRule, applyRule, ruleToId,
applyMod,
get_pr_disjunt_rule, 
) where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe ( listToMaybe, catMaybes )

import qualified HTab.DMap as DMap

import HTab.Formula( Formula(..), PrFormula(..), showLess, neg, Atom(..),
                     Dependency, DependencySet, dsUnion, dsInsert, dsEmpty,
                     prefix, AccFormula(..),
                     Prefix, NomSymbol(..), PropSymbol(..), RelSymbol(..),
                     disj, conj, nom, prop, replaceVar )
import HTab.Branch( Branch(..), createNewPref, createNewProp, createNewNomTestRelevance,
                    BranchInfo(..),
                    addFormulas, addAccFormula,
                    addDiaRuleCheck, addDiaXRuleCheck,
                    addDownRuleCheck, addDiffRuleCheck,
                    addParentPrefix, reduceDisjunctionAgainstBranch,
                    getUnappliedUBPairs, updateUBBookKeep,
                    getUrfatherAndDeps, isNotBlocked, merge,
                    diaAlreadyDone,  diaXAlreadyDone, downAlreadyDone, incPropSymbol, incNomSymbol,
                    ReducedDisjunct(..), newPropBaseName, newNomBaseName,
                    ScheduledRule(..), TodoList(..),
                    deleteUEV, insertUEV_addFormula )
import HTab.CommandLine(CmdLineParams, semBranch, unitProp, strategyStr, uBlocking)
import HTab.RuleMetadata(RuleId(..))
import qualified HTab.DisjSet as DS

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix Formula
                           | BM_AddDiaXRuleCheck Prefix (RelSymbol,Formula)
                           | BM_AddDownRuleCheck Prefix Formula
                           | BM_AddDiffRuleCheck Formula PropSymbol Bool
                           | BM_CreateNewPref
                           | BM_CreateNewProp
                           | BM_CreateNewNomTestRelevance Formula
                           | BM_AddParentPrefix Prefix Prefix
                           | BM_Clash DependencySet PrFormula
                           | BM_UpdateUBBookKeep Prefix Prefix
                           | BM_DeleteUEV Int
                           | BM_InsertUEV_addFormula (Maybe Int) DependencySet (Int -> PrFormula)
                           | BM_Merge Prefix DS.Pointer DependencySet

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  DiaRule    PrFormula AccFormula PrFormula        -- creates a prefix
           | DiaXRule   PrFormula Dependency
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | AtRule     PrFormula PrFormula
           | DownRule   PrFormula PrFormula PrFormula
           | DiffRule   (Prefix, DependencySet, Formula)
           | ExistModRule PrFormula PrFormula                 -- creates a prefix
           | DiscardRule PrFormula
           | ClashRule DependencySet PrFormula
           | UBlockRule Prefix Prefix [PrFormula] [PrFormula]
           | MergeRule Prefix DS.Pointer DependencySet

-- from the description of a rule application, creates the list of lists of modifications to the branch
-- for certain rules, we need to look in the branch to see what modifications we do

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ClashRule ds f) = [[BM_Clash ds f]]


getMods _ (MergeRule p n ds)=
 [[BM_Merge p n ds]]

getMods _ (DiaRule (PrFormula pr _ f) acctoadd@(AccFormula _ _ p1 p2) toadd) =
 [[BM_AddParentPrefix p2 p1,
   BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd],
   BM_AddDiaRuleCheck pr f,
   BM_CreateNewPref]]

getMods _ (DiaXRule (PrFormula pr ds (DiaX mi r ev)) dep)=
 [[BM_AddFormulas [PrFormula pr ds2 ev],
   BM_AddDiaXRuleCheck pr (r,ev)]
   ++ case mi of { Nothing  -> [] ;
                   Just idx -> [BM_DeleteUEV idx]
                 }
  ,
  [BM_AddDiaXRuleCheck pr (r,ev),
   BM_InsertUEV_addFormula mi ds2
                           (\i -> PrFormula pr ds2 ((neg ev) `conj` (Dia r $ DiaX (Just i) r ev)))]
 ]
     where ds2 = dsInsert dep ds

getMods _ (DiaXRule _ _)= error "getMods DiaXRule"

getMods _ (ExistModRule _ toadd) =
 [[BM_AddFormulas [toadd],
   BM_CreateNewPref]]

getMods _ (UBlockRule p1 p2 choiceEqual choiceDisequal) =
 [[BM_UpdateUBBookKeep p1 p2, BM_AddFormulas choiceEqual],
  [BM_UpdateUBBookKeep p1 p2, BM_AddFormulas choiceDisequal]
 ]

getMods _ (DisjRule _ toadds) =
 [[BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule _ toaddss) =
 [[BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (AtRule _ toadd) =
 [[BM_AddFormulas [toadd]]]

getMods _ (DownRule (PrFormula pr _ f) toadd1 toadd2) =
 [[BM_CreateNewNomTestRelevance f,  --  order  --  what about using a monadic
   BM_AddFormulas [toadd1, toadd2], -- matters -- writing for the getMods functions ?
   BM_AddDownRuleCheck pr f
 ]]

getMods br (DiffRule (pr, ds , f2)) =
 case Map.lookup f2 (dDiaRlCh br) of
  Nothing -> [[BM_CreateNewPref, BM_CreateNewProp,
               BM_AddFormulas [PrFormula newPref ds f2,
                               PrFormula newPref ds (prop newProp),
                               PrFormula pr      ds (neg $ prop newProp)],
               BM_AddDiffRuleCheck f2 newProp False
             ]]
              where newPref = getNewPref br
                    newProp = getNewProp br

  Just (diffProp,doneTwiceBool)
          -> -- the "different place" for this D-formula has already been created
                   case DMap.lookup pr (P diffProp) (clashStr br) of -- are we already at the "different place" ?
                    Nothing -> [[BM_AddFormulas [PrFormula pr ds (disj (neg $ prop diffProp) (D f2))]
                                 -- no, so mark oneself as different from the "different place"; and when it is no longer true,
                                 -- we will generate another different world
                               ]]
                    Just (bool_,ds_) ->
                     if bool_ && not doneTwiceBool -- we need to create a "second different place"
                      then
                        let newPref = getNewPref br
                            newProp = getNewProp br
                        in
                        [[BM_CreateNewPref, BM_CreateNewProp,
                          BM_AddFormulas [PrFormula newPref (dsUnion ds ds_) f2,
                                          PrFormula newPref (dsUnion ds ds_) (prop newProp),
                                          PrFormula pr      (dsUnion ds ds_) (neg $ prop newProp)],
                          BM_AddDiffRuleCheck f2 newProp True
                        ]]
                      else [[]]

getMods _ (DiscardRule _) = [[]]


instance Show Rule where
   show (MergeRule pr po _)        = "merge:              " ++ show (pr,po)
   show (DiaRule   todelete _ _ )  = "diamond:            " ++ showLess todelete
   show (DiaXRule  todelete _)     = "diamondX:           " ++ showLess todelete
   show (DisjRule  todelete _ )    = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )    = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete _ )    = "at:                 " ++ showLess todelete
   show (DownRule  todelete _ _ )  = "down:               " ++ showLess todelete
   show (ExistModRule todelete _)  = "E:                  " ++ showLess todelete
   show (DiffRule (pr,_,f) )       = "D:                  " ++ show pr ++ ":" ++ show f
   show (DiscardRule todelete)     = "Discard:            " ++ showLess todelete
   show (ClashRule bprs f)         = "Clash:              " ++ show bprs ++ " " ++ show f
   show (UBlockRule p1 p2 _ _ )    = "Unrestricted blocking " ++ show (p1,p2)

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (MergeRule _ _ _)  -> R_Merge
              (DiaRule _ _ _)    -> R_Dia
              (DiaXRule _ _)     -> R_DiaX
              (DisjRule _ _)     -> R_Disj
              (SemBrRule _ _)    -> R_SemBr
              (AtRule _ _ )      -> R_At
              (DownRule _ _ _)   -> R_Down
              (ExistModRule _ _) -> R_Exist
              (DiffRule _ )      -> R_Diff
              (DiscardRule _)    -> R_Discard
              (ClashRule _ _)    -> R_Clash
              (UBlockRule _ _ _ _) -> R_UBlocking

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRule :: Branch -> CmdLineParams -> Dependency -> Maybe (Rule,TodoList)
applicableRule br clp d =
 case todoList br of
  Fair [] -> Nothing
  Fair (sr:tl) -> Just (scheduledRuleToRule br clp d sr, Fair tl)
  _        ->  listToMaybe $ catMaybes $ map (ruleByChar br clp d) (strategyStr clp)

scheduledRuleToRule :: Branch -> CmdLineParams -> Dependency -> ScheduledRule -> Rule
scheduledRuleToRule _ _ d (SR_UBlocking p1 p2) = ubRule p1 p2 d
scheduledRuleToRule _ _ _ (SR_Merge pr po ds)  = MergeRule pr po ds
scheduledRuleToRule br clp d (SR_Formula pf@(PrFormula _ _ f2)) =
 case f2 of
  Dis _     -> if semBranch clp then semBrRule clp pf br d else disjRule clp pf br d
  Dia _ _   -> diaRule pf br
  DiaX _ _ _-> diaXRule pf br d
  At _ _    -> atRule pf br
  Down _ _  -> downRule pf br
  E _       -> existRule pf br
  D _       -> diffRule pf
  _         -> error "scheduledRuleToRule, incorrect formula kind"

ruleByChar :: Branch -> CmdLineParams -> Dependency -> Char -> Maybe (Rule,TodoList)
ruleByChar br clp d char =
 case char of
  'm' -> applicableMergeRule
  'o' -> applicableDisjRule
  'd' -> applicableDiaRule
  't' -> applicableDiaXRule
  's' -> applicableAtRule
  'e' -> applicableExistRule
  'D' -> applicableDiffRule
  'b' -> applicableDownRule
  'u' -> if uBlocking clp then applicableUBlockRule else Nothing
  _   -> error "ruleByChar"
 where
  todos  = todoList br
  applicableDiaRule   = case [ f | f@(PrFormula pr _ _) <- Set.toAscList $ diaStr todos,
                                    isNotBlocked br pr] of
                           []    -> Nothing
                           (f:_) -> Just (diaRule f br, todos{diaStr = Set.delete f $ diaStr todos})

  applicableDiaXRule  = do (f,new) <- Set.minView $ diaXStr todos
                           return (diaXRule f br d, todos{diaXStr = new})

  applicableAtRule    = do (f,new) <- Set.minView $ atStr todos
                           return (atRule f br, todos{atStr = new})

  applicableDownRule  = do (f,new) <- Set.minView $ downStr todos
                           return (downRule f br, todos{downStr = new})

  applicableExistRule = do (f,new) <- Set.minView $ existStr todos
                           return (existRule f br, todos{existStr = new})

  applicableDiffRule  = do (f,new) <- Set.minView $ diffStr todos
                           return (diffRule f, todos{diffStr = new})

  applicableUBlockRule = case getUnappliedUBPairs br of
                            []          -> Nothing
                            ((p1,p2):_) -> Just (ubRule p1 p2 d, todos)

  applicableMergeRule  = do ((ds,p,po),new) <- Set.minView $ mergeStr todos
                            return (MergeRule p po ds, todos{mergeStr = new})

  applicableDisjRule
   =  if semBranch clp then do (f,new) <- Set.minView $ disjStr todos
                               return (semBrRule clp f br d, todos{disjStr = new})
                       else do (f,new) <- Set.minView $ disjStr todos
                               return (disjRule clp f br d,  todos{disjStr = new})

applyRule :: CmdLineParams -> Rule -> Branch -> TodoList -> [BranchInfo]
applyRule clp rule br_ todo
 = map (applyMods clp br) (getMods br rule)
   where br = br_{todoList = todo}

applyMods :: CmdLineParams -> Branch -> [BranchModification] -> BranchInfo
applyMods clp br (hd:tl)
  = case (applyMod clp br hd) of
      BranchOK br2             -> applyMods clp br2 tl
      si@(BranchClash _ _ _ _) -> si
applyMods _ br [] = BranchOK br


applyMod :: CmdLineParams -> Branch -> BranchModification -> BranchInfo
applyMod clp br (BM_AddFormulas li)                = addFormulas clp br li
applyMod clp br (BM_AddAccFormula accFor)          = addAccFormula clp br accFor
applyMod  _  br (BM_AddDiaRuleCheck pr f)          = BranchOK $ addDiaRuleCheck br pr f
applyMod  _  br (BM_AddDiaXRuleCheck pr (r,f))     = BranchOK $ addDiaXRuleCheck br pr (r,f)
applyMod  _  br (BM_AddDownRuleCheck pr f)         = BranchOK $ addDownRuleCheck br pr f
applyMod clp br (BM_CreateNewPref)                 = createNewPref clp br
applyMod  _  br (BM_CreateNewProp)                 = BranchOK $ createNewProp br
applyMod  _  br (BM_CreateNewNomTestRelevance f)   = BranchOK $ createNewNomTestRelevance br f
applyMod  _  br (BM_AddDiffRuleCheck f pr b)       = BranchOK $ addDiffRuleCheck br f pr b
applyMod  _  br (BM_AddParentPrefix son father)    = BranchOK $ addParentPrefix br son father
applyMod  _  br (BM_Clash ds (PrFormula pr ds2 f)) = BranchClash br pr (dsUnion ds ds2) f
applyMod  _  br (BM_UpdateUBBookKeep p1 p2)        = BranchOK $ updateUBBookKeep p1 p2 br
applyMod  _  br (BM_DeleteUEV i)                   = BranchOK $ deleteUEV br i
applyMod clp br (BM_InsertUEV_addFormula mi ds ff) = insertUEV_addFormula br clp mi ds ff
applyMod clp br (BM_Merge pr p ds)                 = merge clp br pr ds p


-- the actual rules and their helper functions

-- dia (may create a discard rule)
diaRule :: PrFormula -> Branch -> Rule
diaRule f@(PrFormula pr ds (Dia r f2)) br
  = if diaAlreadyDone br f
     then DiscardRule f
     else DiaRule f (AccFormula (dsUnion ds ds2) r ur newPr) (PrFormula newPr ds f2)
      where newPr      = getNewPref br
            (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)

diaRule _ _ = error $ "diaRule"

-- diaX (may create a discard rule)
diaXRule :: PrFormula -> Branch -> Dependency -> Rule
diaXRule f@(PrFormula pr _ (DiaX _ r f2)) br d
  = if diaXAlreadyDone br pr (r,f2)
     then DiscardRule f
     else DiaXRule f d

diaXRule _ _ _ = error $ "diaXRule"

--

getNewPref :: Branch -> Prefix
getNewPref br = (lastPref br)+1

getNewProp :: Branch -> PropSymbol
getNewProp br = maybe (PropSymbol newPropBaseName) incPropSymbol (lastProp br)

getNewNom :: Branch -> NomSymbol
getNewNom br =  maybe (NomSymbol newNomBaseName) incNomSymbol (lastNom br)

-- E
existRule :: PrFormula -> Branch -> Rule
existRule f@(PrFormula _ ds (E f2)) br
  = ExistModRule f (PrFormula newPr ds f2)
     where newPr = getNewPref br
existRule _ _ = error $ "existRule"

-- D
diffRule :: PrFormula -> Rule
diffRule (PrFormula pr ds (D f2))
  = DiffRule (pr, ds, f2)

diffRule _ = error $ "diffRule"

-- disjunction
disjRule :: CmdLineParams -> PrFormula -> Branch -> Dependency -> Rule
disjRule clp df@(PrFormula pr ds (Dis fs)) br d
  = if not $ unitProp clp
     then DisjRule df (breakDisj df d)
     else case reduceDisjunctionAgainstBranch br pr fs of
             Triviality               -> DiscardRule df
             Contradiction ds_clash   -> ClashRule (dsUnion ds ds_clash) df
             Reduced new_ds disjuncts -> DisjRule df (prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"

-- semantic branching
semBrRule :: CmdLineParams -> PrFormula -> Branch -> Dependency -> Rule    -- todo : unit propagation, part 2 (b)
semBrRule clp df@(PrFormula pr ds (Dis fs)) br d
 = if not $ unitProp clp
    then SemBrRule df (sbModList $ breakDisj df d)
    else case reduceDisjunctionAgainstBranch br pr fs of
            Triviality               -> DiscardRule df
            Contradiction ds_clash   -> ClashRule (dsUnion ds ds_clash) df
            Reduced new_ds disjuncts -> SemBrRule df (sbModList $ prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
-- todo same remark as above
semBrRule _ _ _ _ = error "sembrRule"


sbModList ::  [PrFormula] -> [[PrFormula]]
sbModList fs = go fs []
 where go :: [PrFormula] -> [PrFormula] -> [[PrFormula]]
       go (hd:tl) negated = 
           (hd:negated):(go tl ((neg_ hd):negated))
           where neg_ (PrFormula pr ds f) = PrFormula pr ds (neg f)
       go [] _ = []



-- helper function for disjunction and semantic branching
-- updates the branching pointers of each formula
breakDisj :: PrFormula -> Dependency -> [PrFormula]
breakDisj (PrFormula pr ds (Dis fs)) d = prefix pr (dsInsert d ds) fs
breakDisj _ _ = error $ "breakDisj error"

-- @
atRule :: PrFormula -> Branch -> Rule
atRule af@(PrFormula _ ds (At (NomSymbol n) f)) br
 = AtRule af (PrFormula earliestPrefix (dsUnion ds ds2) f)
    where (earliestPrefix,ds2,_) = getUrfatherAndDeps br (DS.Nominal n)

atRule _ _ = error "atRule error"

-- down
downRule :: PrFormula -> Branch -> Rule
downRule df@(PrFormula pr ds (Down v f)) br
 = if downAlreadyDone br df
    then DiscardRule df
    else DownRule df (PrFormula pr ds (replaceVar v newNom f)) (PrFormula pr ds $ nom newNom)
    where newNom = getNewNom br
downRule _ _ = error "downRule error"

--if the input rule is a disjunction, returns the prefix of the rule
get_pr_disjunt_rule :: Rule -> Maybe Prefix
get_pr_disjunt_rule (DisjRule  (PrFormula pr _ _) _) = Just pr
get_pr_disjunt_rule (SemBrRule (PrFormula pr _ _) _) = Just pr
get_pr_disjunt_rule (DiaXRule  (PrFormula pr _ _) _) = Just pr
get_pr_disjunt_rule _                                = Nothing

ubRule :: Prefix -> Prefix -> Dependency -> Rule
ubRule p1 p2 d = UBlockRule p1 p2 [PrFormula p1 deps equalNom,  PrFormula p2 deps equalNom]
                                  [PrFormula p1 deps nequalNom, PrFormula p2 deps (neg nequalNom)]
 where equalNom  = nom $ NomSymbol $ "0n_eq_"  ++ show p1 ++ "_" ++ show p2
       nequalNom = nom $ NomSymbol $ "0n_neq_" ++ show p1 ++ "_" ++ show p2
       -- the nominals above start with a 0 so that no input nominal can have the same name
       deps = dsInsert d dsEmpty
