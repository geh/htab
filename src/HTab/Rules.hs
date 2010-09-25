module HTab.Rules
(
Rule(..),BranchModification(..),
applicableRule, applyRule, ruleToId,
applyMod
) where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.Maybe ( listToMaybe, mapMaybe )

import HTab.Formula( Formula(..), PrFormula(..), showLess, neg,
                     Dependency, DependencySet, dsUnion, dsInsert, dsEmpty,
                     prefix, AccFormula(..), Rel,
                     Prefix,
                     conj, replaceVar, Prop, Literal )
import HTab.Branch( Branch(..), createNewPref, createNewProp, createNewNomTestRelevance,
                    BranchInfo(..),
                    addFormulas, addAccFormula,
                    addDiaRuleCheck, addDiaXRuleCheck,
                    addDownRuleCheck, addDiffRuleCheck,
                    addParentPrefix,
                    reduceDisjunctionProposeLazy, doLazyBranching,
                    getUnappliedUBPairs, updateUBBookKeep,
                    getUrfatherAndDeps, isNotBlocked, merge,
                    diaAlreadyDone,  diaXAlreadyDone, downAlreadyDone,
                    ReducedDisjunct(..), getUrfather,
                    ScheduledRule(..), TodoList(..),
                    deleteUEV, insertUEV_addFormula )
import HTab.CommandLine(CmdLineParams, UnitProp(..), lazyBranching, semBranch, unitProp, strategy, unrestrictedBlocking, noLoopCheck)
import HTab.RuleId(RuleId(..))
import qualified HTab.DisjSet as DS

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix (Rel,Formula)
                           | BM_AddDiaXRuleCheck Prefix (Rel,Formula)
                           | BM_AddDownRuleCheck Prefix Formula
                           | BM_AddDiffRuleCheck Formula (Maybe Prop)
                           | BM_CreateNewPref
                           | BM_CreateNewProp
                           | BM_CreateNewNomTestRelevance Formula
                           | BM_AddParentPrefix Prefix Prefix
                           | BM_Clash DependencySet PrFormula
                           | BM_UpdateUBBookKeep Prefix Prefix
                           | BM_DeleteUEV Int
                           | BM_InsertUEV_addFormula (Maybe Int) DependencySet (Int -> PrFormula)
                           | BM_Merge Prefix DS.Pointer DependencySet
                           | BM_DoLazyBranch Prefix Literal [PrFormula]

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  DiaRule    PrFormula -- creates a prefix
           | DiaXRule   PrFormula Dependency
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | LazyBranchRule PrFormula Prefix Literal [PrFormula]
           | AtRule     PrFormula
           | DownRule   PrFormula
           | DiffRule   PrFormula Dependency
           | ExistRule  PrFormula                 -- creates a prefix
           | DiscardRule PrFormula
           | ClashRule DependencySet PrFormula
           | UBlockRule Prefix Prefix Dependency
           | MergeRule Prefix DS.Pointer DependencySet
           | RoleIncRule Prefix [Rel] Prefix DependencySet

-- from the description of a rule application, creates the list of lists of modifications to the branch
-- for certain rules, we need to look in the branch to see what modifications we do

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ClashRule ds f) = [[BM_Clash ds f]]
getMods _ (MergeRule p n ds)= [[BM_Merge p n ds]]

getMods _ (RoleIncRule p1 rs p2 ds) = [[BM_AddAccFormula (AccFormula ds r p1 p2)] | r <- rs]

getMods br (DiaRule df@(PrFormula pr ds (Dia r f)))
 = if diaAlreadyDone br df
    then getMods br (DiscardRule df)
    else  [[BM_AddParentPrefix newPr ur,
            BM_AddAccFormula acctoadd,
            BM_AddFormulas [toadd],
            BM_AddDiaRuleCheck pr (r,f),
            BM_CreateNewPref]]
 where acctoadd   = AccFormula (dsUnion ds ds2) r ur newPr
       toadd      = PrFormula newPr ds f
       newPr      = getNewPref br
       (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)

getMods _ (DiaRule _) = error "getMods DiaRule"

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

getMods br (ExistRule (PrFormula _ ds (E f2))) =
 [[BM_AddFormulas [toadd],
   BM_CreateNewPref]]
 where toadd = PrFormula newPr ds f2
       newPr = getNewPref br

getMods _ (ExistRule _) = error "getMods ExistRule"


getMods br (UBlockRule p1 p2 d) =
 [[BM_UpdateUBBookKeep p1 p2,
   BM_Merge p1 (DS.Prefix p2) deps],
  [BM_CreateNewProp,
   BM_UpdateUBBookKeep p1 p2,
   BM_AddFormulas choiceDisequal]
 ]
   where
     choiceDisequal = [PrFormula p1 deps       (Lit newProp),
                       PrFormula p2 deps (neg (Lit newProp))]
     newProp = nextProp br
     deps = dsInsert d dsEmpty

getMods _ (DisjRule _ toadds) =
 [[BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule _ toaddss) =
 [[BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (LazyBranchRule _ pr lit pfs) =
 [[BM_DoLazyBranch pr lit pfs]]

getMods br (AtRule (PrFormula _ ds (At n f))) =
 [[BM_AddFormulas [toadd]]]
  where toadd = PrFormula earliestPrefix (dsUnion ds ds2) f
        (earliestPrefix,ds2,_) = getUrfatherAndDeps br (DS.Nominal n)

getMods _ (AtRule _) = error "getMods AtRules"


getMods br (DownRule df@(PrFormula pr ds f@(Down v f2)))
 = if downAlreadyDone br df
    then getMods br (DiscardRule df)
    else  [[BM_CreateNewNomTestRelevance f,  --  order  --  what about using a monadic
            BM_AddFormulas [toadd1, toadd2], -- matters -- writing for the getMods functions ?
            BM_AddDownRuleCheck pr f
          ]]
 where toadd1 = PrFormula pr ds (replaceVar v newNom f2)
       toadd2 = PrFormula pr ds $ Lit newNom
       newNom = nextNom br

getMods _ (DownRule _) = error "getMods DownRule"

getMods br (DiffRule (PrFormula pr ds_ (D f2)) d) =
 case Map.lookup f2 (dDiaRlCh br) of
  Nothing -> [[BM_AddDiffRuleCheck f2 Nothing,
               BM_CreateNewPref, BM_CreateNewPref,
               BM_CreateNewProp,
               BM_AddFormulas [PrFormula newPref1 ds f2,
                               PrFormula newPref2 ds f2,
                               PrFormula newPref1 ds (      Lit newProp),
                               PrFormula newPref2 ds (neg $ Lit newProp),
                               PrFormula pr       ds (neg $ Lit newProp)]
               ],
              [BM_AddDiffRuleCheck f2 (Just newProp),
               BM_CreateNewPref,
               BM_CreateNewProp,
               BM_AddFormulas [PrFormula newPref1 ds f2,
                               PrFormula newPref1 ds (      Lit newProp),
                               PrFormula pr       ds (neg $ Lit newProp)]
               ]
             ]
              where newPref1 = getNewPref br
                    newPref2 = newPref1 + 1
                    newProp  = nextProp br
  Just Nothing          -> [[]]
  Just (Just diffProp)  -> [[BM_AddFormulas [PrFormula pr ds (neg $ Lit diffProp)]]]
  where ds = d `dsInsert` ds_

getMods _ (DiffRule _ _) = error "getMods DiffRule"



getMods _ (DiscardRule _) = [[]]


instance Show Rule where
   show (MergeRule pr po _)        = "merge:              " ++ show (pr,po)
   show (DiaRule   todelete)       = "diamond:            " ++ showLess todelete
   show (DiaXRule  todelete _)     = "diamondX:           " ++ showLess todelete
   show (DisjRule  todelete _ )    = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )    = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete )      = "at:                 " ++ showLess todelete
   show (DownRule  todelete )      = "down:               " ++ showLess todelete
   show (ExistRule todelete )      = "E:                  " ++ showLess todelete
   show (DiffRule  todelete _)     = "D:                  " ++ showLess todelete
   show (DiscardRule todelete)     = "Discard:            " ++ showLess todelete
   show (ClashRule bprs f)         = "Clash:              " ++ show bprs ++ " " ++ show f
   show (UBlockRule p1 p2 _ )      = "Unrestricted blocking " ++ show (p1,p2)
   show (RoleIncRule p1 rs p2 _)   = "Role inclusion      " ++ show (p1,rs,p2)
   show (LazyBranchRule todelete _ _ _)
                                   = "Lazy Branch "         ++ showLess todelete

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (MergeRule _ _ _)  -> R_Merge
              (DiaRule _ )       -> R_Dia
              (DiaXRule _ _)     -> R_DiaX
              (DisjRule _ _)     -> R_Disj
              (SemBrRule _ _)    -> R_SemBr
              (AtRule _ )        -> R_At
              (DownRule _)       -> R_Down
              (ExistRule _)      -> R_Exist
              (DiffRule _ _)     -> R_Diff
              (DiscardRule _)    -> R_Discard
              (ClashRule _ _)    -> R_Clash
              (UBlockRule _ _ _) -> R_UBlocking
              (RoleIncRule _ _ _ _) -> R_RoleInc
              (LazyBranchRule _ _ _ _) -> R_LazyBranch

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRule :: Branch -> CmdLineParams -> Dependency -> Maybe (Rule,TodoList,Branch)
applicableRule br clp d =
 case todoList br of
  Fair [] -> Nothing
  Fair (sr:tl) -> Just (scheduledRuleToRule br clp d sr, Fair tl, br)
  _        ->  listToMaybe $ mapMaybe (ruleByChar br clp d) (strategy clp)

scheduledRuleToRule :: Branch -> CmdLineParams -> Dependency -> ScheduledRule -> Rule
scheduledRuleToRule _ _ d (SR_Inclusion p1 rs p2 ds) = RoleIncRule p1 rs p2 (dsInsert d ds)
scheduledRuleToRule _ _ d (SR_UBlocking p1 p2) = UBlockRule p1 p2 d
scheduledRuleToRule _ _ _ (SR_Merge pr po ds)  = MergeRule pr po ds
scheduledRuleToRule br clp d (SR_Formula pf@(PrFormula _ _ f2)) =
 case f2 of
  Dis _     -> if semBranch clp then semBrRule clp pf br d else disjRule clp pf br d
  Dia _ _   -> DiaRule pf
  DiaX _ _ _-> diaXRule pf br d
  At _ _    -> AtRule pf
  Down _ _  -> DownRule pf
  E _       -> ExistRule pf
  D _       -> DiffRule pf d
  _         -> error "scheduledRuleToRule, incorrect formula kind"

ruleByChar :: Branch -> CmdLineParams -> Dependency -> Char -> Maybe (Rule,TodoList,Branch)
ruleByChar br clp d char =
 case char of
  'n' -> applicableMergeRule
  '|' -> applicableDisjRule
  '<' -> applicableDiaRule
  '*' -> applicableDiaXRule
  '@' -> applicableAtRule
  'E' -> applicableExistRule
  'D' -> applicableDiffRule
  'b' -> applicableDownRule
  'u' -> if unrestrictedBlocking clp then applicableUBlockRule else Nothing
  'r' -> applicableRoleIncRule
  _   -> error "ruleByChar"
 where
  todos  = todoList br

  applicableDiaRule
   = do (f@(PrFormula pr _ _),new) <- Set.minView $ diaTodo todos
        if noLoopCheck clp
         then return (DiaRule f, todos{diaTodo = new},br)
         else if diaAlreadyDone br f
               then return (DiscardRule f, todos{diaTodo = new} , br )
               else if isNotBlocked br pr
                     then return ( DiaRule f,     todos{diaTodo = new}, br )
                     else let ur = getUrfather br (DS.Prefix pr)
                              brBlocked = br{blockedDias = IntMap.insertWith (++) ur [f] (blockedDias br)}
                              -- blocked formulas are added one by one to the blockedDias list.
                              -- a better way would be to put every formula of a given blocked prefix
                              -- to that list, but as we do not index todo formulas by prefix we can
                              -- not do it.
                          in
                          return ( DiscardRule f, todos{diaTodo = new}, brBlocked)

  applicableDiaXRule  = do (f,new) <- Set.minView $ diaXTodo todos
                           return (diaXRule f br d, todos{diaXTodo = new},br)

  applicableAtRule    = do (f,new) <- Set.minView $ atTodo todos
                           return (AtRule f, todos{atTodo = new},br)

  applicableDownRule  = do (f,new) <- Set.minView $ downTodo todos
                           return (DownRule f, todos{downTodo = new},br)

  applicableExistRule = do (f,new) <- Set.minView $ existTodo todos
                           return (ExistRule f, todos{existTodo = new},br)

  applicableDiffRule  = do (f,new) <- Set.minView $ diffTodo todos
                           return (DiffRule f d, todos{diffTodo = new},br)

  applicableRoleIncRule = do ((ds, p1, p2, rs),new) <- Set.minView $ roleIncTodo todos
                             return (RoleIncRule p1 rs p2 (dsInsert d ds), todos{roleIncTodo = new},br)

  applicableUBlockRule = case getUnappliedUBPairs br of
                            []          -> Nothing
                            ((p1,p2):_) -> Just (UBlockRule p1 p2 d, todos,br)

  applicableMergeRule  = do ((ds,p,po),new) <- Set.minView $ mergeTodo todos
                            return (MergeRule p po ds, todos{mergeTodo = new},br)

  applicableDisjRule
   = case unitProp clp of
      Eager -> {- scan all disjuncts until one can be discarded, reduced to one disjunct or clashes -}
                case mapMaybe (makeInteresting clp br d) $ Set.toList $ disjTodo todos of
                  ((r,pf):_) -> return (r, todos{disjTodo = Set.delete pf $ disjTodo todos},br)
                  [] -> regularApplicableDisjRule --todo: update counter (CurCount, MaxCount) step 10 until which space out unit propagation
      _     ->  regularApplicableDisjRule

  regularApplicableDisjRule
   =  if semBranch clp
       then do (f,new) <- Set.minView $ disjTodo todos
               return (semBrRule clp f br d, todos{disjTodo = new},br)
       else do (f,new) <- Set.minView $ disjTodo todos
               return (disjRule clp f br d,  todos{disjTodo = new},br)

makeInteresting :: CmdLineParams -> Branch -> Dependency -> PrFormula ->  Maybe (Rule,PrFormula)
makeInteresting clp br d df@(PrFormula pr ds (Dis fs))
 = case reduceDisjunctionProposeLazy br pr fs of
          Triviality               -> Just (DiscardRule df,df)
          Contradiction ds_clash   -> Just (ClashRule (dsUnion ds ds_clash) df,df)
          Reduced new_ds disjuncts mProposed
            | Set.size disjuncts == 1 -> Just (DisjRule df ( prefix pr newDeps disjuncts ), df)
            | lazyBranching clp -> case mProposed of
                                    Nothing  -> Nothing
                                    Just lit -> Just (LazyBranchRule df pr lit [PrFormula pr newDeps (Dis disjuncts)], df)
            | otherwise  -> Nothing
              where newDeps = dsInsert d $ dsUnion ds new_ds
            -- TODO should not insert d if the formula was actually not changed
               -- --> reduceDisjunctionProposeLazy should return a boolean
               -- -->  or have a constructor "Unchanged" ?

makeInteresting _ _ _ _ = error "makeInteresting on a non disjunction"

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
applyMod  _  br (BM_AddDiaRuleCheck pr (r,f))      = BranchOK $ addDiaRuleCheck br pr (r,f)
applyMod  _  br (BM_AddDiaXRuleCheck pr (r,f))     = BranchOK $ addDiaXRuleCheck br pr (r,f)
applyMod  _  br (BM_AddDownRuleCheck pr f)         = BranchOK $ addDownRuleCheck br pr f
applyMod clp br (BM_CreateNewPref)                 = createNewPref clp br
applyMod  _  br (BM_CreateNewProp)                 = BranchOK $ createNewProp br
applyMod  _  br (BM_CreateNewNomTestRelevance f)   = BranchOK $ createNewNomTestRelevance br f
applyMod  _  br (BM_AddDiffRuleCheck f mp)         = BranchOK $ addDiffRuleCheck br f mp
applyMod  _  br (BM_AddParentPrefix son father)    = BranchOK $ addParentPrefix br son father
applyMod  _  br (BM_Clash ds (PrFormula pr ds2 f)) = BranchClash br pr (dsUnion ds ds2) f
applyMod  _  br (BM_UpdateUBBookKeep p1 p2)        = BranchOK $ updateUBBookKeep p1 p2 br
applyMod  _  br (BM_DeleteUEV i)                   = BranchOK $ deleteUEV br i
applyMod clp br (BM_InsertUEV_addFormula mi ds ff) = insertUEV_addFormula br clp mi ds ff
applyMod clp br (BM_Merge pr p ds)                 = merge clp br pr ds p
applyMod  _  br (BM_DoLazyBranch pr l pfs)         = BranchOK $ doLazyBranching pr l pfs br
-- the actual rules and their helper functions

-- diaX (may create a discard rule)
diaXRule :: PrFormula -> Branch -> Dependency -> Rule
diaXRule f@(PrFormula pr _ (DiaX _ r f2)) br d
  = if diaXAlreadyDone br pr (r,f2)
     then DiscardRule f
     else DiaXRule f d

diaXRule _ _ _ = error "diaXRule"

--

getNewPref :: Branch -> Prefix
getNewPref br = lastPref br + 1

-- disjunction
disjRule :: CmdLineParams -> PrFormula -> Branch -> Dependency -> Rule
disjRule clp df@(PrFormula pr ds (Dis fs)) br d
  = if unitProp clp == UPNo
     then DisjRule df $ prefix pr (dsInsert d ds) fs
     else case reduceDisjunctionProposeLazy br pr fs of
             Triviality               -> DiscardRule df
             Contradiction ds_clash   -> ClashRule (dsUnion ds ds_clash) df
             Reduced new_ds disjuncts _
               -> DisjRule df (prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"

-- semantic branching
semBrRule :: CmdLineParams -> PrFormula -> Branch -> Dependency -> Rule    -- todo : unit propagation, part 2 (b)
semBrRule clp df@(PrFormula pr ds (Dis fs)) br d
 = if unitProp clp == UPNo
    then SemBrRule df $ sbModList $ prefix pr (dsInsert d ds) fs
    else case reduceDisjunctionProposeLazy br pr fs of
            Triviality               -> DiscardRule df
            Contradiction ds_clash   -> ClashRule (dsUnion ds ds_clash) df
            Reduced new_ds disjuncts _
              -> SemBrRule df (sbModList $ prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
-- todo same remark as above
semBrRule _ _ _ _ = error "sembrRule"


sbModList ::  [PrFormula] -> [[PrFormula]]
sbModList fs = go fs []
 where go :: [PrFormula] -> [PrFormula] -> [[PrFormula]]
       go (hd:tl) negated = 
           (hd:negated):(go tl ((neg_ hd):negated))
           where neg_ (PrFormula pr ds f) = PrFormula pr ds (neg f)
       go [] _ = []

