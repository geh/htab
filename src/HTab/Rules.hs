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
                     Dependency, DependencySet, dsUnion, dsInsert,
                     prefix, AccFormula(..), Rel,
                     Prefix,
                     replaceVar, Prop, Literal )
import HTab.Branch( Branch(..), createNewPref, createNewProp, createNewNomTestRelevance,
                    BranchInfo(..),
                    addFormulas, addAccFormula,
                    addDiaRuleCheck,
                    addDownRuleCheck, addDiffRuleCheck,
                    addParentPrefix,
                    reduceDisjunctionProposeLazy, doLazyBranching,
                    getUrfatherAndDeps, isNotBlocked, merge,
                    diaAlreadyDone, downAlreadyDone,
                    ReducedDisjunct(..), getUrfather,
                    TodoList(..))
import HTab.CommandLine(Params, UnitProp(..), lazyBranching, semBranch, unitProp, strategy, noLoopCheck)
import HTab.RuleId(RuleId(..))
import qualified HTab.DisjSet as DS

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix (Rel,Formula)
                           | BM_AddDownRuleCheck Prefix Formula
                           | BM_AddDiffRuleCheck Formula (Maybe Prop)
                           | BM_CreateNewPref
                           | BM_CreateNewProp
                           | BM_CreateNewNomTestRelevance Formula
                           | BM_AddParentPrefix Prefix Prefix
                           | BM_Clash DependencySet PrFormula
                           | BM_Merge Prefix DS.Pointer DependencySet
                           | BM_DoLazyBranch Prefix Literal [PrFormula]

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  DiaRule    PrFormula -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | LazyBranchRule PrFormula Prefix Literal [PrFormula]
           | AtRule     PrFormula
           | DownRule   PrFormula
           | DiffRule   PrFormula Dependency
           | ExistRule  PrFormula                 -- creates a prefix
           | DiscardDownRule PrFormula
           | DiscardDiaDoneRule PrFormula
           | DiscardDiaDone2Rule PrFormula
           | DiscardDiaBlockedRule PrFormula
           | DiscardDisjTrivialRule PrFormula
           | ClashDisjRule DependencySet PrFormula
           | MergeRule Prefix DS.Pointer DependencySet
           | RoleIncRule Prefix [Rel] Prefix DependencySet

-- from the description of a rule application, creates the list of lists of modifications to the branch
-- for certain rules, we need to look in the branch to see what modifications we do

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ClashDisjRule ds f) = [[BM_Clash ds f]]
getMods _ (MergeRule p n ds)= [[BM_Merge p n ds]]

getMods _ (RoleIncRule p1 rs p2 ds) = [[BM_AddAccFormula (AccFormula ds r p1 p2)] | r <- rs]

getMods br (DiaRule df@(PrFormula pr ds (Dia r f)))
 = if diaAlreadyDone br df
    then getMods br (DiscardDiaDone2Rule df)
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

getMods br (ExistRule (PrFormula _ ds (E f2))) =
 [[BM_AddFormulas [toadd],
   BM_CreateNewPref]]
 where toadd = PrFormula newPr ds f2
       newPr = getNewPref br

getMods _ (ExistRule _) = error "getMods ExistRule"

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
    then getMods br (DiscardDownRule df)
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

getMods _ (DiscardDownRule _) = [[]]
getMods _ (DiscardDiaDoneRule _) = [[]]
getMods _ (DiscardDiaDone2Rule _) = [[]]
getMods _ (DiscardDiaBlockedRule _) = [[]]
getMods _ (DiscardDisjTrivialRule _) = [[]]


instance Show Rule where
   show (MergeRule pr po _)               = "merge:              " ++ show (pr,po)
   show (DiaRule   todelete)              = "diamond:            " ++ showLess todelete
   show (DisjRule  todelete _ )           = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )           = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete )             = "at:                 " ++ showLess todelete
   show (DownRule  todelete )             = "down:               " ++ showLess todelete
   show (ExistRule todelete )             = "E:                  " ++ showLess todelete
   show (DiffRule  todelete _)            = "D:                  " ++ showLess todelete

   show (DiscardDownRule todelete)        = "Discard:            " ++ showLess todelete
   show (DiscardDiaDoneRule todelete)     = "Discard done:       " ++ showLess todelete
   show (DiscardDiaDone2Rule todelete)    = "Discard done 2:     " ++ showLess todelete
   show (DiscardDiaBlockedRule todelete)  = "Discard blocked:    " ++ showLess todelete
   show (DiscardDisjTrivialRule todelete) = "Discard trivial:    " ++ showLess todelete

   show (ClashDisjRule bprs f)     = "Clash:              " ++ show bprs ++ " " ++ show f
   show (RoleIncRule p1 rs p2 _)   = "Role inclusion      " ++ show (p1,rs,p2)
   show (LazyBranchRule todelete _ _ _)
                                   = "Lazy Branch "         ++ showLess todelete

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (MergeRule _ _ _)  -> R_Merge
              (DiaRule _ )       -> R_Dia
              (DisjRule _ _)     -> R_Disj
              (SemBrRule _ _)    -> R_SemBr
              (AtRule _ )        -> R_At
              (DownRule _)       -> R_Down
              (ExistRule _)      -> R_Exist
              (DiffRule _ _)     -> R_Diff
              (DiscardDownRule _)        -> R_DiscardDown
              (DiscardDiaDoneRule _)     -> R_DiscardDiaDone
              (DiscardDiaDone2Rule _)    -> R_DiscardDiaDone2
              (DiscardDiaBlockedRule _)  -> R_DiscardDiaBlocked
              (DiscardDisjTrivialRule _) -> R_DiscardDisjTrivial
              (ClashDisjRule _ _)      -> R_ClashDisj
              (RoleIncRule _ _ _ _)    -> R_RoleInc
              (LazyBranchRule _ _ _ _) -> R_LazyBranch

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRule :: Branch -> Params -> Dependency -> Maybe (Rule,TodoList,Branch)
applicableRule br p d = listToMaybe $ mapMaybe (ruleByChar br p d) (strategy p)

ruleByChar :: Branch -> Params -> Dependency -> Char -> Maybe (Rule,TodoList,Branch)
ruleByChar br p d char =
 case char of
  'n' -> applicableMergeRule
  '|' -> applicableDisjRule
  '<' -> applicableDiaRule
  '@' -> applicableAtRule
  'E' -> applicableExistRule
  'D' -> applicableDiffRule
  'b' -> applicableDownRule
  'r' -> applicableRoleIncRule
  _   -> error "ruleByChar"
 where
  todos  = todoList br

  applicableDiaRule
   = do (f@(PrFormula pr _ _),new) <- Set.minView $ diaTodo todos
        if noLoopCheck p
         then return (DiaRule f, todos{diaTodo = new},br)
         else if diaAlreadyDone br f
               then return (DiscardDiaDoneRule f, todos{diaTodo = new} , br )
               else if isNotBlocked br pr
                     then return ( DiaRule f,     todos{diaTodo = new}, br )
                     else let ur = getUrfather br (DS.Prefix pr)
                              brBlocked = br{blockedDias = IntMap.insertWith (++) ur [f] (blockedDias br)}
                              -- blocked formulas are added one by one to the blockedDias list.
                              -- a better way would be to put every formula of a given blocked prefix
                              -- to that list, but as we do not index todo formulas by prefix we can
                              -- not do it.
                          in
                          return ( DiscardDiaBlockedRule f, todos{diaTodo = new}, brBlocked)

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

  applicableMergeRule  = do ((ds,pr,po),new) <- Set.minView $ mergeTodo todos
                            return (MergeRule pr po ds, todos{mergeTodo = new},br)

  applicableDisjRule
   = case unitProp p of
      Eager -> {- scan all disjuncts until one can be discarded, reduced to one disjunct or clashes -}
                case mapMaybe (makeInteresting p br d) $ Set.toList $ disjTodo todos of
                  ((r,pf):_) -> return (r, todos{disjTodo = Set.delete pf $ disjTodo todos},br)
                  [] -> regularApplicableDisjRule --todo: update counter (CurCount, MaxCount) step 10 until which space out unit propagation
      _     ->  regularApplicableDisjRule

  regularApplicableDisjRule
   =  if semBranch p
       then do (f,new) <- Set.minView $ disjTodo todos
               return (semBrRule p f br d, todos{disjTodo = new},br)
       else do (f,new) <- Set.minView $ disjTodo todos
               return (disjRule p f br d,  todos{disjTodo = new},br)

makeInteresting :: Params -> Branch -> Dependency -> PrFormula ->  Maybe (Rule,PrFormula)
makeInteresting p br d df@(PrFormula pr ds (Dis fs))
 = case reduceDisjunctionProposeLazy br pr fs of
          Triviality               -> Just (DiscardDisjTrivialRule df,df)
          Contradiction ds_clash   -> Just (ClashDisjRule (dsUnion ds ds_clash) df,df)
          Reduced new_ds disjuncts mProposed
            | Set.size disjuncts == 1 -> Just (DisjRule df ( prefix ur newDeps disjuncts ), df)
            | lazyBranching p && ur <= unblockedPrefsLim br
                                  -> case mProposed of
                                    Nothing  -> Nothing
                                    Just lit -> Just (LazyBranchRule df ur lit [PrFormula ur newDeps (Dis disjuncts)], df)
            | otherwise  -> Nothing
              where newDeps = dsInsert d $ dsUnion ds new_ds
                    ur = getUrfather br (DS.Prefix pr)
            -- TODO should not insert d if the formula was actually not changed
               -- --> reduceDisjunctionProposeLazy should return a boolean
               -- -->  or have a constructor "Unchanged" ?

makeInteresting _ _ _ _ = error "makeInteresting on a non disjunction"

applyRule :: Params -> Rule -> Branch -> TodoList -> [BranchInfo]
applyRule p rule br_ todo
 = map (applyMods p br) (getMods br rule)
   where br = br_{todoList = todo}

applyMods :: Params -> Branch -> [BranchModification] -> BranchInfo
applyMods p br (hd:tl)
  = case (applyMod p br hd) of
      BranchOK br2             -> applyMods p br2 tl
      si@(BranchClash _ _ _ _) -> si
applyMods _ br [] = BranchOK br


applyMod :: Params -> Branch -> BranchModification -> BranchInfo
applyMod p br (BM_AddFormulas li)                = addFormulas p br li
applyMod p br (BM_AddAccFormula accFor)          = addAccFormula p br accFor
applyMod _ br (BM_AddDiaRuleCheck pr (r,f))      = BranchOK $ addDiaRuleCheck br pr (r,f)
applyMod _ br (BM_AddDownRuleCheck pr f)         = BranchOK $ addDownRuleCheck br pr f
applyMod p br (BM_CreateNewPref)                 = createNewPref p br
applyMod _ br (BM_CreateNewProp)                 = BranchOK $ createNewProp br
applyMod _ br (BM_CreateNewNomTestRelevance f)   = BranchOK $ createNewNomTestRelevance br f
applyMod _ br (BM_AddDiffRuleCheck f mp)         = BranchOK $ addDiffRuleCheck br f mp
applyMod _ br (BM_AddParentPrefix son father)    = BranchOK $ addParentPrefix br son father
applyMod _ br (BM_Clash ds (PrFormula pr ds2 f)) = BranchClash br pr (dsUnion ds ds2) f
applyMod p br (BM_Merge pr po ds)                = merge p br pr ds po
applyMod _ br (BM_DoLazyBranch pr l pfs)         = BranchOK $ doLazyBranching pr l pfs br
-- the actual rules and their helper functions

getNewPref :: Branch -> Prefix
getNewPref br = lastPref br + 1

-- disjunction
disjRule :: Params -> PrFormula -> Branch -> Dependency -> Rule
disjRule p df@(PrFormula pr ds (Dis fs)) br d
  = if unitProp p == UPNo
     then DisjRule df $ prefix pr (dsInsert d ds) fs
     else case reduceDisjunctionProposeLazy br pr fs of
             Triviality               -> DiscardDisjTrivialRule df
             Contradiction ds_clash   -> ClashDisjRule (dsUnion ds ds_clash) df
             Reduced new_ds disjuncts _
               -> DisjRule df (prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"

-- semantic branching
semBrRule :: Params -> PrFormula -> Branch -> Dependency -> Rule    -- todo : unit propagation, part 2 (b)
semBrRule p df@(PrFormula pr ds (Dis fs)) br d
 = if unitProp p == UPNo
    then SemBrRule df $ sbModList $ prefix pr (dsInsert d ds) fs
    else case reduceDisjunctionProposeLazy br pr fs of
            Triviality               -> DiscardDisjTrivialRule df
            Contradiction ds_clash   -> ClashDisjRule (dsUnion ds ds_clash) df
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

