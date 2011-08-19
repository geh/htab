module HTab.Rules
(
Rule(..),
applicableRule, applyRule, ruleToId
) where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe ( mapMaybe )

import HTab.Formula( Formula(..), PrFormula(..), showLess, neg,
                     Dependency, DependencySet, dsUnion, dsInsert,
                     prefix, Rel,
                     Prefix,
                     replaceVar, Literal )
import HTab.Branch( Branch(..), createNewPref, createNewProp, createNewNomTestRelevance,
                    BranchInfo(..),
                    addFormulas, addAccFormula,
                    addDiaRuleCheck, addToBlockedDias,
                    addDownRuleCheck, addDiffRuleCheck,
                    addParentPrefix,
                    reduceDisjunctionProposeLazy, doLazyBranching,
                    getUrfatherAndDeps, isNotBlocked, merge,
                    diaAlreadyDone, downAlreadyDone,
                    ReducedDisjunct(..), getUrfather,
                    TodoList(..))
import HTab.CommandLine(Params, UnitProp(..), lazyBranching, semBranch, unitProp, strategy)
import HTab.RuleId(RuleId(..))
import qualified HTab.DisjSet as DS

-- rule constructors contain the data needed to modify a branch

data Rule =  DiaRule    PrFormula                 -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | LazyBranchRule PrFormula Prefix Literal [PrFormula]
           | AtRule     PrFormula
           | DownRule   PrFormula
           | DiffRule   PrFormula Dependency      -- creates a prefix
           | ExistRule  PrFormula                 -- creates a prefix
           | DiscardDownRule PrFormula
           | DiscardDiaDoneRule PrFormula
           | DiscardDiaDone2Rule PrFormula
           | DiscardDiaBlockedRule PrFormula
           | DiscardDisjTrivialRule PrFormula
           | ClashDisjRule DependencySet PrFormula
           | MergeRule Prefix DS.Pointer DependencySet
           | RoleIncRule Prefix [Rel] Prefix DependencySet


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
applicableRule :: Branch -> Params -> Dependency -> Maybe (Rule,Branch)
applicableRule br p d =
 case mapMaybe (ruleByChar br p d) (strategy p) of
      [] -> Nothing
      ((rule,newtodo,newbr):_) -> Just (rule,newbr{todoList = newtodo})

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
        if diaAlreadyDone br f
          then       return ( DiscardDiaDoneRule f,    todos{diaTodo = new}, br)
          else if isNotBlocked br pr
                then return ( DiaRule f,               todos{diaTodo = new}, br)
                else return ( DiscardDiaBlockedRule f, todos{diaTodo = new}, br)

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


(>>?) :: BranchInfo -> (Branch -> BranchInfo) -> BranchInfo
clash@(BranchClash _ _ _ _) >>? _ = clash
(BranchOK br) >>? f = f br

applyRule :: Params -> Rule -> Branch -> [BranchInfo]
applyRule p rule br
 = case rule of
    DiaRule df@(PrFormula pr ds (Dia r f))
     -> if diaAlreadyDone br df
         then
            applyRule p (DiscardDiaDone2Rule df) br
         else
          [ addParentPrefix newPr ur br >>?
            addAccFormula p (dsUnion ds ds2, r, ur, newPr) >>?
            addFormulas p [PrFormula newPr ds f] >>?
            addDiaRuleCheck pr (r,f) >>?
            createNewPref p ]
            where newPr      = getNewPref br
                  (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
    DiaRule  _ -> error "applyRule DiaRule with wrong formula kind"
    DisjRule _ prFormulas ->
            [ addFormulas p [toadd] br |  toadd <- prFormulas ]
    SemBrRule _ prFormulass ->
            [ addFormulas p toadds br |  toadds <- prFormulass ]
    LazyBranchRule _ pr lit prFormulas ->
            [ doLazyBranching pr lit prFormulas br ]
    AtRule  (PrFormula _ ds (At n f)) ->
            [ addFormulas p [toadd] br ]
            where (ur,ds2,_) = getUrfatherAndDeps br (DS.Nominal n)
                  toadd = PrFormula ur (dsUnion ds ds2) f
    AtRule _ -> error "error applyMods AtRule with wrong formula (should not happen!)"
    DownRule df@(PrFormula pr ds f@(Down v f2)) ->
          if downAlreadyDone br df
            then applyRule p (DiscardDownRule df) br
            else -- order matters
                 [ createNewNomTestRelevance f br >>?
                   addFormulas p [toadd1, toadd2] >>?
                   addDownRuleCheck pr f ]
                  where toadd1 = PrFormula pr ds (replaceVar v newNom f2)
                        toadd2 = PrFormula pr ds $ Lit newNom
                        newNom = nextNom br
    DownRule _ -> error "getMods DownRule"
    DiffRule   (PrFormula pr ds_ (D f2)) d ->
      case Map.lookup f2 (dDiaRlCh br) of
           Nothing -> [ addDiffRuleCheck f2 Nothing br >>?
                        createNewPref p >>?
                        createNewPref p >>?
                        createNewProp >>?
                        addFormulas p [ PrFormula newPref1 ds f2,
                                        PrFormula newPref2 ds f2,
                                        PrFormula newPref1 ds (      Lit newProp),
                                        PrFormula newPref2 ds (neg $ Lit newProp),
                                        PrFormula pr       ds (neg $ Lit newProp) ]
                        ,
                        addDiffRuleCheck f2 (Just newProp) br >>?
                        createNewPref p >>?
                        createNewProp >>?
                        addFormulas p [ PrFormula newPref1 ds f2,
                                        PrFormula newPref1 ds (      Lit newProp),
                                        PrFormula pr       ds (neg $ Lit newProp) ]
                      ]
                       where newPref1 = getNewPref br
                             newPref2 = newPref1 + 1
                             newProp  = nextProp br
           Just (Just diffProp)  -> [addFormulas p [PrFormula pr ds (neg $ Lit diffProp)] br]
           Just Nothing          -> [BranchOK br]
           where ds = d `dsInsert` ds_
    DiffRule _ _ -> error "getMods DiffRule"
    ExistRule (PrFormula _ ds (E f2)) ->
       [addFormulas p [toadd] br >>? createNewPref p]   -- this createNewPref  / getNewPref thing needs to stop
       where toadd = PrFormula newPr ds f2
             newPr = getNewPref br
    ExistRule _ -> error "getMods ExistRule"
    DiscardDownRule _         -> [BranchOK br]
    DiscardDiaDoneRule _      -> [BranchOK br]
    DiscardDiaDone2Rule _     -> [BranchOK br]
    DiscardDisjTrivialRule _  -> [BranchOK br]
    DiscardDiaBlockedRule f   -> [addToBlockedDias f br]

    ClashDisjRule ds (PrFormula pr ds2 f) -> [BranchClash br pr (dsUnion ds ds2) f]
    MergeRule pr po ds -> [merge p pr ds po br]
    RoleIncRule p1 rs p2 ds ->
     [addAccFormula p (ds, r, p1, p2) br | r <- rs]


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

