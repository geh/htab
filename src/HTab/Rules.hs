module HTab.Rules
(
Rule(..),
applicableRule, applyRule, ruleToId
) where

import qualified Data.Set as Set
import Data.Maybe ( mapMaybe )

import HTab.Formula( Formula(..), PrFormula(..), showLess,
                     Dependency, DependencySet, dsUnion, dsInsert,
                     prefix, Rel, negPr,
                     Prefix, Nom, Atom(..),
                     replaceVar, Literal(..))
import HTab.Branch( Branch(..), BranchInfo(..), TodoList(..),
                    -- for rules
                    createNewNode, createNewNom,
                    addFormulas, addAccFormula,
                    addDiaRuleCheck, addToBlockedDias,
                    addDownRuleCheck,
                    doLazyBranching,
                    getUrfatherAndDeps, merge,
                    -- for choosing rule in todo list
                    patternBlocked,
                    diaAlreadyDone, downAlreadyDone,
                    -- for rules and choosing rule in todo list
                    reduceDisjunctionProposeLazy, getUrfather,
                    ReducedDisjunct(..)
                    )
import HTab.CommandLine(Params, UnitProp(..),
                        lazyBranching, semBranch, unitProp,
                        strategy)
import HTab.RuleId(RuleId(..))
import qualified HTab.DisjSet as DS

-- rule constructors contain the data needed to modify a branch

data Rule =  DiaRule    PrFormula                 -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [PrFormula]
           | LazyBrRule PrFormula Prefix Literal [PrFormula]
           | AtRule     PrFormula
           | DownRule   PrFormula
           | ExistRule  PrFormula                 -- creates a prefix
           | DiscardDownRule PrFormula
           | DiscardDiaDoneRule PrFormula
           | DiscardDiaBlockedRule PrFormula
           | DiscardDisjTrivialRule PrFormula
           | ClashDisjRule DependencySet PrFormula
           | MergeRule Prefix Nom DependencySet
           | RoleIncRule Prefix [Rel] Prefix DependencySet


instance Show Rule where
   show (MergeRule pr n _)                = "merge:              " ++ show (pr, show n)
   show (DiaRule   todelete)              = "diamond:            " ++ showLess todelete
   show (DisjRule  todelete _ )           = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )           = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete )             = "at:                 " ++ showLess todelete
   show (DownRule  todelete )             = "down:               " ++ showLess todelete
   show (ExistRule todelete )             = "E:                  " ++ showLess todelete

   show (DiscardDownRule todelete)        = "Discard:            " ++ showLess todelete
   show (DiscardDiaDoneRule todelete)     = "Discard done:       " ++ showLess todelete
   show (DiscardDiaBlockedRule todelete)  = "Discard blocked:    " ++ showLess todelete
   show (DiscardDisjTrivialRule todelete) = "Discard trivial:    " ++ showLess todelete

   show (ClashDisjRule bprs f)     = "Clash:              " ++ show bprs ++ " " ++ show f
   show (RoleIncRule p1 rs p2 _)   = "Role inclusion      " ++ show (p1,rs,p2)
   show (LazyBrRule todelete _ _ _)= "Lazy Branch "         ++ showLess todelete

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
              (DiscardDownRule _)        -> R_DiscardDown
              (DiscardDiaDoneRule _)     -> R_DiscardDiaDone
              (DiscardDiaBlockedRule _)  -> R_DiscardDiaBlocked
              (DiscardDisjTrivialRule _) -> R_DiscardDisjTrivial
              (ClashDisjRule _ _)      -> R_ClashDisj
              (RoleIncRule _ _ _ _)    -> R_RoleInc
              (LazyBrRule _ _ _ _)     -> R_LazyBranch

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRule :: Branch -> Params -> Dependency -> Maybe (Rule,Branch)
applicableRule br p d =
 case mapMaybe (ruleByChar br p d) (strategy p) of
   [] -> Nothing
   ((rule,newtodo):_) -> Just (rule,br{todoList = newtodo})

ruleByChar :: Branch -> Params -> Dependency -> Char -> Maybe (Rule,TodoList)
ruleByChar br p d char =
 case char of
  'n' -> applicableMergeRule
  '|' -> applicableDisjRule
  '<' -> applicableDiaRule
  '@' -> applicableAtRule
  'E' -> applicableExistRule
  'b' -> applicableDownRule
  'r' -> applicableRoleIncRule
  _   -> error "ruleByChar"
 where
  todos  = todoList br

  applicableDiaRule
   = do (f,new) <- Set.minView $ diaTodo todos
        if diaAlreadyDone br f
          then       return ( DiscardDiaDoneRule f,    todos{diaTodo = new})
          else
           if patternBlocked br f
             then return ( DiscardDiaBlockedRule f, todos{diaTodo = new})
             else return ( DiaRule f,               todos{diaTodo = new})
  applicableAtRule    = do (f,new) <- Set.minView $ atTodo todos
                           return (AtRule f, todos{atTodo = new})
  applicableDownRule  = do (f,new) <- Set.minView $ downTodo todos
                           if downAlreadyDone br f
                            then return (DiscardDownRule f, todos{downTodo = new})
                            else return (DownRule f, todos{downTodo = new})
  applicableExistRule = do (f,new) <- Set.minView $ existTodo todos
                           return (ExistRule f, todos{existTodo = new})
  applicableRoleIncRule
   = do ((ds, p1, p2, rs),new) <- Set.minView $ roleIncTodo todos
        return (RoleIncRule p1 rs p2 (dsInsert d ds), todos{roleIncTodo = new})
  applicableMergeRule  = do ((ds,pr,n),new) <- Set.minView $ mergeTodo todos
                            return (MergeRule pr n ds, todos{mergeTodo = new})
  applicableDisjRule
   = case unitProp p of
      Eager -> {- scan all disjuncts until one can be discarded,
                  reduced to one disjunct or clashes -}
          case mapMaybe (makeInteresting p br d) $ Set.toList $ disjTodo todos of
            ((r,pf):_) -> return (r, todos{disjTodo = Set.delete pf $ disjTodo todos})
            [] -> regularApplicableDisjRule
         -- todo: update counter (CurCount, MaxCount) step 10
         -- to space out unit propagation lookup
      _     ->  regularApplicableDisjRule
  regularApplicableDisjRule
   = do (f,new) <- Set.minView $ disjTodo todos
        return (disjRule p f br d, todos{disjTodo = new})

makeInteresting :: Params -> Branch -> Dependency -> PrFormula ->  Maybe (Rule,PrFormula)
makeInteresting p br d df@(PrFormula pr ds (Dis fs))
 = case reduceDisjunctionProposeLazy br pr fs of
          Triviality               -> Just (DiscardDisjTrivialRule df,df)
          Contradiction ds_clash   -> Just (ClashDisjRule (dsUnion ds ds_clash) df,df)
          Reduced new_ds disjuncts mProposed
           | Set.size disjuncts == 1
              -> Just (DisjRule df ( prefix ur newDeps disjuncts ), df)
           | lazyBranching p
              -> case mProposed of
                  Nothing  -> Nothing
                  Just lit
                   -> Just (LazyBrRule df ur lit [PrFormula ur newDeps (Dis disjuncts)],
                            df)
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
    DiaRule (PrFormula pr ds md (Dia r f))
     -> [ addAccFormula p (dsUnion ds ds2, r, ur, newPr) br >>?
          addFormulas p [PrFormula newPr ds (md+1) f] >>?
          addDiaRuleCheck pr (r,f) newPr >>?
          createNewNode p ]
          where newPr      = lastPref br + 1
                (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
    DisjRule _ prFormulas ->
            [ addFormulas p [toadd] br |  toadd <- prFormulas ]
    SemBrRule _ prFormulas ->
            [ addFormulas p toadds br |  toadds <- go prFormulas [] ]
             where
              go (hd:tl) negs = (hd:negs):(go tl (negPr hd:negs))
              go [] _ = []
    LazyBrRule _ pr lit prFormulas ->
            [ doLazyBranching pr lit prFormulas br ]
    AtRule  (PrFormula _ ds (At n f)) ->
            [ addFormulas p [toadd] br{ nomPrefClasses = equiv }]
            where (ur,ds2,equiv) = getUrfatherAndDeps br (DS.Nominal n)
                  toadd = PrFormula ur (dsUnion ds ds2) f
    DownRule (PrFormula pr ds f@(Down v f2)) ->
                 [ createNewNom br >>?
                   addFormulas p [toadd1, toadd2] >>?
                   addDownRuleCheck pr f ]
                  where toadd1 = PrFormula pr ds (replaceVar v newNom f2)
                        toadd2 = PrFormula pr ds $ Lit $ PosLit $ N newNom
                        newNom = '_':(show $ nextNom br)
    ExistRule (PrFormula _ ds md (E f2)) ->
       [addFormulas p [toadd] br >>? createNewNode p]
       where toadd = PrFormula newPr ds (md+1) f2
             newPr = lastPref br + 1
    DiscardDownRule _         -> [BranchOK br]
    DiscardDiaDoneRule _      -> [BranchOK br]
    DiscardDisjTrivialRule _  -> [BranchOK br]
    DiscardDiaBlockedRule f   -> [addToBlockedDias f br]

    ClashDisjRule ds (PrFormula pr ds2 f) -> [BranchClash br pr (dsUnion ds ds2) f]
    MergeRule pr n ds -> [merge p pr ds n br]
    RoleIncRule p1 rs p2 ds ->
     [addAccFormula p (ds, r, p1, p2) br | r <- rs]
    _ -> error $ "applyRule with bad argument: " ++ show rule

disjRule :: Params -> PrFormula -> Branch -> Dependency -> Rule
disjRule p df@(PrFormula pr ds (Dis fs)) br d
  = if unitProp p == UPNo
     then rule df $ prefix pr (dsInsert d ds) fs
     else case reduceDisjunctionProposeLazy br pr fs of
             Triviality               -> DiscardDisjTrivialRule df
             Contradiction ds_clash   -> ClashDisjRule (dsUnion ds ds_clash) df
             Reduced new_ds disjuncts _
               -> rule df (prefix pr (dsInsert d $ dsUnion ds new_ds) disjuncts)
    where rule = if semBranch p then SemBrRule else DisjRule
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"
