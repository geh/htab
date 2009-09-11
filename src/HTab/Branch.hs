{-# OPTIONS_GHC -fglasgow-exts #-}

----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module HTab.Branch
(
Branch(..), BranchMonad, createNewProp, createNewPref, createNewNomTestRelevance, BranchInfo(..),
addFormulas, addFormula, addAccFormula, remFormula,
addDiaRuleCheck, addDiaXRuleCheck, addDownRuleCheck, addDiffRuleCheck,
addParentPrefix, addFirstFormulas,
updateUBBookKeep, ScheduledRule(..), TodoList(..), processTodoList,
BranchData(..),branch_depth, getBranch,
emptyBranch,initialBranchStateFor,
addZeroInPath,incPathHead,prefixes,
reduceDisjunctionAgainstBranch,
getUrfather, getUrfatherAndDeps, isInTheModel, relationIsInTheModel,
getModelRepresentative, isNotBlocked,
calculateStepInfo, BlockingMode(..), diaAlreadyDone, diaXAlreadyDone,
downAlreadyDone, incPropSymbol, incNomSymbol,
UCache(..),Univ_constraints,AugmentedPrefixes,UCMap,BranchTrueForms,gen_unsat_cache,setPrevPref,
collectUevBprs, ReducedDisjunct(..), newNomBaseName, newPropBaseName, getUnappliedUBPairs,
isReflexive, isSymmetric, isTransitive,
del_pref_disjunctPrefixes, del_level_disjunctPrefixes, search_disjunctPrefixes,DisjunctPrefixes
) where

--import Debug.Trace

import Control.Monad.State(StateT, MonadState)
import Data.List(delete, minimumBy)
import Data.Char ( isNumber )

import HTab.UCMatrix ( UCMatrix )
import qualified HTab.UCMatrix as UCMatrix
import HTab.UCList

import Data.Map ( Map, foldWithKey )
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified HTab.DisjSet as DS

import Data.Maybe( fromJust, fromMaybe, catMaybes)

import HTab.Timeout( TimeoutSignal )
import HTab.Statistics(Statistics)
import HTab.CommandLine(CmdLineParams(..), Caching(..))

import HTab.Formula

import HTab.DMap ( DMap(..), toMap )
import qualified HTab.DMap as DMap
import HTab.Base(moveInMap, almostCartesianProduct, doMemoize, set, list)

import HTab.Relations ( Relations, emptyRels, insertRelation, mergePrefixWith,
                        getSuccessors, getPredecessors, getIncomingLinks, getOutgoingLinks,
                        showPretty )

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

getBranch :: BranchInfo -> Branch
getBranch (BranchOK br)          = br
getBranch (BranchClash br _ _ _) = br

type Clashable_info   = DMap Prefix Atom (Bool,DependencySet)
type Conj_structure   = Set.Set PrFormula
type Disj_structure   = Set.Set PrFormula
type Dia_structure    = Set.Set PrFormula
type DiaX_structure   = Set.Set PrFormula
type At_structure     = Set.Set PrFormula
type Down_structure   = Set.Set PrFormula
type Exist_structure  = Set.Set PrFormula
type Diff_structure   = Set.Set PrFormula
type Box_constraints  = DMap Prefix Rel [(DependencySet,Formula)]

type Dia_rule_chart    = Map.Map Prefix (Set.Set Formula)
type DiaX_rule_chart   = Map.Map Prefix (Set.Set Formula)
type BoxX_rule_chart   = Map.Map Prefix (Set.Set Formula)
type Down_rule_chart   = Map.Map Prefix (Set.Set Formula)
type At_rule_chart     = Set.Set Formula
type Exist_rule_chart  = Set.Set Formula
type Diff_Dia_rule_chart  = Map.Map Formula (PropSymbol,Bool)
       -- maps D(phi) formulas to the prop symbol used to differentiate
       -- the current prefix from the one used to contain (phi) , and to a boolean indicating if a second
       -- different world has already been created
type DownVarRelevant_chart = Map.Map Formula Bool

type Diff_Box_constraints = [(DependencySet,Formula,NomSymbol)]

type Univ_constraints  = [(DependencySet,Formula)]

type PrefToFormulas   = Map.Map Prefix (Set.Set Formula)
type PrefToDepSet     = Map.Map Prefix DependencySet
type PrefToUev        = DMap Prefix (Formula,Rel) DependencySet

type EquivClasses = DS.DisjSet DS.Pointer
type InclusionUrfathersMap = Map.Map Prefix Prefix

type AugmentedPrefixes = [Prefix] -- list of prefixes whose label is modified during the current step of the algorithm

type PrevPrefixes = [Prefix] --To keep the prefixes true at b-b1, where b is the current branch, and b1 is prev(b)


type PrefixParent = Map.Map Prefix Prefix

data BlockingMode = InclusionBlockingGlobal | InclusionBlockingChain | ChainBlocking
 deriving (Eq,Show)


type BranchTrueForms = DMap Prefix Formula DependencySet 
type UCMap = Bimap.Bimap UCFormula Int 
--The unsat cache, includes two data structure to allow us to choose any of them.
--once chosen a data structure, the other is kept emptied
type DisjunctPrefixes = [(Int,Prefix)]

data UCache = UCache { matrix :: UCMatrix, --the bit matrix 
                       listsList :: UCList, --list apporach
                       current_index :: Int,  
                       descrip_matrix :: UCMap,
                       current_row :: Int,
                       max_row :: Int}
              deriving (Show)


data Branch = Branch {clashStr :: Clashable_info,
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- immediate rules constraints
                  boxConstrFwd :: Box_constraints,
                  boxConstrBwd :: Box_constraints,
                      univCons :: Univ_constraints,
                      dBoxCons :: Diff_Box_constraints, -- constraints of the (B) modality
                 -- saturation of rules
                       diaRlCh :: Dia_rule_chart,       -- saturation of the diamond rule
                      diaXRlCh :: DiaX_rule_chart,      -- saturation of the diamondX rule
                      boxXRlCh :: BoxX_rule_chart,      -- saturation of the boxX rule
                      downRlCh :: Down_rule_chart,      -- saturatino of the down-arrow rule
                        atRlCh :: At_rule_chart,        -- saturation of the @ rule
                     existRlCh :: Exist_rule_chart,     -- saturation of the exist rule
                      dDiaRlCh :: Diff_Dia_rule_chart,  -- saturation of the diff diamond rule chart (D)
                 -- formulas true in an equivalence class
                   prefToForms :: PrefToFormulas,
             --all formulas true in the branch, by prefixes
               branchTrueForms :: BranchTrueForms,
        --To keep the prefixes true at b-b1, where b is the current branch, and b1 is prev(b)
                   prevPref :: PrevPrefixes, 
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: PrefToDepSet,
                 -- other data
                        accStr :: Relations,
                 -- equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       lastNom :: Maybe NomSymbol,
                      lastProp :: Maybe PropSymbol,
                       incrPrs :: AugmentedPrefixes,
                  prefToUevFwd :: PrefToUev,
                  prefToUevBwd :: PrefToUev,
                    bookKeepUB :: (Prefix,Prefix),
                 -- caching / memoisation data
             downVarRelevantCh :: DownVarRelevant_chart,
                 -- information about language of input formula and blocking mode
                 inputLanguage :: LanguageInfo,
                     inclUrMap :: Maybe InclusionUrfathersMap,
                     blockMode :: BlockingMode,
                    prefParent :: PrefixParent,
              relevantNominals :: Set.Set NomSymbol,
                       relInfo :: RelInfo}

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--

emptyBranch :: CmdLineParams -> LanguageInfo -> RelInfo -> Branch
emptyBranch clp fLang relInfo_ =
 addReflexiveLinks 0 $
                Branch
                { clashStr = DMap.empty::Clashable_info,
                  todoList = emptyTodoList clp,
                  accStr   =emptyRels,
                  boxConstrBwd=DMap.empty::Box_constraints,
                  boxConstrFwd=DMap.empty::Box_constraints,
                  diaRlCh=Map.empty::Dia_rule_chart,
                  diaXRlCh=Map.empty::DiaX_rule_chart,
                  boxXRlCh=Map.empty::BoxX_rule_chart,
                  downRlCh=Map.empty::Down_rule_chart,
                  atRlCh=Set.empty::At_rule_chart,
                  existRlCh=Set.empty::Exist_rule_chart,
                  dDiaRlCh = Map.empty::Diff_Dia_rule_chart,
                  downVarRelevantCh = Map.empty::DownVarRelevant_chart,
                  dBoxCons = [],
                  univCons=[],
                  lastPref = 0,
                  lastNom  = Nothing,
                  lastProp = Nothing,
                  prefToForms= Map.empty::PrefToFormulas,
                  branchTrueForms=DMap.empty :: BranchTrueForms, 
                  prToDepSet= Map.empty::PrefToDepSet,
                  prefToUevFwd= DMap.empty::PrefToUev,
                  prefToUevBwd= DMap.empty::PrefToUev,
                  bookKeepUB=(0,0),
                  nomPrefClasses= DS.mkDSet::EquivClasses,
                  inputLanguage = fLang,
                  inclUrMap = Nothing,
                  incrPrs = [],
                  prevPref =[], 
                  blockMode = blockingMode,
                  prefParent = Map.empty::PrefixParent,
                  relevantNominals = set $ languageNoms fLang,
                  relInfo = relInfo_
                }
 where blockingMode = if inclBlockChain clp && (not $ inclBlockGlobal clp)
                       then InclusionBlockingChain
                       else InclusionBlockingGlobal

instance Show Branch where
    show br = "Input language: " ++ show (inputLanguage br) ++
              "\nClashable formulas:\n" ++ prettyShowMap_ (DMap.toMap $ clashStr br) (\v -> "(" ++ prettyShowMap_clashable v ++ ")") "\n " ++
              "\nTodo list(s): "   ++ show (todoList br)  ++
              "\nAccessibility: "        ++ showPretty (accStr br) ++
              "\nBox constraints fwd: " ++ prettyShowMap_ (DMap.toMap $ boxConstrFwd br) (\v -> "(" ++ prettyShowMap_rel_ds_x v ++ ")") "\n " ++
              "\nBox constraints bwd: " ++ prettyShowMap_ (DMap.toMap $ boxConstrBwd br) (\v -> "(" ++ prettyShowMap_rel_ds_x v ++ ")") "\n " ++
              "\nDia rule chart: "  ++ prettyShowMap_ (diaRlCh br) (show . list) "\n " ++
              "\nDown rule chart: " ++ prettyShowMap_ (downRlCh br) (show . list) "\n " ++
              "\n@ rule chart: "   ++ show (list $ atRlCh br) ++
              "\nExist rule chart:" ++ show (list $ existRlCh br) ++
              "\nDiff dia rule chart: "  ++ prettyShowMap_ (dDiaRlCh br) show "\n " ++
              "\nDown var relevant chart: " ++ prettyShowMap_ (downVarRelevantCh br) show ", " ++
              "\nUnrestricted blocking book-keep:" ++ show (bookKeepUB br) ++ ", " ++
              "\nUniv constraints: "++ show (univCons br) ++
              "\nDiff box constraints: "++ show (dBoxCons br) ++
              "\nPrefix to dependency set:\n " ++ prettyShowMap_ (prToDepSet br) dsShow "\n " ++
              "\nPrefix to formulas:\n" ++ prettyShowMap_ (prefToForms br) (show . Set.toList) "\n " ++
              "\nPrefix to unfulfilled <*>: " ++ show (DMap.flattenDMap $ prefToUevFwd br) ++
              "\nPrefix to unfulfilled <-*>: " ++ show (DMap.flattenDMap $ prefToUevBwd br) ++
              "\nTrue formulas: " ++ "\n " ++ prettyShowMap_ (branchTrueForms br) (show . Set.toList) "\n " ++
              "\nParent: " ++ prettyShowMap (prefParent br) ", " ++
              "\nInclusion urfather map: "  ++ show (inclUrMap br) ++
              "\nIncreased prefixes: " ++ show (incrPrs br) ++
              "\nPrefixes in (current branch - prev(current branch): " ++ show (notPrevPref br) ++ 
              "\nBlocking mode: " ++ show (blockMode br) ++
              "\nPrefix-Nominal classes : " ++ prettyShowMap (nomPrefClasses br) ", " ++
              "\nModel-relevant nominals : " ++ show (relevantNominals br)

instance Emptyable (Map a b) where
 empty = Map.null

instance Emptyable (DMap a b c) where
 empty (DMap m) = Map.null m

instance Emptyable Relations where
 empty = Relations.null

instance Emptyable (Set a) where
 empty = Set.null


{-
   "add formula(s)" functions, that handle all that is related
   to prefixes, nominals, and vId/nom rules
-}

type MergeHistory = [(Prefix,String)]

addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> MergeHistory -> BranchInfo
addFormulas clp br (hd:tl) history
       = case addFormula clp br hd history of
          BranchOK br2             -> addFormulas clp br2 tl history
          bi@(BranchClash _ _ _ _) -> bi

addFormulas _ br [] _ = BranchOK br


-- 3 main cases : adding a positive nominal, adding a disjunction, and otherwise.
addFormula :: CmdLineParams -> Branch -> PrFormula -> MergeHistory -> BranchInfo
addFormula clp br f@(PrFormula pr fDs f2@(Lit (PosLit (N (NomSymbol n))))) history
 | (pr,n) `elem` history = addFormulaBaseCase clp br f
 | otherwise
   = let
         (DS.Prefix ur1,classes1) = DS.find  (DS.Prefix pr) (nomPrefClasses br)
         (nomAncestor  ,classes2) = DS.find  (DS.Nominal n) classes1
         classes3                 = DS.union (DS.Prefix pr) (DS.Nominal n) classes2
     in
      case nomAncestor of
       DS.Nominal _  ->     -- nominal not yet in the equivalence classes
            let
                newBr = addClassDeps ur1 fDs $ br { nomPrefClasses = classes3 }
            in
                addFormula clp newBr ( PrFormula ur1 fDs f2 ) ((ur1,n):history)
       DS.Prefix ur2
         | ur1 == ur2       -- same class
            -> addFormula clp (addClassDeps ur1 fDs br) ( PrFormula ur1 fDs f2 ) ((ur1,n):history)
         | otherwise        -- two different classes
            ->
              let
                 oldUr                    = max ur1 ur2
                 newUr                    = min ur1 ur2
                 clashableInfoSlots       = catMaybes $ map (\ur -> DMap.lookup1 ur (clashStr br))  [ur1,ur2]
                 currentDependencies      = dsUnions $ fDs:(map (findDeps br) [ur1,ur2])
                 newPrToDepSet            = Map.insert newUr currentDependencies (prToDepSet br)
                 newClashableSlotUrfather = addDepsToClashableSlot currentDependencies $ clashableInfoSlotsUnions clashableInfoSlots
              in
                 case newClashableSlotUrfather of
                  Slot_UpdateFailure clashingDeps ->
                      let newBr = br{nomPrefClasses = classes3} in
                      BranchClash newBr pr (dsUnion clashingDeps currentDependencies) f2

                  Slot_UpdateSuccess urfatherSlot ->
                      let newClashStr    = DMap $ Map.delete oldUr $ Map.insert newUr urfatherSlot (toMap $ clashStr br)
                          newPrefToForms = moveInMap (prefToForms br) oldUr newUr Set.union
                          newbranchTrueForms = DMap.moveInnerDataDMap (branchTrueForms br) oldUr newUr dsUnion
                          newBoxConstrFwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrFwd br) oldUr newUr
                          newBoxConstrBwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrBwd br) oldUr newUr
                          newAccStr       = mergePrefixWith (accStr br) oldUr newUr fDs


                          newDiaRlCh     = moveInMap (diaRlCh br)  oldUr newUr Set.union
                          newDiaXRlCh    = moveInMap (diaXRlCh br) oldUr newUr Set.union
                          newBoxXRlCh    = moveInMap (boxXRlCh br) oldUr newUr Set.union

                          mapBoxFwd = map (\idx -> Map.findWithDefault Map.empty idx (toMap $ boxConstrFwd br) ) [ur1,ur2]
                          mapBoxBwd = map (\idx -> Map.findWithDefault Map.empty idx (toMap $ boxConstrBwd br) ) [ur1,ur2]
                          mapAccFwd = map (Map.fromList . (getOutgoingLinks (accStr br))) [ur1,ur2]
                          mapAccBwd = map (Map.fromList . (getIncomingLinks (accStr br))) [ur1,ur2]
                          formulasToSend1 = concatMap (newFormulasToSend fDs) $ almostCartesianProduct mapBoxFwd mapAccFwd
                          formulasToSend2 = concatMap (newFormulasToSend fDs) $ almostCartesianProduct mapBoxBwd mapAccBwd

                          functionalityNominalToSend = addFNom $ filter ((isFunctional (relInfo br)) . fst) $ getOutgoingLinks (accStr br) oldUr
                               where addFNom :: [(Rel, [(Prefix,DependencySet)])] -> [PrFormula]
                                     addFNom = concatMap (\(r,pds) ->
                                                            map (\(p,ds) -> PrFormula p (dsUnion ds fDs) (funcNominal r newUr)) pds
                                                         )
                          injectivityNominalsToSend  = addINom $ filter ((isInjective  (relInfo br)) . fst) $ getIncomingLinks (accStr br) oldUr
                               where addINom :: [(Rel, [(Prefix,DependencySet)])] -> [PrFormula]
                                     addINom = concatMap (\(r,pds) ->
                                                            map (\(p,ds) -> PrFormula p (dsUnion ds fDs) (injNominal r newUr)) pds
                                                         )

                          formulasToSend  = formulasToSend1 ++ formulasToSend2 ++ functionalityNominalToSend ++ injectivityNominalsToSend

                          newPrefToUevFwd
                           = if hasTransClos br
                              then DMap $ moveInMap (toMap $ prefToUevFwd br) oldUr newUr ( Map.unionWith dsUnion )
                              else prefToUevFwd br

                          newPrefToUevBwd
                           = if hasTransClos br
                              then DMap $ moveInMap (toMap $ prefToUevBwd br) oldUr newUr ( Map.unionWith dsUnion )
                              else prefToUevBwd br

                          formulasToAdd  = nubAndMergeDeps (PrFormula newUr fDs f2:formulasToSend)
                          newBr             = br{nomPrefClasses = classes3,
                                                 boxConstrFwd   = newBoxConstrFwd,
                                                 boxConstrBwd   = newBoxConstrBwd,
                                                 accStr         = newAccStr,
                                                 prToDepSet     = newPrToDepSet,
                                                 prefToForms    = newPrefToForms,
                                                 branchTrueForms= newbranchTrueForms,
                                                 prefToUevFwd   = newPrefToUevFwd,
                                                 prefToUevBwd   = newPrefToUevBwd,
                                                 diaRlCh        = newDiaRlCh,
                                                 diaXRlCh       = newDiaXRlCh,
                                                 boxXRlCh       = newBoxXRlCh,
                                                 clashStr       = newClashStr}
                      in
                          addFormulas clp newBr formulasToAdd ((newUr,n):history)


-- if Unit Propagation enabled : try to reduce disjunction
addFormula clp br pf@(PrFormula pr ds disF@(Dis fs)) _
 = if not $ unitProp clp
    then addFormulaBaseCase clp br pf
    else case reduceDisjunctionAgainstBranch br pr fs of
           Triviality              -> BranchOK br
           Contradiction dsClash   -> BranchClash br pr (dsUnion ds dsClash) disF
           Reduced newDs disjuncts -> addFormulaBaseCase clp br (PrFormula pr (dsUnion ds newDs) (Dis disjuncts))

addFormula clp br f _
 = addFormulaBaseCase clp br f

addFormulaBaseCase :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormulaBaseCase clp br f@(PrFormula pr ds f2)
 = addFormula2 clp newBr fToAdd
    where
      (urfather,ds2,newClasses) = getUrfatherAndDeps br (DS.Prefix pr)
      newBr = br{nomPrefClasses = newClasses}
      fToAdd = if urfather == pr -- always the case if we are in the modal language
                then f
                else PrFormula urfather (dsUnion ds ds2) f2

addFormula2 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2 clp br pf@(PrFormula pr _ f) =
   addFormula3 clp br5 pf
 where
     br2 = addToBranchTrueForms br pf -- TODO if cache ...
     br3 = if forInclusion br f
             then addToPrefToForms br2 pf
             else br2
     br4 = updatePrefToUev br3 pr f
     --br5 = addToNotPrevPref pr br4 -- TODO if cache ...
     br5 = addToAugmentedPrefixes pr br4

addFormula3 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula3 _ br pf@(PrFormula _ _ (Con _))
           = BranchOK $ addToTodo br pf

addFormula3 _ br pf@(PrFormula _ _ (Dis _))
           = BranchOK $ addToTodo br pf

addFormula3 clp br_ (PrFormula pr ds (Box r f))
           = let br = case r of { InvRelSymbol _ -> blockChain br_ ; _ -> br_ } in
             addBoxConstraint clp br pr r f ds

addFormula3 clp br (PrFormula pr ds (BoxX r f))
           = addBoxXConstraint clp br pr r f ds

addFormula3 _ br_ pf@(PrFormula pr _ f2@(Dia r _))
           = let br = case r of { InvRelSymbol _ -> blockChain br_ ; _ -> br_ } in
             BranchOK $ if diaAlreadyDone br pr f2
                          then br                  -- diamond rule saturation
                          else addToTodo br pf

addFormula3 _ br pf@(PrFormula pr ds f2@(DiaX r f))
           = BranchOK $ if diaXAlreadyDone br pr f2
                          then br                  -- diamondX rule saturation
                          else addDiaXUev br' pr ds r f
                                 where br' = blockChain $ addToTodo br pf

addFormula3 clp br (PrFormula _ ds (A f))
           = addUnivConstraint clp br ds f

addFormula3 clp br (PrFormula pr ds (B f))
           = addDiffUnivConstraint clp br ds f pr

addFormula3 _ br pf@(PrFormula _ _ f2@(E _))
           = BranchOK $ if existAlreadyDone br f2  -- exist rule saturation
                         then br
                         else addToTodo br{existRlCh = Set.insert f2 (existRlCh br)} pf

addFormula3 _ br pf@(PrFormula _ _ (D _))
           = BranchOK $ addToTodo br pf

addFormula3 _ br pf@(PrFormula _ _ f2@(At _ _))
           = BranchOK $ if atAlreadyDone br f2  -- at rule saturation
                         then br
                         else addToTodo br{atRlCh = Set.insert f2 (atRlCh br)} pf

addFormula3 _ br pf@(PrFormula pr _ f2@(Down _ _))
           = BranchOK $ if downAlreadyDone br pr f2
                            then br                            -- down-arrow rule saturation
                            else addToTodo br pf

addFormula3 _ br (PrFormula pr ds (Lit l)) = addAndUpdateMap br pr ds l


{- todo list functions -}

addToTodo :: Branch -> PrFormula -> Branch
addToTodo br pf@(PrFormula _ _ f2) =
 br{todoList = newTodoList}
 where
   newTodoList =
     case todoList br of
      Fair srs -> Fair (srs ++ [SR_Formula pf])
      utodo    ->
       case f2 of
         Con _    -> utodo{conjStr  = Set.insert pf (conjStr utodo)}
         Dis _    -> utodo{disjStr  = Set.insert pf (disjStr utodo)}
         Dia _ _  -> utodo{diaStr   = Set.insert pf (diaStr utodo)}
         DiaX _ _ -> utodo{diaXStr  = Set.insert pf (diaXStr utodo)}
         E _      -> utodo{existStr = Set.insert pf (existStr utodo)}
         D _      -> utodo{diffStr  = Set.insert pf (diffStr utodo)}
         At _ _   -> utodo{atStr    = Set.insert pf (atStr utodo)}
         Down _ _ -> utodo{downStr  = Set.insert pf (downStr utodo)}
         _        -> error "addToTodo"


{-    helper functions for equivalence class merge     -}

nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added to a branch
-- as several prefixed formulas with different branching dependencies. This functions takes
-- a list of prefixes formulas, looks which inner formulas are the same and merge their
-- branching dependencies.
nubAndMergeDeps prfs =  namd prfs (Map.empty::Map.Map (Prefix,Formula) DependencySet)

namd :: [PrFormula] -> Map.Map (Prefix,Formula) DependencySet -> [PrFormula]
namd ((PrFormula p ds f):prfs) theMap =
  namd prfs (Map.insertWith dsUnion (p,f) ds theMap)

namd [] theMap = map (\((p,f),ds) -> PrFormula p ds f) (Map.assocs theMap)

{-
   Functions related to vId, nom, prefixes and nominals ...
-}


--to fill the new field
addToBranchTrueForms :: Branch -> PrFormula -> Branch
addToBranchTrueForms br (PrFormula pre dps f) =
  br{branchTrueForms = newMap}
 where currentBtf = branchTrueForms br
       newMap = DMap.insertWith dsUnion pre f dps currentBtf


addToPrefToForms :: Branch -> PrFormula -> Branch
addToPrefToForms br (PrFormula pre _ f) =
  br{prefToForms = newMap}
 where currentPtf = prefToForms br
       newMap = Map.insertWith Set.union pre (Set.singleton f) currentPtf

{-     handling nominal urfathers, equivalence classes and dependencies     -}

isNominalUrfather :: Branch -> Prefix -> Bool
isNominalUrfather b p = DS.isRoot (DS.Prefix p) classes
                         where classes = nomPrefClasses b

getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather b p = u
                  where (u,_,_) = getUrfatherAndDeps b p

getUrfatherAndDeps :: Branch -> DS.Pointer -> (Prefix,DependencySet,EquivClasses)
getUrfatherAndDeps br p =
   if DS.isRoot p classes then defaultAnswer
                          else (ur,deps,newClasses)
  where classes = nomPrefClasses br
        (urfather, newClasses) = DS.find p classes
        (DS.Prefix ur) = urfather
        DS.Prefix unboxedP = p
        defaultAnswer = (unboxedP,dsEmpty,classes)
        deps = findDeps br ur

findDeps :: Branch -> Prefix -> DependencySet
findDeps br pr = Map.findWithDefault dsEmpty pr (prToDepSet br)

addClassDeps :: Prefix -> DependencySet -> Branch -> Branch
addClassDeps pr ds br = br { prToDepSet = Map.insertWith dsUnion pr ds (prToDepSet br) }


-- check if the added formula removes an unfulfilled eventuality
-- if yes, propagate to the previous prefixes
updatePrefToUev :: Branch -> Prefix -> Formula -> Branch
updatePrefToUev br pr f = let br2 = updatePrefToUevFwd br pr f in updatePrefToUevBwd br2 pr f

updatePrefToUevFwd :: Branch -> Prefix -> Formula -> Branch
updatePrefToUevFwd br pr' f =
 case DMap.lookup1 pr $ prefToUevFwd br of
   Nothing     -> br
   Just uevs   -> let (toRemove,toKeep) = Map.partitionWithKey (\(f2,_) _ -> f2==f) uevs
                      newUevs = toKeep
                      relsToCrawl = map snd $ Map.keys toRemove
                      newPrefToUev = if Map.null newUevs -- not sure if we need to separate the two cases
                                      then DMap.delete pr          $ prefToUevFwd br
                                      else DMap.insert1 pr newUevs $ prefToUevFwd br
                      previousPrefixes = concatMap (findPreviousPrefixes br pr) relsToCrawl
                  in
                      foldr (\pp br_ -> updatePrefToUev br_ pp f)
                            br{prefToUevFwd = newPrefToUev}
                            previousPrefixes
 where pr = getUrfather br (DS.Prefix pr')

updatePrefToUevBwd :: Branch -> Prefix -> Formula -> Branch
updatePrefToUevBwd br pr' f =
 case DMap.lookup1 pr $ prefToUevBwd br of
   Nothing     -> br
   Just uevs   -> let (toRemove,toKeep) = Map.partitionWithKey (\(f2,_) _ -> f2==f) uevs
                      newUevs = toKeep
                      relsToCrawl = map snd $ Map.keys toRemove
                      newPrefToUev = if Map.null newUevs -- not sure if we need to separate the two cases
                                      then DMap.delete pr          $ prefToUevBwd br
                                      else DMap.insert1 pr newUevs $ prefToUevBwd br
                      followingPrefixes = concatMap (findFollowingPrefixes br pr) relsToCrawl
                  in
                      foldr (\pp br_ -> updatePrefToUev br_ pp f)
                            br{prefToUevBwd = newPrefToUev}
                            followingPrefixes
 where pr = getUrfather br (DS.Prefix pr')


findPreviousPrefixes :: Branch -> Prefix -> Rel -> [Prefix]
findPreviousPrefixes br p r = map fst $ getPredecessors (accStr br) p r

findFollowingPrefixes :: Branch -> Prefix -> Rel -> [Prefix]
findFollowingPrefixes br p r = map fst $ getSuccessors (accStr br) p r

{-     box-related constraints     -}

newFormulasToSend :: DependencySet -> (Map.Map Rel [(DependencySet,Formula)], Map.Map Rel [(Prefix,DependencySet)]) -> [PrFormula]
newFormulasToSend deps (mapBox, mapAcc)
 = [PrFormula p (dsUnions [deps,ds1,ds2]) f |
                      r1 <- Map.keys mapBox,
                      r2 <- Map.keys mapAcc,    r1 == r2,
                      (ds1,f) <- (Map.!) mapBox r1,
                      (p,ds2) <- (Map.!) mapAcc r2     ]

addBoxConstraint :: CmdLineParams -> Branch -> Prefix -> RelSymbol -> Formula -> DependencySet -> BranchInfo
addBoxConstraint clp br pr_ (RelSymbol r) f ds
 = addFormulas clp newBr toAdd []
   where pr = getUrfather br (DS.Prefix pr_)
         newBr = br{boxConstrFwd = updateBoxConstr pr r f ds (boxConstrFwd br)}
         accessiblePrDs   = getSuccessors (accStr br) pr r
         toAdd = symApplications ++ transApplications ++ boxApplications
         transApplications = if isTransitive (relInfo br) (RelSymbol r)
                             then map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) (Box (RelSymbol r) f)) accessiblePrDs
                             else []
         symApplications = if isSymmetric (relInfo br) (RelSymbol r) then [PrFormula pr ds $ box (InvRelSymbol r) f] else []
         boxApplications = map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) f) accessiblePrDs

addBoxConstraint clp br pr_ (InvRelSymbol r) f ds
 = addFormulas clp newBr toAdd []
   where pr = getUrfather br (DS.Prefix pr_)
         newBr = br{boxConstrBwd = updateBoxConstr pr r f ds (boxConstrBwd br)}
         accessiblePrDs        = getPredecessors (accStr br) pr r
         toAdd = transApplications ++ boxApplications
         transApplications = if isTransitive (relInfo br) (RelSymbol r)
                             then map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) (Box (InvRelSymbol r) f)) accessiblePrDs
                             else []
         boxApplications = map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) f) accessiblePrDs

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> Box_constraints -> Box_constraints
updateBoxConstr p1_ r_ f_ ds_ (DMap boxConstr_) =
  case Map.lookup p1_ boxConstr_ of
    Nothing       -> DMap $ Map.insert p1_ (Map.singleton r_ [(ds_,f_)]) boxConstr_
    Just innerMap -> case Map.lookup r_ innerMap of
                       Nothing             -> DMap $ Map.insert p1_ (Map.insert r_ [(ds_,f_)] innerMap)                boxConstr_
                       Just innerInnerList -> DMap $ Map.insert p1_ (Map.insert r_ ((ds_,f_):innerInnerList) innerMap) boxConstr_


-- [*]phi --> phi & [][*]phi
-- need not to do all that addBoxConstraint does
addBoxXConstraint :: CmdLineParams -> Branch -> Prefix -> RelSymbol -> Formula -> DependencySet -> BranchInfo
addBoxXConstraint clp br nonRepresentativePr r f ds
 = if boxXAlreadyDone br pr (BoxX r f)
    then BranchOK br
    else addFormulas clp br2 [PrFormula pr ds f,
                     PrFormula pr ds (Box r (BoxX r f))]
                     []
   where pr = getUrfather br (DS.Prefix nonRepresentativePr)
         br2 = addBoxXRuleCheck br pr (BoxX r f)

addBoxXRuleCheck :: Branch -> Prefix -> Formula -> Branch
addBoxXRuleCheck br pr f =
  br{boxXRlCh=Map.insertWith Set.union ur (Set.singleton f) (boxXRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

boxXAlreadyDone :: Branch -> Prefix -> Formula -> Bool
boxXAlreadyDone b p f@(BoxX _ _) =
  case Map.lookup ur (boxXRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

boxXAlreadyDone _ _ _ = error "boxX already done : wrong formula kind"

addAccFormula :: CmdLineParams -> Branch -> AccFormula -> BranchInfo
addAccFormula clp br (AccFormula ds (RelSymbol r) p1_ p2_)
 = addFormulas clp newBr toAdd []
   where toAdd = transApplications ++ funcApplications ++ injApplications ++ boxApplications
         transApplications = if isTransitive (relInfo br) (RelSymbol r)
                              then
                               (  ( map (\(ds2,f) -> PrFormula p2 (dsUnion ds ds2) (Box (RelSymbol r) f)) toSendFwd )
                               ++ ( map (\(ds2,f) -> PrFormula p1 (dsUnion ds ds2) (Box (RelSymbol r) f)) toSendBwd )  )
                              else []
         funcApplications = if isFunctional (relInfo br) r
                             then [PrFormula p2 ds (funcNominal r p1)] -- add nominal to destination
                             else []
         injApplications = if isInjective (relInfo br) r
                            then [PrFormula p1 ds (injNominal r p1)] -- add nominal to origin
                            else []
         boxApplications =  (  ( map (\(ds2,f) -> PrFormula p2 (dsUnion ds ds2) f) toSendFwd )
                            ++ ( map (\(ds2,f) -> PrFormula p1 (dsUnion ds ds2) f) toSendBwd )  )
         p1 = getUrfather br (DS.Prefix p1_)
         p2 = getUrfather br (DS.Prefix p2_)
         newBr    = insertRelationBranch br p1 r p2 ds
         toSendFwd = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p1 (toMap $ boxConstrFwd br) -- [(DependencySet,Prefix)]
         toSendBwd = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p2 (toMap $ boxConstrBwd br) -- [(DependencySet,Prefix)]

addAccFormula clp br (AccFormula ds (InvRelSymbol r) p1_ p2_ ) -- so, create p2<>p1
 = addAccFormula clp br (AccFormula ds (RelSymbol r) p2_ p1_)

insertRelationBranch :: Branch -> Prefix -> Rel -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 r p2 ds
 = br{accStr = insertRelation (accStr br) p1 r p2 ds}

{-  functional relations  -}

funcNominal :: Rel -> Prefix -> Formula
funcNominal r p = nom $ NomSymbol $ "f_" ++ r ++ show p

{-  injective relations  -}

injNominal :: Rel -> Prefix -> Formula
injNominal r p = nom $ NomSymbol $ "i_" ++ r ++ show p

{-  functions related to blocking conditions and model building -}

isNotBlocked :: Branch -> Prefix -> Bool
isNotBlocked br pr =
 case blockMode br of
   InclusionBlockingGlobal -> let ur =  getUrfather br (DS.Prefix pr) in
                              getModelRepresentative br ur == ur  -- i'm not happy to call this model related function
   InclusionBlockingChain  -> not $ isChainInclusionBlocked br pr
   ChainBlocking           -> not $ isChainBlocked br pr

isChainInclusionBlocked :: Branch -> Prefix -> Bool
isChainInclusionBlocked  br pr =
  go br ur ur
 where ur = getUrfather br (DS.Prefix pr)
       go :: Branch -> Prefix -> Prefix -> Bool
       go br_ initial current =
          case fatherOf current of
            Nothing       -> False
            Just ancestor -> let urAncestor = getUrfather br (DS.Prefix ancestor) in
                             if formulasIncluded br_ initial urAncestor
                              then True else go br_ initial ancestor
       parentMap    = prefParent br
       fatherOf pr_ = Map.lookup pr_ parentMap

isChainBlocked :: Branch -> Prefix -> Bool
isChainBlocked br pr = test2equal $ map (formulasOf br) (getAllParents br pr)

getAllParents :: Branch -> Prefix -> [Prefix]
-- getAllParents up to one that has an input nominal
getAllParents br pr = (getUrfather br (DS.Prefix pr)):rest
 where rest = case Map.lookup pr (prefParent br) of
                Nothing     -> []
                Just parent -> if isNominalUrfather br parent
                                then getAllParents br parent
                                else [getUrfather br (DS.Prefix parent)]


test2equal :: (Ord a) => [Set a] -> Bool -- inefficient
test2equal (s:sets) = any ((==) s) sets || test2equal sets
test2equal [] = False


isInTheModel :: Branch -> Prefix -> Bool
isInTheModel br pr
 = if isNominalUrfather br pr
    then
     case blockMode br of
       InclusionBlockingGlobal ->  (getModelRepresentative br pr) == pr
       InclusionBlockingChain  ->  (getModelRepresentative br pr) == pr
       ChainBlocking           ->  case findModelRepresentativeChainBlocking br pr of
                                    Nothing   -> False
                                    Just repr -> repr == pr
   else False

relationIsInTheModel :: Branch -> (Prefix,Rel,Prefix) -> Bool
relationIsInTheModel br (p1,_,p2)
 = case blockMode br of
     ChainBlocking            -> hasIdentityUrfather br p1 && hasIdentityUrfather br p2
     _                        -> isInTheModel br p1
   where hasIdentityUrfather br_ pr_
          = case findModelRepresentativeChainBlocking br_ pr_ of {Nothing -> False ; _ -> True }

getModelRepresentative :: Branch -> Prefix -> Prefix  -- which is also an inclusion representative
getModelRepresentative br pr
 = case blockMode br of
    InclusionBlockingGlobal -> giu_get_oldest (fromJust $ inclUrMap br) nomUrfather
                                where nomUrfather = getUrfather br (DS.Prefix pr)
                                      giu_get_oldest :: InclusionUrfathersMap -> Prefix -> Prefix
                                       -- request "includer" prefix until fixpoint reached
                                      giu_get_oldest ium pr_
                                       = if parent == pr_ then pr_ else giu_get_oldest ium parent
                                          where parent = ium Map.! pr_
    InclusionBlockingChain  -> -- find the *oldest* inclusion urfather on the chain
                                 go br nomUrfather nomUrfather Nothing
                                where nomUrfather = getUrfather br (DS.Prefix pr)
                                      go :: Branch -> Prefix -> Prefix -> Maybe Prefix -> Prefix
                                      go br_ initial current mBlocker =
                                         case fatherOf current of
                                           Nothing       -> fromMaybe initial mBlocker
                                           Just ancestor -> let urAncestor = getUrfather br (DS.Prefix ancestor) in
                                                            if formulasIncluded br_ initial urAncestor
                                                             then go br_ initial ancestor (Just urAncestor)
                                                             else go br_ initial ancestor mBlocker
                                      parentMap    = prefParent br
                                      fatherOf pr_ = Map.lookup pr_ parentMap
    ChainBlocking -> case findModelRepresentativeChainBlocking br pr of
                      Nothing -> error ("found an interesting counter example " ++ show pr)
                      Just repr -> repr


findModelRepresentativeChainBlocking :: Branch -> Prefix -> Maybe Prefix
findModelRepresentativeChainBlocking br pr
 =  go br pr 0
     where
       go :: Branch -> Prefix -> Prefix -> Maybe Prefix
       go br_ initial current =
          let urCurrent =  getUrfather br (DS.Prefix current) in
           if urCurrent == initial
            then if isChainBlocked br initial then Nothing else Just initial
            else if (sameSetOfFormulas br_ initial urCurrent) && (not $ isChainBlocked br urCurrent)
                   then Just urCurrent
                   else go br_ initial (current+1)


calculateInclusionUrfathers :: Branch -> Branch
-- calculates the prefix -> inclusion urfather map incrementally, by
-- updating the map from the given prefix, which typically is the smallest augmented
-- prefix in the previous step

-- if the inclusion urfather blocking mode is enabled, we handle this map
-- if not, we let it as it is
calculateInclusionUrfathers br =
    br{inclUrMap = newInclUrMap}
     where newInclUrMap =  case blockMode br of
                            InclusionBlockingGlobal -> Just $ calculateInclusionUrfathersMap br
                            _                       -> Nothing

calculateInclusionUrfathersMap :: Branch -> InclusionUrfathersMap
calculateInclusionUrfathersMap br = 
  case inclUrMap br of
   Just previousM -> if null $ incrPrs br
                      then fromScratchInclUrMap        -- this case is reached if we applied the (A) rule  -- does it happen ??
                      else updateInclUrMap previousM  -- works, provided that the augmented prefixes list is correctly filled
   Nothing        -> fromScratchInclUrMap

 where updateInclUrMap prevM  = foldr     updateM        prevM           (filter (isNominalUrfather br) [pr..(lastPref br)])
       fromScratchInclUrMap   = foldr     updateM        emptyM          (filter (isNominalUrfather br) (prefixes br))

       updateM pref currentM_ = condFoldr (oneStep pref) currentM        (filter (isNominalUrfather br) (reverse [0..pref-1]))
                                 where currentM = Map.insert pref pref currentM_
       oneStep pref pref2 iuMap =
         if formulasIncluded br pref pref2
             then (Map.insert pref pref2 iuMap,False) -- if inclusion, update map and stop
             else (iuMap, True)
       smallestModifiedPrefix = minimum $ incrPrs br 
       pr = smallestModifiedPrefix
       emptyM = Map.empty::InclusionUrfathersMap


condFoldr :: (a -> b -> (b,Bool)) -> b -> [a] -> b
condFoldr _ lastB    []      = lastB
condFoldr f initialB (hd:tl)
   = let (newB,continue) = f hd initialB in
      if continue then condFoldr f newB tl else newB

formulasIncluded :: Branch -> Prefix -> Prefix-> Bool
formulasIncluded br p1 p2 = (formulasOf br p1) `Set.isSubsetOf` (formulasOf br p2)

sameSetOfFormulas :: Branch -> Prefix -> Prefix -> Bool
sameSetOfFormulas br p1 p2 = (formulasOf br p1) == (formulasOf br p2)

-- maybe should get the urfather of given prefix, so that the caller functions won't have to do it
formulasOf :: Branch -> Prefix -> Set.Set Formula
formulasOf br p = Map.findWithDefault Set.empty p (prefToForms br)

-- is the formula useful to calculate inclusion urfathers ?
forInclusion :: Branch -> Formula -> Bool
forInclusion br (Lit (PosLit atom)) = forInclAtom br atom
forInclusion br (Lit (NegLit atom)) = forInclAtom br atom
forInclusion _ (Con _) = False
forInclusion _ (Dis _) = False
forInclusion _ (At _ _) = False
forInclusion _ (Down _ _) = False
forInclusion _ (Box _ _) = True
forInclusion _ (Dia _ _) = True
forInclusion _ (BoxX _ _) = True
forInclusion _ (DiaX _ _) = True
forInclusion _ (A _) = False
forInclusion _ (E _) = False
forInclusion _ (D _) = False
forInclusion _ (B _) = False

forInclAtom :: Branch -> Atom -> Bool
forInclAtom _  Taut  = False
forInclAtom br (N n) = Set.member n (relevantNominals br)
forInclAtom _  (P _) = True

addParentPrefix :: Branch -> Prefix -> Prefix -> Branch
addParentPrefix br son father =  br{prefParent = Map.insert son father (prefParent br)}

{-     book-keeping that needs to be done before each step of the tableaux calculus     -}

calculateStepInfo :: Branch -> Branch
calculateStepInfo = wipeAugmentedPrefixes . calculateInclusionUrfathers

wipeAugmentedPrefixes :: Branch -> Branch
wipeAugmentedPrefixes br = br{incrPrs=[]}

addToAugmentedPrefixes :: Prefix -> Branch -> Branch
addToAugmentedPrefixes pr br = br{incrPrs = (pr:incrPrs br)}

--To keep the prefixes true at b-b1, where b is the current branch, and b1 is prev(b)
setPrevPref :: Branch -> Branch
setPrevPref br = br{prevPref = prefixes br}

-- addToNotPrevPref :: Prefix -> Branch -> Branch
-- addToNotPrevPref pr br = br{notPrevPref = (pr:notPrevPref  br)}


{-     modifications done by rule application     -}

addDiaRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDiaRuleCheck br pr f =
  br{diaRlCh=Map.insertWith Set.union ur (Set.singleton f) (diaRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaAlreadyDone :: Branch -> Prefix -> Formula -> Bool
diaAlreadyDone b p f@(Dia _ _) =
  case Map.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ _ = error "dia already done : wrong formula kind"
--

addDiaXRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDiaXRuleCheck br pr f =
  br{diaXRlCh=Map.insertWith Set.union ur (Set.singleton f) (diaXRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaXAlreadyDone :: Branch -> Prefix -> Formula -> Bool
diaXAlreadyDone b p f@(DiaX _ _) =
  case Map.lookup ur (diaXRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

diaXAlreadyDone _ _ _ = error "diaX already done : wrong formula kind"

-- for a given prefix and relation, add a formula and its branching prefixes to the
-- set of uevs
-- if the same formula is already here, merge branching prefixes
addDiaXUev :: Branch -> Prefix -> DependencySet -> RelSymbol -> Formula -> Branch
addDiaXUev br pr' ds (RelSymbol r) f
 = case DMap.lookup1 pr $ prefToUevFwd br of
    Nothing      -> let ptu = DMap.insert1 pr (Map.singleton (f,r) ds) (prefToUevFwd br) in
                       br{prefToUevFwd = ptu}
    Just uevs    -> case Map.lookup (f,r) uevs of
                     Nothing      -> let newUevs = Map.insert (f,r) ds uevs in
                                       br{prefToUevFwd = DMap.insert1 pr newUevs $ prefToUevFwd br}
                     Just ds2     -> let newUevs = Map.insert (f,r) (dsUnion ds ds2) uevs in
                                       br{prefToUevFwd = DMap.insert1 pr newUevs $ prefToUevFwd br}
  where pr = getUrfather br (DS.Prefix pr')

addDiaXUev br pr' ds (InvRelSymbol r) f -- inverse modality
 = case DMap.lookup1 pr $ prefToUevBwd br of
    Nothing      -> let ptu = DMap.insert1 pr (Map.singleton (f,r) ds) (prefToUevBwd br) in
                       br{prefToUevBwd = ptu}
    Just uevs    -> case Map.lookup (f,r) uevs of
                     Nothing      -> let newUevs = Map.insert (f,r) ds uevs in
                                       br{prefToUevBwd = DMap.insert1 pr newUevs $ prefToUevBwd br}
                     Just ds2     -> let newUevs = Map.insert (f,r) (dsUnion ds ds2) uevs in
                                       br{prefToUevBwd = DMap.insert1 pr newUevs $ prefToUevBwd br}
  where pr = getUrfather br (DS.Prefix pr')
-- TODO ^ ^ ^ ^ code redondant


collectUevBprs :: Branch -> DependencySet
collectUevBprs br
 =  dsUnion ( Map.fold getAndMergeDs dsEmpty (toMap $ prefToUevFwd br) )
            ( Map.fold getAndMergeDs dsEmpty (toMap $ prefToUevBwd br) )
   where getAndMergeDs :: Map.Map (Formula,Rel) DependencySet -> DependencySet -> DependencySet
         getAndMergeDs m ds = dsUnions (ds:Map.elems m)

--

addDownRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDownRuleCheck br pr f =
  br{downRlCh=Map.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

downAlreadyDone :: Branch -> Prefix -> Formula -> Bool
downAlreadyDone b p f@(Down _ _) =
  case Map.lookup ur (downRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

downAlreadyDone _ _ _ = error "down already done : wrong formula kind"

--

existAlreadyDone :: Branch -> Formula -> Bool
existAlreadyDone b f@(E _) = Set.member f (existRlCh b)
existAlreadyDone _ _ = error "exist already done : wrong formula kind"

--

atAlreadyDone :: Branch -> Formula -> Bool
atAlreadyDone b f@(At _ _) = Set.member f (atRlCh b)
atAlreadyDone _ _ = error "at already done : wrong formula kind"

--

addUnivConstraint :: CmdLineParams -> Branch -> DependencySet -> Formula -> BranchInfo
addUnivConstraint clp br ds f
 = addFormulas clp newBr
               ( map (\p -> PrFormula p ds f) urfathers )
               []
   where newBr = br{univCons = (ds,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

--

addDiffUnivConstraint :: CmdLineParams -> Branch -> DependencySet -> Formula -> Prefix -> BranchInfo
addDiffUnivConstraint clp br ds f pr
 = addFormulas clp newBr
               ( (PrFormula pr ds $ nom newNom)
                 :(map (\somePrefix -> PrFormula somePrefix ds (Dis $ set [f, nom newNom])) otherUrfathers)
               )
               []
   where currentUrfather = getUrfather br (DS.Prefix pr)
         prefs = [0..(lastPref br)]
         otherUrfathers = delete currentUrfather $ filter (isNominalUrfather br) prefs
         (updatedBr, newNom) = createNewNom br
         newBr = updatedBr{dBoxCons = (ds,f,newNom):(dBoxCons updatedBr)}

--

addDiffRuleCheck :: Branch -> Formula -> PropSymbol -> Bool -> Branch
addDiffRuleCheck br f propsym b =
  br{dDiaRlCh=Map.insert f (propsym,b) (dDiaRlCh br)}

--

getUnappliedUBPairs :: Branch -> [(Prefix,Prefix)]
getUnappliedUBPairs br =
 [ (a,b) | a <- [i..lastP], -- lastP >= a >=i
           b <- [0..(a-1)], -- a > b
           (a == i && b > j) || (a > i),
           ur a /= ur b
 ]
 where (i,j) = bookKeepUB br -- i > j
       lastP = lastPref br
       ur = (getUrfather br) . DS.Prefix

updateUBBookKeep :: Prefix -> Prefix -> Branch -> Branch
updateUBBookKeep p1 p2 br
 = case todoList br of
    Fair _ ->  br
    _      ->  br{bookKeepUB = (p1,p2)}
-- UGLY because if there's a fair schedule, the book keep is already updated


--

createNewPref :: CmdLineParams -> Branch -> BranchInfo
createNewPref clp br
 = addFormulas clp newBrWithRefl
                         (   map (\(ds,f) -> PrFormula newPr ds f) univConstraints
                          ++ map (\(ds,f,newNom) -> PrFormula newPr ds (Dis $ set [f, nom newNom])) diffBoxConstraints)
                         []
   where newPr = lastPref br + 1
         newBr_ = br{lastPref = newPr}
         newBr = case todoList br of
                    Fair _ -> addUBlockingSchedule newBr_
                    _      -> newBr_
         univConstraints = univCons br
         diffBoxConstraints = dBoxCons br
         newBrWithRefl = addReflexiveLinks newPr newBr


addUBlockingSchedule :: Branch -> Branch
addUBlockingSchedule br
 = if (l == 0) || ( (snd $ bookKeepUB br) == l - 1)
    then br
    else br{ bookKeepUB = (l,l-1),
             todoList   = newTodo
           }
    where l       = lastPref br
          newSrs  = map (uncurry SR_UBlocking) $ getUnappliedUBPairs br
          newTodo = let Fair srs = todoList br in Fair (srs ++ newSrs)

addReflexiveLinks :: Prefix -> Branch -> Branch
addReflexiveLinks pr br
 = foldr (\rel_ br_ -> insertRelationBranch br_ pr rel_ pr dsEmpty) br reflRels
   where reflRels = map ((\(RelSymbol r) -> r) . fst) $ filter (\(_,props) -> Reflexive `elem` props) (relInfo br)


--

incPropSymbol :: PropSymbol -> PropSymbol
incPropSymbol (PropSymbol n) = PropSymbol (nextName n)


createNewProp :: Branch -> Branch
createNewProp br
 = br{lastProp = Just newProp}
    where newProp = maybe (PropSymbol newPropBaseName) incPropSymbol (lastProp br)

--

incNomSymbol :: NomSymbol -> NomSymbol
incNomSymbol (NomSymbol n) = NomSymbol (nextName n)

createNewNom :: Branch -> (Branch, NomSymbol)
createNewNom br
 = (br{lastNom = Just newNom}, newNom)
    where newNom =  maybe (NomSymbol newNomBaseName) incNomSymbol (lastNom br)


createNewNomTestRelevance :: Branch -> Formula -> Branch
createNewNomTestRelevance br f
 = br{lastNom = Just newNom ,
      relevantNominals = if relevant then Set.insert newNom (relevantNominals br) else relevantNominals br,
      downVarRelevantCh = newDVRC
     }
   where (relevant, newDVRC) = doMemoize checkIfVariableNegatedOnce f (downVarRelevantCh br)
         newNom = maybe (NomSymbol newNomBaseName) incNomSymbol (lastNom br)

--

newNomBaseName, newPropBaseName :: String
newNomBaseName = "0N"
newPropBaseName = "0P"

nextName :: String -> String
nextName name
 = newNumString ++ remainder
   where (numString,remainder) = span isNumber name
         newNumString          = increaseNumString numString
         increaseNumString ss  = show ((read ss) + 1::Int)


--

processTodoList :: Branch -> Branch
processTodoList br =
 br{todoList = newTodo}
 where newTodo
        = case todoList br of
            Fair (_:srs) -> Fair srs
            Fair []      -> error "processTodoList : empty todo list"
            _            -> error "processTodoList : wrong strategy"


remFormula :: Branch  -> PrFormula -> Branch
remFormula br pf@(PrFormula _ _ f2)
 = br{todoList = newTodoList}
   where
    newTodoList =
     case todoList br of
      f@(Fair _) -> f
      utodo ->
       case f2 of
        Con _    -> utodo{conjStr =(Set.delete pf (conjStr  utodo))}
        Dis _    -> utodo{disjStr =(Set.delete pf (disjStr  utodo))}
        Dia _ _  -> utodo{diaStr  =(Set.delete pf (diaStr   utodo))}
        DiaX _ _ -> utodo{diaXStr =(Set.delete pf (diaXStr  utodo))}
        At _ _   -> utodo{atStr   =(Set.delete pf (atStr    utodo))}
        E _      -> utodo{existStr=(Set.delete pf (existStr utodo))}
        D _      -> utodo{diffStr =(Set.delete pf (diffStr  utodo))}
        Down _ _ -> utodo{downStr =(Set.delete pf (downStr  utodo))}
        _        -> error "remFormula unfair strategy"

-- preparation of the branch at the beginning of the calculus:
--  - add the input formula at prefix 0
--  - add a nominal formula at a fresh prefix for each nominal of the input formula

addFirstFormulas :: CmdLineParams -> Branch -> Formula -> LanguageInfo -> BranchInfo
addFirstFormulas clp br_ f fLang
 = addFormulas clp br ( pf : ( map (\(p,n) ->  PrFormula p dsEmpty (nom n)) $ zip [1..] ns)) []
    where ns = languageNoms fLang
          nbNs = length ns
          noms = [1..nbNs]
          br =  foldr addReflexiveLinks (  br_{lastPref = nbNs} ) noms
          pf = firstPrefixedFormula f

gen_unsat_cache :: CmdLineParams -> Formula -> UCache
gen_unsat_cache clp f = case caching clp of
                          Just MatrixCaching
                                -> let c = ((get_max_subterms f)+(get_num_nominals f)) * 2
                                   in UCache{matrix = UCMatrix.empty c c,
                                         listsList = [],--not used in this approach
                                               current_index =(-1),
                                               descrip_matrix = Bimap.empty,
                                               current_row = (-1),
                                               max_row=(c-1)}
                          Just ListCaching
                                   -> UCache{matrix = UCMatrix.empty 0 0,--not used in this approach
                                      listsList = [],
                                            current_index =(-1),
                                            descrip_matrix = Bimap.empty,
                                            current_row = (-1),
                                            max_row=0}  --not used in this approach
                          Nothing
                           -> UCache{matrix = UCMatrix.empty 0 0,--not used in this approach
                                              listsList = [],
                                              current_index =(-1),
                                              descrip_matrix = Bimap.empty,
                                              current_row = (-1),
                                              max_row=0}  --not used in this approach



{-     functions to handle the "clashable information", ie literals associated to prefixes     -}

data UpdateResult = UpdateSuccess Clashable_info | UpdateFailure DependencySet

addAndUpdateMap :: Branch -> Prefix -> DependencySet -> Literal -> BranchInfo
addAndUpdateMap br pr ds l
  = case ( case l of PosLit a -> updateMap (clashStr br) pr ds a True
                     NegLit a -> updateMap (clashStr br) pr ds a False ) of
     UpdateSuccess cs  -> BranchOK br{clashStr = cs}
     UpdateFailure ds2 -> BranchClash br pr ds2 (Lit l)


-- Insert a piece of clashable information into all the clashable information of a branch

updateMap :: Clashable_info -> Prefix -> DependencySet -> Atom -> Bool -> UpdateResult
updateMap cs  _  _   Taut True = UpdateSuccess cs
updateMap _   _  ds Taut False = UpdateFailure ds
updateMap (DMap cs) pre ds a bool
  = case Map.lookup pre cs of
       Nothing            -> UpdateSuccess $ DMap $ Map.insert pre (Map.singleton a (bool,ds)) cs
       Just slot          -> case updateClashableInfoSlot slot a bool ds of
                              Slot_UpdateSuccess updatedSlot -> UpdateSuccess $ DMap $ Map.insert pre updatedSlot cs
                              Slot_UpdateFailure failureDeps -> UpdateFailure failureDeps


type Clashable_info_slot = Map.Map Atom (Bool,DependencySet)
data Slot_UpdateResult =   Slot_UpdateSuccess Clashable_info_slot
                         | Slot_UpdateFailure DependencySet


-- Union a list of clashable info slots
clashableInfoSlotsUnions :: [Clashable_info_slot] -> Slot_UpdateResult
clashableInfoSlotsUnions []              = Slot_UpdateSuccess (Map.empty::Clashable_info_slot)
clashableInfoSlotsUnions [cis]           = Slot_UpdateSuccess cis
clashableInfoSlotsUnions (cis1:cis2:tl)
 = case unionClashableInfoSlots cis1 cis2 of
     failure@(Slot_UpdateFailure _) -> failure
     Slot_UpdateSuccess newCis      -> clashableInfoSlotsUnions (newCis:tl)

-- Union two clashable info slots

-- if there is a clash, the result reports the set of dependencies whose earliest dependency is the earliest
-- among all dependencies sets that caused the clash
unionClashableInfoSlots :: Clashable_info_slot -> Clashable_info_slot -> Slot_UpdateResult
unionClashableInfoSlots cis1 cis2
 = ucis_helper cis1 (Map.assocs cis2)
    where ucis_helper :: Clashable_info_slot -> [(Atom,(Bool,DependencySet))] -> Slot_UpdateResult
          ucis_helper cis a_b_ds_s =
             let (updateStatus,clashing_ds_s)
                  = foldr (\(a,(bool,ds)) (upResult,clashingBps_s)
                           -> case upResult of
                               Slot_UpdateSuccess cis_ ->  (updateClashableInfoSlot cis_ a bool ds, clashingBps_s     )
                               Slot_UpdateFailure ds_s ->  (updateClashableInfoSlot cis a bool ds, ds_s:clashingBps_s)  -- we reuse the input Clashabe Info Slot
                          )
                          (Slot_UpdateSuccess cis,[])   a_b_ds_s
                 result = case clashing_ds_s of
                              []   -> updateStatus                                    -- is 'success'
                              ds_s -> Slot_UpdateFailure $ findEarliestSet ds_s
                                         where findEarliestSet ds_s_ = minimumBy compareBPSets ds_s_
                                               compareBPSets ds1 ds2 = compare (dsMin ds1) (dsMin ds2)
             in
                result


-- Insert a piece of information in a clashable info slot

updateClashableInfoSlot :: Clashable_info_slot -> Atom -> Bool -> DependencySet -> Slot_UpdateResult
updateClashableInfoSlot cis Taut True  _  = Slot_UpdateSuccess cis
updateClashableInfoSlot  _  Taut False ds = Slot_UpdateFailure ds
updateClashableInfoSlot cis a             bool  ds  -- nominals, propositional symbols
 = case Map.lookup a cis of
    Nothing          -> Slot_UpdateSuccess $ Map.insert a (bool,ds) cis
    Just (bool2,ds2) -> if bool == bool2
                         then Slot_UpdateSuccess $ Map.insert a (bool,dsToKeep) cis
                         else Slot_UpdateFailure $ dsUnion ds ds2
                           where dsToKeep = if dsMin ds2 < dsMin ds then ds2 else ds
                                  -- if the same information is caused by an earlier
                                  -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

addDepsToClashableSlot :: DependencySet -> Slot_UpdateResult -> Slot_UpdateResult
addDepsToClashableSlot ds res_cis =
 case res_cis of
  Slot_UpdateSuccess cis         ->  Slot_UpdateSuccess $ Map.map (\(a,currentDs) -> (a,dsUnion currentDs ds)) cis
  failure@(Slot_UpdateFailure _) -> failure



queryClashableSlot :: Branch -> Prefix -> Literal -> Maybe (Bool,DependencySet)
-- Output : Nothing = nevermind ; Just True = already there ; Just False = contrary there
queryClashableSlot _ _ (PosLit Taut) = Just (True,dsEmpty)
queryClashableSlot _ _ (NegLit Taut) = Just (False,dsEmpty)
queryClashableSlot br pr (NegLit a)
  = case DMap.lookup pr a (clashStr br) of
      Nothing           -> Nothing
      Just (bool,ds)    -> Just (not bool,ds)
queryClashableSlot br pr (PosLit a)
  = case DMap.lookup pr a (clashStr br) of
      Nothing           -> Nothing
      Just (bool,ds)    -> Just (bool,ds)


{-     function used for unit propagation     -}

data ReducedDisjunct = Triviality | Contradiction DependencySet | Reduced DependencySet (Set Formula)

reduceDisjunctionAgainstBranch :: Branch -> Prefix -> Set Formula -> ReducedDisjunct
reduceDisjunctionAgainstBranch br pr fs =
         case foldr scanDisjunctAndTest (Just ( Set.empty , dsEmpty )) (list fs) of
          Nothing                      ->  Triviality
          Just  (  disjuncts , ds ) | Set.null disjuncts -> Contradiction ds
                                    | otherwise          -> Reduced       ds disjuncts

         where -- for each removed literal of the disjunction, we have to add the dependencies of the literal that got it removed to the re-created formula
               -- and if the recreated formula is empty, then there is a clash, with all the branching dependencies
               -- if the formula is "trivial" (= one disjunct is already there) we just remove the formula, i guess...
           ur = getUrfather br (DS.Prefix pr)
           scanDisjunctAndTest :: Formula -> Maybe (Set Formula,DependencySet) -> Maybe (Set Formula,DependencySet)
           scanDisjunctAndTest       _                Nothing               =    Nothing
           scanDisjunctAndTest  l@(Lit current) (Just (disjuncts,ds_))    =
             case queryClashableSlot br ur current of
                Nothing          -> Just (Set.insert l disjuncts,ds_)
                Just (True,_)    -> Nothing
                Just (False,ds2) -> Just (disjuncts,dsUnion ds_ ds2)
           scanDisjunctAndTest       f          (Just (disjuncts,ds_))    =    Just (Set.insert f disjuncts,ds_)


{-     other functions     -}
blockChain :: Branch -> Branch
blockChain br = br{blockMode = ChainBlocking}

hasTransClos :: Branch -> Bool
hasTransClos br = languageTrans $ inputLanguage br

prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]

hasProperty :: RelInfo -> RelSymbol -> RelProperties -> Bool
hasProperty relI r p = case List.lookup r relI of
                        Nothing         -> False
                        Just properties -> p `elem` properties

isReflexive :: RelInfo -> RelSymbol -> Bool
isReflexive relI r = hasProperty relI r Reflexive

isSymmetric :: RelInfo -> RelSymbol -> Bool
isSymmetric relI r = hasProperty relI r Symmetric

isTransitive :: RelInfo -> RelSymbol -> Bool
isTransitive relI r = hasProperty relI r Transitive

isFunctional :: RelInfo -> Rel -> Bool
isFunctional relI r = hasProperty relI (RelSymbol r) Functional

isInjective :: RelInfo -> Rel -> Bool
isInjective relI r = hasProperty relI (RelSymbol r) Injective

{-      Monad related stuff      -}

data BranchData = BranchData { branch_info :: BranchInfo,
                               branch_clp :: CmdLineParams,
                               branch_path :: [Int],
                               timeout_signal :: TimeoutSignal,
                               ------unsat cache info-------
                               unsat_cache :: UCache,
                               disjunctPrefixes::DisjunctPrefixes}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

addZeroInPath :: BranchData -> BranchData
addZeroInPath bd = bd{branch_path=(0:(branch_path bd))}

incPathHead :: BranchData -> BranchData
incPathHead bd = bd{branch_path=(( head (branch_path bd) + 1 ):(tail $ branch_path bd))}

-- 

getAllParents_without_urfather :: Branch -> Prefix -> [Prefix]
getAllParents_without_urfather br pr = (pr:rest)
       where rest = case Map.lookup pr (prefParent br) of
                      Nothing     -> []
                      Just parent -> getAllParents_without_urfather br parent
                               


search_disjunctPrefixes :: Prefix -> DisjunctPrefixes  -> Bool
search_disjunctPrefixes  p plist = any (\(_,pd) -> p==pd) plist
-- search_disjunctPrefixes br p ((_,pd):t) = if (p == pd)
--                                               then True
--                                               else search_disjunctPrefixes br p t


test_level :: Int -> (Int,Prefix) -> Bool
test_level cur_lev (lev, _) = cur_lev >= lev

del_level_disjunctPrefixes :: Int -> DisjunctPrefixes  -> DisjunctPrefixes  
del_level_disjunctPrefixes lev list_p = filter (test_level lev) list_p

-- test_prefix_acc ::  [Prefix] -> (Int,Prefix) -> Bool
-- test_prefix_acc all_parents (_,p) = 
--             elem p all_parents -- check if the urfather of the ancestor is in the list of all parents.


                       
del_pref_disjunctPrefixes :: Branch -> Prefix -> DisjunctPrefixes -> DisjunctPrefixes 
del_pref_disjunctPrefixes br pr_clash disjunctPrefixes_list = 
                    let all_parents =  (getAllParents_without_urfather br pr_clash )
                    in  filter (\(_,pd) -> (elem pd all_parents)) disjunctPrefixes_list
                    
--                     in  filter (test_prefix_acc all_parents) disjunctPrefixes_list






-----------------------------------------------------------------------
---------------------------debugging----------------------------------
-----------------------------------------------------------------------

-- debug :: Show a => a -> a
-- debug x = trace (show x) x
