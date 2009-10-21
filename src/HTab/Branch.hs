{-# OPTIONS_GHC -fglasgow-exts #-}

----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module HTab.Branch
(
Branch(..), BranchMonad, createNewProp, createNewPref, createNewNomTestRelevance, BranchInfo(..),
addFormulas, addFormula, addAccFormula,
addDiaRuleCheck, addDiaXRuleCheck, addDownRuleCheck, addDiffRuleCheck,
addParentPrefix, addFirstFormulas,
updateUBBookKeep, ScheduledRule(..), TodoList(..),
BranchData(..), getBranch,
emptyBranch,initialBranchStateFor,prefixes,
reduceDisjunctionAgainstBranch, merge,
getUrfather, getUrfatherAndDeps, isInTheModel, relationIsInTheModel,
getModelRepresentative, isNotBlocked,
calculateStepInfo, BlockingMode(..), diaAlreadyDone, diaXAlreadyDone,
downAlreadyDone, incPropSymbol, incNomSymbol,
UCache(..),CacheStructure(..),
Univ_constraints,AugmentedPrefixes,UCMap,TrueForms,initUnsatCache,setPrevPref,
unfulfilledEventualities, ReducedDisjunct(..), newNomBaseName, newPropBaseName, getUnappliedUBPairs,
isReflexive, isSymmetric, isTransitive,
delNonAncestors, del_level_disjunctPrefixes, search_disjunctPrefixes,DisjunctPrefixes,
deleteUEV, insertUEV_addFormula
) where

import Control.Monad.State(StateT, MonadState)
import Data.List(minimumBy)
import Data.Char ( isNumber )

import HTab.UCList ( UCList )
import qualified HTab.UCList as UCList
import HTab.UCTrie ( UCTrie )
import qualified HTab.UCTrie as UCTrie

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
                        successors, predecessors, incomingLinks, outgoingLinks)
import qualified HTab.Relations as Relations
import qualified Data.Bimap as Bimap

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
type Merge_structure  = Set.Set (DependencySet, Prefix, DS.Pointer)
type Box_constraints  = DMap Prefix Rel [(DependencySet,Formula)]

type Dia_rule_chart    = Map.Map Prefix (Set.Set Formula)
type DiaX_rule_chart   = Map.Map Prefix (Set.Set (RelSymbol,Formula))
type BoxX_rule_chart   = Map.Map Prefix (Set.Set Formula)
type Down_rule_chart   = Map.Map Prefix (Set.Set Formula)
type At_rule_chart     = Set.Set Formula
type Exist_rule_chart  = Set.Set Formula
type Diff_Dia_rule_chart  = Map.Map Formula (PropSymbol,Bool)
       -- maps D(phi) formulas to the prop symbol used to differentiate
       -- the current prefix from the one used to contain (phi) , and to a boolean indicating if a second
       -- different world has already been created
type DownVarRelevant_chart = Map.Map Formula Bool

type Univ_constraints  = [(DependencySet,Formula)]

type PrefToFormulas   = Map.Map Prefix (Set.Set Formula)
type PrefToDepSet     = Map.Map Prefix DependencySet
type Eventualities    = Map.Map Int DependencySet

type EquivClasses = DS.DisjSet DS.Pointer
type InclusionUrfathersMap = Map.Map Prefix Prefix

type AugmentedPrefixes = [Prefix] -- list of prefixes whose label is modified during the current step of the algorithm

type PrevPrefixes = [Prefix] --To keep the prefixes true at b-b1, where b is the current branch, and b1 is prev(b)


type PrefixParent = Map.Map Prefix Prefix

data BlockingMode = InclusionBlockingGlobal | InclusionBlockingChain | ChainBlocking
 deriving (Eq,Show)


type TrueForms = DMap Prefix Formula DependencySet

data Branch = Branch {clashStr :: Clashable_info,
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- immediate rules constraints
                  boxConstrFwd :: Box_constraints,
                  boxConstrBwd :: Box_constraints,
                      univCons :: Univ_constraints,
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
                     trueForms :: TrueForms,
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
                 eventualities :: Eventualities,
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
                  univCons=[],
                  lastPref = 0,
                  lastNom  = Nothing,
                  lastProp = Nothing,
                  prefToForms= Map.empty::PrefToFormulas,
                  trueForms=DMap.empty :: TrueForms,
                  prToDepSet= Map.empty::PrefToDepSet,
                  eventualities = Map.empty::Eventualities,
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
 where blockingMode =
         if    languagePast fLang
            || languageTrans fLang
            || languageDown fLang
            || relInfo_ `oneIs` Symmetric
            || relInfo_ `oneIs` Functional
            || relInfo_ `oneIs` Injective
           then ChainBlocking
           else if inclBlockChain clp && (not $ inclBlockGlobal clp)
                 then InclusionBlockingChain
                 else InclusionBlockingGlobal

instance Show Branch where
 show br
  = concat [  "Input language: ", show (inputLanguage br),
              "\nClashable formulas:", showMap (\v -> "(" ++ showMap_lits v ++ ")") "\n " (toMap $ clashStr br),
              "\n", show (todoList br),
              showl "\nRelations: "       (accStr br),
              ifNotEmpty (boxConstrFwd br)
                         (\c -> "\nBox fwd: " ++ showMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap c)),
              ifNotEmpty (boxConstrBwd br)
                         (\c -> "\nBox bwd: " ++ showMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap c)),
              showl "\nDia rule chart: "  (diaRlCh br),
              showl "\nDown rule chart: " (downRlCh br),
              showl "\n@ rule chart: "     (list $ atRlCh br),
              showl "\nExist rule chart: " (list $ existRlCh br),
              showl "\nDiff dia rule chart: "   (dDiaRlCh br),
              showl "\nDown var relevant chart: " (downVarRelevantCh br),
              "\nUnrestricted blocking book-keep:", show (bookKeepUB br), ", ",
              showl "\nUniv constraints: " (univCons br),
              ifNotEmpty (prToDepSet br) (\m -> "\nPrefix to dependency set:" ++ showMap  dsShow "\n " m),
              ifNotEmpty (prefToForms br) (\m -> "\nPrefix to formulas:"       ++ showMap  (show . Set.toList) "\n " m),
              showl "\nEventualities: "  (eventualities br),
              ifNotEmpty (trueForms br) (\m -> "\nTrue formulas: " ++ show (DMap.flatten m)),
              showl "\nParent: " (prefParent br),
              "\nInclusion urfather map: ", show (inclUrMap br),
              "\nIncreased prefixes: ", show (incrPrs br),
              "\nPrefixes in (current branch - prev(current branch): ", show (prevPref br),
              "\nBlocking mode: ", show (blockMode br),
              "\nPrefix-Nominal classes : ", showMap show ", " (nomPrefClasses br),
              showl "\nModel-relevant nominals : " (list $ relevantNominals br)
           ]
              where
                  ifNotEmpty b f = if empty b then "" else f b
                  showl intro b  = if empty b then "" else intro ++ show b
                  str True = "" ; str False = "!"

                  showMap vShow sep = foldWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) ""
                  showMap_lits = foldWithKey (\a (b,d) -> (++ str b ++ show a ++ " " ++ dsShow d  ++ ", ")) ""
                  showMap_rel = foldWithKey (\r dxs -> (++ "-" ++ r ++ "-> " ++ show dxs ++ ", ")) ""

class Emptyable a where
 empty :: a -> Bool

instance Emptyable [a] where
 empty [] = True
 empty _  = False

instance Emptyable (Map a b) where
 empty = Map.null

instance Emptyable (DMap a b c) where
 empty (DMap m) = Map.null m

instance Emptyable Relations where
 empty = Relations.null

instance Emptyable (Set a) where
 empty = Set.null


data TodoList =  Unfair{conjStr :: Conj_structure,
                        disjStr :: Disj_structure,
                         diaStr :: Dia_structure,
                        diaXStr :: DiaX_structure,
                       existStr :: Exist_structure,
                          atStr :: At_structure,
                        downStr :: Down_structure,
                        diffStr :: Diff_structure,
                       mergeStr :: Merge_structure }
               | Fair [ScheduledRule]

instance Show TodoList where
 show (Fair srs) = "Todo list: " ++ show srs
 show (Unfair conjs disjs dias diaxs es ars downs diffs merges)
   = "Todo lists:" ++ concatMap (\el -> "\n" ++ show (list el)) [conjs, disjs, dias, diaxs, es, ars, downs, diffs]
                   ++ "\n" ++ show (list merges)

data ScheduledRule =   SR_Formula PrFormula
                     | SR_UBlocking Prefix Prefix
                     | SR_Merge Prefix DS.Pointer DependencySet

instance Show ScheduledRule where
 show (SR_Formula pf)    = show pf
 show (SR_UBlocking i j) = "SR " ++ show (i,j)
 show (SR_Merge pr po _) = "SR Merge" ++ show (pr,po)

emptyTodoList :: CmdLineParams -> TodoList
emptyTodoList clp =
 if fairStrategy clp
   then Fair []
   else Unfair {
                  conjStr= Set.empty::Conj_structure,
                  disjStr= Set.empty::Disj_structure,
                  diaStr = Set.empty::Dia_structure,
                  diaXStr = Set.empty::DiaX_structure,
                  existStr = Set.empty::Exist_structure,
                  atStr = Set.empty::At_structure,
                  downStr = Set.empty::Down_structure,
                  diffStr = Set.empty::Diff_structure,
                  mergeStr = Set.empty::Merge_structure
               }

{-
   "add formula" functions, that handle
   prefixes, nominals, and vId rule
-}

addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas clp br fs =
 foldr (\f bi ->
          case bi of
           BranchOK br2 -> addFormula clp br2 f
           clash -> clash
       )
       (BranchOK br)
       fs

-- 2 main cases : adding a positive nominal, and otherwise.
addFormula :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula clp br_ pf_
 =   addFormulaPutAway        pf clp
   $ addFormulaBookKeep clp pf br
  where
   (br, pf) = vId br_ pf_

addFormulaBookKeep :: CmdLineParams -> PrFormula -> Branch -> Branch
addFormulaBookKeep clp pf@(PrFormula pr _ _) br
 =   addToAugmentedPrefixes   pr
   $ addToPrefToForms         pf
   $ addToTrueForms       clp pf br

addFormulaPutAway :: PrFormula -> CmdLineParams -> Branch -> BranchInfo
addFormulaPutAway pf@(PrFormula pr ds f2) clp br =
 case f2 of
   Con fs     -> addFormulas clp br (prefix pr ds fs)
   Dis _      -> addToTodo pf br
   Dia _ _    -> addToTodo pf br
   DiaX _ _ _ -> addToTodo pf br
   Box r f    -> addBoxConstraint      pr r f ds clp br
   BoxX r f   -> addBoxXConstraint     pr r f ds clp br
   A f        -> addUnivConstraint          f ds clp br
   B f        -> b_rule                pr   f ds clp br
   E _        -> addToTodo pf br
   D _        -> addToTodo pf br
   At _ _     -> addToTodo pf br
   Down _ _   -> addToTodo pf br
   Lit l@(PosLit (N _)) -> let BranchOK br_ = addToTodo pf br
                           in addAndUpdateMap pr ds l br_
   Lit l                -> addAndUpdateMap pr ds l br

{- todo list functions -}

addToTodo :: PrFormula -> Branch -> BranchInfo
addToTodo pf@(PrFormula p ds f2) br =
 BranchOK $
  if alreadyDone
   then br
   else brWithSaturation{todoList = newTodoList}
  where
   newTodoList =
     case todoList br of
      Fair srs -> Fair (srs ++ [SR_Formula pf])
      utodo    ->
       case f2 of
         Dis _      -> utodo{disjStr  = Set.insert pf (disjStr utodo)}
         Dia _ _    -> utodo{diaStr   = Set.insert pf (diaStr utodo)}
         DiaX _ _ _ -> utodo{diaXStr  = Set.insert pf (diaXStr utodo)}
         E _        -> utodo{existStr = Set.insert pf (existStr utodo)}
         D _        -> utodo{diffStr  = Set.insert pf (diffStr utodo)}
         At _ _     -> utodo{atStr    = Set.insert pf (atStr utodo)}
         Down _ _   -> utodo{downStr  = Set.insert pf (downStr utodo)}
         Lit (PosLit (N (NomSymbol n))) -> utodo{mergeStr   = Set.insert (ds,p,(DS.Nominal n)) (mergeStr utodo)}
         _          -> error "addToTodo"
   alreadyDone =
    case f2 of
     E  _       -> existAlreadyDone br f2
     D _        -> False
     At _ _     -> atAlreadyDone br f2
     Down _ _   -> downAlreadyDone br pf
     Dia  _ _   -> diaAlreadyDone br pf
     DiaX _ r ev-> diaXAlreadyDone br p (r,ev)
     Dis _      -> False
     Lit (PosLit (N n)) -> inSameClass br p n
     _          -> error "alreadyDone"
   brWithSaturation =
    case f2 of
     E _         -> br{existRlCh = Set.insert f2 (existRlCh br)}
     At _ _      -> br{atRlCh    = Set.insert f2 (atRlCh br)}
     DiaX _ r g  -> addDiaXRuleCheck br p (r,g)
     -- do-nothing cases
     Dis _       -> br
     D _         -> br
     Down _ _    -> br
     Dia _ _     -> br
     Lit _       -> br
     -- error cases
     _           -> error "writeSaturation"

{-    helper functions for equivalence class merge     -}

merge :: CmdLineParams -> Branch -> Prefix -> DependencySet -> DS.Pointer -> BranchInfo
merge clp br pr fDs pointer -- pointer is a nominal or a prefix
 = let
       (DS.Prefix ur1,classes1) = DS.find  (DS.Prefix pr) (nomPrefClasses br)
       (poAncestor   ,classes2) = DS.find  pointer classes1
       classes3                 = DS.union (DS.Prefix pr) pointer classes2
   in
    case poAncestor of
     DS.Nominal _     -> BranchOK $ addClassDeps ur1 fDs $ br { nomPrefClasses = classes3 }
                         -- nominal not yet in the equivalence classes
     DS.Prefix ur2
       | ur1 == ur2   -> BranchOK $ addClassDeps ur1 fDs br
       | otherwise
          ->
            let
               oldUr                    = max ur1 ur2
               newUr                    = min ur1 ur2
               clashableInfoSlots       = catMaybes $ map (\ur -> DMap.lookup1 ur (clashStr br))  [ur1,ur2]
               currentDependencies      = dsUnions $ fDs:(map (findDeps br) [ur1,ur2])
               newPrToDepSet            = Map.insert newUr currentDependencies (prToDepSet br)
               newClashableSlotUrfather = cisAddDeps currentDependencies $ cisUnions clashableInfoSlots
            in
             case newClashableSlotUrfather of
              Slot_UpdateFailure clashingDeps ->
                  let newBr = br{nomPrefClasses = classes3} in
                  BranchClash newBr pr (dsUnion clashingDeps currentDependencies) (neg taut) -- TODO not ideal

              Slot_UpdateSuccess urfatherSlot ->
                  let newClashStr     = DMap $ Map.delete oldUr $ Map.insert newUr urfatherSlot (toMap $ clashStr br)

                      -- structures that merge
                      newPrefToForms  = moveInMap (prefToForms br) oldUr newUr Set.union
                      newBoxConstrFwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrFwd br) oldUr newUr
                      newBoxConstrBwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrBwd br) oldUr newUr
                      newAccStr       = mergePrefixWith (accStr br) oldUr newUr fDs
                      newTrueForms    = DMap.moveInnerDataDMap (trueForms br) oldUr newUr dsUnion
                      newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
                      newDiaXRlCh     = moveInMap (diaXRlCh br) oldUr newUr Set.union
                      newBoxXRlCh     = moveInMap (boxXRlCh br) oldUr newUr Set.union

                      -- structures that combine
                      mapBoxFwd = map (\idx -> Map.findWithDefault Map.empty idx (toMap $ boxConstrFwd br) ) [ur1,ur2]
                      mapAccFwd = map (Map.fromList . (outgoingLinks (accStr br))) [ur1,ur2]
                      formulasToSend1 = concatMap (boxRule fDs) $ almostCartesianProduct mapBoxFwd mapAccFwd

                      mapBoxBwd = map (\idx -> Map.findWithDefault Map.empty idx (toMap $ boxConstrBwd br) ) [ur1,ur2]
                      mapAccBwd = map (Map.fromList . (incomingLinks (accStr br))) [ur1,ur2]
                      formulasToSend2 = concatMap (boxRule fDs) $ almostCartesianProduct mapBoxBwd mapAccBwd

                      funNomsToSend = addFNom $ filter ((isFunctional (relInfo br)) . fst) $ outgoingLinks (accStr br) oldUr
                       where addFNom :: [(Rel, [(Prefix,DependencySet)])] -> [PrFormula]
                             addFNom = concatMap (\(r,pds) ->
                                                    map (\(p,ds) -> PrFormula p (dsUnion ds fDs) (funcNominal r newUr)) pds
                                                 )
                      injNomsToSend  = addINom $ filter ((isInjective (relInfo br)) . fst) $ incomingLinks (accStr br) oldUr
                       where addINom :: [(Rel, [(Prefix,DependencySet)])] -> [PrFormula]
                             addINom = concatMap (\(r,pds) ->
                                                    map (\(p,ds) -> PrFormula p (dsUnion ds fDs) (injNominal r newUr)) pds
                                                 )

                      formulasToAdd   = nubAndMergeDeps $     formulasToSend1
                                                           ++ formulasToSend2
                                                           ++  funNomsToSend
                                                           ++  injNomsToSend

                      newBr           = br{nomPrefClasses = classes3,
                                           boxConstrFwd   = newBoxConstrFwd,
                                           boxConstrBwd   = newBoxConstrBwd,
                                           accStr         = newAccStr,
                                           prToDepSet     = newPrToDepSet,
                                           prefToForms    = newPrefToForms,
                                           trueForms      = newTrueForms,
                                           diaRlCh        = newDiaRlCh,
                                           diaXRlCh       = newDiaXRlCh,
                                           boxXRlCh       = newBoxXRlCh,
                                           clashStr       = newClashStr}
                  in
                      addFormulas clp newBr formulasToAdd

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

vId :: Branch -> PrFormula -> (Branch,PrFormula)
vId br f@(PrFormula pr ds f2)
 = (newBr, newF)
   where
     (urfather,ds2,newClasses) = getUrfatherAndDeps br (DS.Prefix pr)
     newBr = br{nomPrefClasses = newClasses}
     newF  = if urfather == pr
                 then f else PrFormula urfather (dsUnion ds ds2) f2

addToTrueForms :: CmdLineParams -> PrFormula -> Branch -> Branch
addToTrueForms clp (PrFormula pre dps f) br =
 case caching clp of
   Nothing -> br
   _       -> br{trueForms = newMap}
 where newMap = DMap.insertWith dsUnion pre f dps $ trueForms br


addToPrefToForms :: PrFormula -> Branch -> Branch
addToPrefToForms (PrFormula pr _ f) br | forInclusion br f =
  br{prefToForms = newMap}
 where currentPtf = prefToForms br
       newMap = Map.insertWith Set.union pr (Set.singleton f) currentPtf
addToPrefToForms _ br = br

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

inSameClass :: Branch -> Prefix -> NomSymbol -> Bool
inSameClass br p (NomSymbol n)
 = case fst $ DS.find (DS.Nominal n) (nomPrefClasses br) of
    DS.Nominal _ -> False
    DS.Prefix p2 -> getUrfather br (DS.Prefix p) == p2

-- <*>-related functions

deleteUEV :: Branch -> Int -> Branch
deleteUEV br idx = br{eventualities = Map.delete idx (eventualities br)}

insertUEV_addFormula :: Branch -> CmdLineParams -> (Maybe Int) -> DependencySet -> (Int -> PrFormula) -> BranchInfo
insertUEV_addFormula br clp mi ds ff
 = addFormula clp br2 f
  where idxToUse = case mi of
                    Nothing   -> case Map.maxViewWithKey $ eventualities br of
                                   Nothing        -> 0
                                   Just ((i,_),_) -> i+1
                    Just idx  -> idx
        newEvs = Map.insertWith dsUnion idxToUse ds $ eventualities br
        br2 = br{eventualities= newEvs}
        f = ff idxToUse

{-     box-related constraints     -}

boxRule :: DependencySet -> (Map.Map Rel [(DependencySet,Formula)], Map.Map Rel [(Prefix,DependencySet)]) -> [PrFormula]
boxRule deps (mapBox, mapAcc)
 = [PrFormula p (dsUnions [deps,ds1,ds2]) f |
                      r1 <- Map.keys mapBox,
                      r2 <- Map.keys mapAcc,    r1 == r2,
                      (ds1,f) <- (Map.!) mapBox r1,
                      (p,ds2) <- (Map.!) mapAcc r2     ]

addBoxConstraint :: Prefix -> RelSymbol -> Formula -> DependencySet -> CmdLineParams -> Branch -> BranchInfo
addBoxConstraint pr_ (RelSymbol r) f ds clp br
 = addFormulas clp newBr toAdd
   where pr = getUrfather br (DS.Prefix pr_)
         newBr = br{boxConstrFwd = updateBoxConstr pr r f ds (boxConstrFwd br)}
         accessiblePrDs   = successors (accStr br) pr r
         toAdd = symApplications ++ transApplications ++ boxApplications
         transApplications = if isTransitive (relInfo br) (RelSymbol r)
                             then map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) (Box (RelSymbol r) f)) accessiblePrDs
                             else []
         symApplications = if isSymmetric (relInfo br) (RelSymbol r) then [PrFormula pr ds $ box (InvRelSymbol r) f] else []
         boxApplications = map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) f) accessiblePrDs

addBoxConstraint pr_ (InvRelSymbol r) f ds clp br
 = addFormulas clp newBr toAdd
   where pr = getUrfather br (DS.Prefix pr_)
         newBr = br{boxConstrBwd = updateBoxConstr pr r f ds (boxConstrBwd br)}
         accessiblePrDs        = predecessors (accStr br) pr r
         toAdd = transApplications ++ boxApplications
         transApplications = if isTransitive (relInfo br) (RelSymbol r)
                             then map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) (Box (InvRelSymbol r) f)) accessiblePrDs
                             else []
         boxApplications = map (\(p,ds2) -> PrFormula p (dsUnion ds ds2) f) accessiblePrDs

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> Box_constraints -> Box_constraints
updateBoxConstr p1_ r_ f_ ds_ (DMap boxConstr_) =
  case Map.lookup p1_ boxConstr_ of
    Nothing       -> DMap $ Map.insert p1_ (Map.singleton r_ [(ds_,f_)]) boxConstr_
    Just innerMap ->
       case Map.lookup r_ innerMap of
        Nothing             -> DMap $ Map.insert p1_ (Map.insert r_ [(ds_,f_)] innerMap)                boxConstr_
        Just innerInnerList -> DMap $ Map.insert p1_ (Map.insert r_ ((ds_,f_):innerInnerList) innerMap) boxConstr_


-- [*]phi --> phi & [][*]phi
-- need not to do all that addBoxConstraint does
addBoxXConstraint :: Prefix -> RelSymbol -> Formula -> DependencySet -> CmdLineParams ->  Branch -> BranchInfo
addBoxXConstraint nonRepresentativePr r f ds clp br
 = if boxXAlreadyDone br pr (BoxX r f)
    then BranchOK br
    else addFormulas clp br2 [PrFormula pr ds f,
                     PrFormula pr ds (Box r (BoxX r f))]
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
 = addFormulas clp newBr toAdd
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
         toSendFwd = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p1 (toMap $ boxConstrFwd br)
         toSendBwd = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p2 (toMap $ boxConstrBwd br)

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
isInTheModel br pr | isNominalUrfather br pr
 = case blockMode br of
    InclusionBlockingGlobal ->  (getModelRepresentative br pr) == pr
    InclusionBlockingChain  ->  (getModelRepresentative br pr) == pr
    ChainBlocking           ->  case findModelRepresentativeChainBlocking br pr of
                                 Nothing   -> False
                                 Just repr -> repr == pr
isInTheModel _ _ = False

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
                      then fromScratchInclUrMap       -- this case is reached if we applied the (A) rule  -- does it happen ??
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
condFoldr _ accum    []      = accum
condFoldr f accum (hd:tl)
   = let (newAcc,continue) = f hd accum in
      if continue then condFoldr f newAcc tl else newAcc

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
forInclusion _ (DiaX _ _ _) = True
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

{-     modifications done by rule application     -}

addDiaRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDiaRuleCheck br pr f =
  br{diaRlCh=Map.insertWith Set.union ur (Set.singleton f) (diaRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaAlreadyDone :: Branch -> PrFormula -> Bool
diaAlreadyDone b (PrFormula p _ f@(Dia _ _)) =
  case Map.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ = error "dia already done : wrong formula kind"
--

addDiaXRuleCheck :: Branch -> Prefix -> (RelSymbol, Formula) -> Branch
addDiaXRuleCheck br pr f =
  br{diaXRlCh=Map.insertWith Set.union ur (Set.singleton f) (diaXRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaXAlreadyDone :: Branch -> Prefix -> (RelSymbol,Formula) -> Bool
diaXAlreadyDone b p f =
  case Map.lookup ur (diaXRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)



unfulfilledEventualities :: Branch -> Maybe DependencySet
unfulfilledEventualities br
 = if Map.null $ eventualities br
    then Nothing
    else Just $ dsUnions $ Map.elems $ eventualities br

--

addDownRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDownRuleCheck br pr f =
  br{downRlCh=Map.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

downAlreadyDone :: Branch -> PrFormula -> Bool
downAlreadyDone b (PrFormula p _ f@(Down _ _)) =
  case Map.lookup ur (downRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

downAlreadyDone _ _ = error "down already done : wrong formula kind"

--

existAlreadyDone :: Branch -> Formula -> Bool
existAlreadyDone b f@(E _) = Set.member f (existRlCh b)
existAlreadyDone _ _ = error "exist already done : wrong formula kind"

--

atAlreadyDone :: Branch -> Formula -> Bool
atAlreadyDone b f@(At _ _) = Set.member f (atRlCh b)
atAlreadyDone _ _ = error "at already done : wrong formula kind"

--

addUnivConstraint :: Formula -> DependencySet -> CmdLineParams -> Branch -> BranchInfo
addUnivConstraint f ds clp br
 = addFormulas clp newBr
               ( map (\p -> PrFormula p ds f) urfathers )
   where newBr = br{univCons = (ds,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

--

b_rule :: Prefix -> Formula -> DependencySet -> CmdLineParams -> Branch -> BranchInfo
b_rule  pr f ds clp br
 = addFormula clp br (PrFormula pr ds $ downArrow x $ univMod $ ((nom x) `disj` f))
    where x = NomSymbol "x"
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
                         ( map (\(ds,f) -> PrFormula newPr ds f) univConstraints )
   where newPr = lastPref br + 1
         newBr_ = br{lastPref = newPr}
         newBr = case todoList br of
                    Fair _ -> addUBlockingSchedule newBr_
                    _      -> newBr_
         univConstraints = univCons br
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


-- preparation of the branch at the beginning of the calculus:
--  - add the input formula at prefix 0
--  - add a nominal formula at a fresh prefix for each nominal of the input formula
addFirstFormulas :: CmdLineParams -> Branch -> Formula -> LanguageInfo -> BranchInfo
addFirstFormulas clp br_ f fLang
 = addFormula clp br3 pf
    where ns = languageNoms fLang
          nbNs = length ns
          noms = [1..nbNs]
          br =  foldr addReflexiveLinks (  br_{lastPref = nbNs} ) noms
          pf = firstPrefixedFormula f
          newClasses = foldr (\(pr,(NomSymbol n)) -> DS.union (DS.Prefix pr) (DS.Nominal n))
                             (nomPrefClasses br)
                             (zip [1..] ns)
          newClashStr = foldr (\(pr,n) -> DMap.insert pr (N n) (True,dsEmpty))
                              DMap.empty
                              (zip [1..] ns)
          br2 = br{nomPrefClasses = newClasses,
                         clashStr = newClashStr}
          br3 = foldr (\(pr,n) -> addFormulaBookKeep clp (PrFormula pr dsEmpty (nom n)))
                      br2
                      (zip [1..] ns)

initUnsatCache :: CmdLineParams -> UCache
initUnsatCache clp
 = case caching clp of
     Just TrieCaching -> UCache{ cache = emptyCache::UCTrie,
                                 bimap =emptyBimap }
     Just ListCaching -> UCache{ cache = emptyCache::UCList,
                                 bimap =emptyBimap }
     Nothing          -> UCache{ cache = emptyCache::UCList,
                                 bimap =emptyBimap }
  where  emptyBimap = Bimap.singleton (neg taut) 0

{-     functions to handle the "clashable information", ie literals associated to prefixes     -}

data UpdateResult = UpdateSuccess Clashable_info | UpdateFailure DependencySet

addAndUpdateMap :: Prefix -> DependencySet -> Literal -> Branch -> BranchInfo
addAndUpdateMap pr ds l br
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
       Just slot          -> case cisUpdate slot a bool ds of
                              Slot_UpdateSuccess updatedSlot -> UpdateSuccess $ DMap $ Map.insert pre updatedSlot cs
                              Slot_UpdateFailure failureDeps -> UpdateFailure failureDeps


type Clashable_info_slot = Map.Map Atom (Bool,DependencySet)
data Slot_UpdateResult =   Slot_UpdateSuccess Clashable_info_slot
                         | Slot_UpdateFailure DependencySet


-- Union a list of clashable info slots
cisUnions :: [Clashable_info_slot] -> Slot_UpdateResult
cisUnions []              = Slot_UpdateSuccess (Map.empty::Clashable_info_slot)
cisUnions [cis]           = Slot_UpdateSuccess cis
cisUnions (cis1:cis2:tl)
 = case cisUnion cis1 cis2 of
     failure@(Slot_UpdateFailure _) -> failure
     Slot_UpdateSuccess newCis      -> cisUnions (newCis:tl)

-- Union two clashable info slots

-- if there is a clash, the result reports the set of dependencies whose earliest dependency is the earliest
-- among all dependencies sets that caused the clash
cisUnion :: Clashable_info_slot -> Clashable_info_slot -> Slot_UpdateResult
cisUnion cis1 cis2
 = ucis_helper cis1 (Map.assocs cis2)
    where ucis_helper :: Clashable_info_slot -> [(Atom,(Bool,DependencySet))] -> Slot_UpdateResult
          ucis_helper cis a_b_ds_s =
             let (updateStatus,clashing_ds_s)
                  = foldr (\(a,(bool,ds)) (upResult,clashingBps_s)
                           -> case upResult of
                               Slot_UpdateSuccess cis_ ->  (cisUpdate cis_ a bool ds,      clashingBps_s)
                               Slot_UpdateFailure ds_s ->  (cisUpdate cis  a bool ds, ds_s:clashingBps_s)
                                                                 -- we reuse the input Clashabe Info Slot
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

cisUpdate :: Clashable_info_slot -> Atom -> Bool -> DependencySet -> Slot_UpdateResult
cisUpdate cis Taut True  _  = Slot_UpdateSuccess cis
cisUpdate  _  Taut False ds = Slot_UpdateFailure ds
cisUpdate cis a             bool  ds  -- nominals, propositional symbols
 = case Map.lookup a cis of
    Nothing          -> Slot_UpdateSuccess $ Map.insert a (bool,ds) cis
    Just (bool2,ds2) -> if bool == bool2
                         then Slot_UpdateSuccess $ Map.insert a (bool,dsToKeep) cis
                         else Slot_UpdateFailure $ dsUnion ds ds2
                           where dsToKeep = if dsMin ds2 < dsMin ds then ds2 else ds
                                  -- if the same information is caused by an earlier
                                  -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

cisAddDeps :: DependencySet -> Slot_UpdateResult -> Slot_UpdateResult
cisAddDeps ds res_cis =
 case res_cis of
  Slot_UpdateSuccess cis         ->  Slot_UpdateSuccess $ Map.map (\(a,currentDs) -> (a,dsUnion currentDs ds)) cis
  failure@(Slot_UpdateFailure _) -> failure



cisQuery :: Branch -> Prefix -> Literal -> Maybe (Bool,DependencySet)
-- Output : Nothing = nevermind ; Just True = already there ; Just False = contrary there
cisQuery _ _ (PosLit Taut) = Just (True,dsEmpty)
cisQuery _ _ (NegLit Taut) = Just (False,dsEmpty)
cisQuery br pr (NegLit a)
  = case DMap.lookup pr a (clashStr br) of
      Nothing           -> Nothing
      Just (bool,ds)    -> Just (not bool,ds)
cisQuery br pr (PosLit a)
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

         where -- for each removed literal of the disjunction, add dependencies of the removed literal
               -- if the resulting is empty -> clash
               -- if the formula is "trivial" (= one disjunct is already there) we just remove the formula
           ur = getUrfather br (DS.Prefix pr)
           scanDisjunctAndTest :: Formula -> Maybe (Set Formula,DependencySet) -> Maybe (Set Formula,DependencySet)
           scanDisjunctAndTest       _                Nothing               =    Nothing
           scanDisjunctAndTest  l@(Lit current) (Just (disjuncts,ds_))    =
             case cisQuery br ur current of
                Nothing          -> Just (Set.insert l disjuncts,ds_)
                Just (True,_)    -> Nothing
                Just (False,ds2) -> Just (disjuncts,dsUnion ds_ ds2)
           scanDisjunctAndTest       f          (Just (disjuncts,ds_))    =    Just (Set.insert f disjuncts,ds_)


{-     other functions     -}
prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]

oneIs :: RelInfo -> RelProperties -> Bool
oneIs relI p = any ( (elem p) . snd) relI

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
                               timeout_signal :: TimeoutSignal,
                               ------unsat cache info-------
                               unsat_cache :: UCache,
                               disjunctPrefixes::DisjunctPrefixes}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

-- Unsat Cache

data UCache = forall a . CacheStructure a
                => UCache { cache :: a,
                            bimap :: UCMap}

type UCMap = Bimap.Bimap Formula Int

instance Show UCache where
 show UCache{ cache = c,
              bimap = bm }
  = "UCache: " ++ show c ++ show bm

class Show a => CacheStructure a where
  emptyCache :: a
  insertCache :: Set Int -> a -> a
  queryCache :: Set Int -> a -> Maybe [Int]

instance CacheStructure UCList where
 emptyCache = []
 insertCache = UCList.update
 queryCache = UCList.superset_matching

instance CacheStructure UCTrie where
 emptyCache  = UCTrie.empty
 insertCache = UCTrie.update
 queryCache  = UCTrie.query

-- 

type DisjunctPrefixes = [(Int,Prefix)]

search_disjunctPrefixes :: Prefix -> DisjunctPrefixes  -> Bool
search_disjunctPrefixes  p = any ((==p) . snd)

del_level_disjunctPrefixes :: Int -> DisjunctPrefixes  -> DisjunctPrefixes
del_level_disjunctPrefixes lev = filter ((<=lev) . fst)

delNonAncestors :: Branch -> Prefix -> DisjunctPrefixes -> DisjunctPrefixes
delNonAncestors br pr_clash
 = filter ((`elem` ancestors) . snd)
   where ancestors = getAncestors pr_clash
         getAncestors pr = (pr:rest)
               where rest = maybe [] getAncestors $ Map.lookup pr (prefParent br)

