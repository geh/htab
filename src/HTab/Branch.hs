module HTab.Branch
(
Branch(..), BranchInfo(..), TodoList(..), BlockingMode(..),
createNewNode, createNewProp, createNewNomTestRelevance,
addFormulas, addAccFormula,
addToBlockedDias,
addDiaRuleCheck, addDownRuleCheck, addDiffRuleCheck,
addParentPrefix, addFirstFormulas,
emptyBranch,
reduceDisjunctionProposeLazy, doLazyBranching,
merge,
getUrfather, getUrfatherAndDeps,
getModelRepresentative, isNotBlocked,
diaAlreadyDone, downAlreadyDone,
ReducedDisjunct(..),
patternOf, findByPattern,
prefixes, isInTheModel, relationIsInTheModel,
isSymmetric, isTransitive
) where

import Control.Applicative ( (<$>) )
import Data.List(minimumBy)
import Data.Maybe( mapMaybe, fromMaybe )
import Data.Ord ( comparing )

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.IntMap ( IntMap)
import qualified Data.IntMap as IntMap

import qualified HTab.DisjSet as DS

import HTab.CommandLine(Params(..))

import HTab.Formula

import HTab.DMap ( DMap(..), toMap )
import qualified HTab.DMap as DMap

import HTab.Relations ( Relations(..), emptyRels, insertRelation, mergePrefixes,
                        successors, predecessors, linksFromTo )

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

type ClashableInfo      = DMap {- Prefix Literal -} DependencySet
type BoxConstraints     = DMap {- Prefix Rel -} [(Formula,DependencySet)]
type BranchingWitnesses = DMap {- Prefix Literal -} [PrFormula]
type EquivClasses = DS.DisjSet DS.Pointer
data BlockingMode = PatternBlocking | AnywhereBlocking | ChainTwinBlocking  deriving (Eq,Show)

data Branch =
              Branch {
                 -- the premodel
                      clashStr :: ClashableInfo,
                        accStr :: Relations,
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- immediate rules constraints
                  boxConstrFwd :: BoxConstraints,
                  boxConstrBwd :: BoxConstraints,
                      univCons :: [(DependencySet,Formula)],
                 -- saturation of rules
                       diaRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                      downRlCh :: IntMap {- Prefix -} (Set Formula),
                        atRlCh :: Set Formula,
                     existRlCh :: Set Formula,
                      dDiaRlCh :: Map Formula (Maybe Prop),
                 -- pattern blocking
             individualPattern :: IntMap (Set Formula),
                 -- set of formulas true at each point of the premodel
                   prefToForms :: IntMap {- Prefix -} (Set Formula),
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: IntMap {- Prefix -} DependencySet,
                 -- prefix/nominal equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       nextNom :: Nom,
                      nextProp :: Prop,
                 -- lazy branching
                   brWitnesses :: BranchingWitnesses,
                 -- caching / memoisation data
             downVarRelevantCh :: Map Formula Bool,
                 -- information about language of input formula and blocking mode
                 inputLanguage :: LanguageInfo,
                     blockMode :: BlockingMode,
                   blockedDias :: IntMap {- Prefix -} [PrFormula],
                    prefParent :: IntMap {- Prefix -} Prefix,
              relevantNominals :: Set Nom,
                       relInfo :: RelInfo,
                      encoding :: Encoding}

--

emptyBranch :: LanguageInfo -> RelInfo -> Encoding -> Params -> Branch
emptyBranch fLang relInfo_ encoding_ p =
                Branch
                { clashStr          = DMap.empty,
                  accStr            = emptyRels,
                  todoList          = emptyTodoList,
                  boxConstrBwd      = DMap.empty,
                  boxConstrFwd      = DMap.empty,
                  diaRlCh           = IntMap.empty,
                  downRlCh          = IntMap.empty,
                  atRlCh            = Set.empty,
                  existRlCh         = Set.empty,
                  dDiaRlCh          = Map.empty,
                  downVarRelevantCh = Map.empty,
                  individualPattern = IntMap.empty,
                  univCons          = [],
                  lastPref          = 0,
                  nextNom           = maxNom encoding_ + 4,
                  nextProp          = maxProp encoding_ + 4,
                  prefToForms       = IntMap.empty,
                  prToDepSet        = IntMap.empty,
                  brWitnesses       = DMap.empty,
                  nomPrefClasses    = DS.mkDSet,
                  inputLanguage     = fLang,
                  blockMode         = blockingMode,
                  blockedDias       = IntMap.empty,
                  prefParent        = IntMap.empty,
                  relevantNominals  = set $ relevantNoms fLang,
                  relInfo           = relInfo_,
                  encoding          = encoding_
                }
 where blockingMode
        | languagePast fLang || relInfo_ `oneIs` Symmetric = ChainTwinBlocking
        | patternBlocking p = PatternBlocking
        | otherwise         = AnywhereBlocking

instance Show Branch where
 show br
  = concat [  show (inputLanguage br),
              "\nClashable formulas:", showIMap (\v -> "(" ++ showMap_lits v ++ ")") "\n " (toMap $ clashStr br),
              "\n", show (todoList br),
              "\nRelations: ", show (accStr br),
              "\nBox fwd: ", showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap $ boxConstrFwd br),
              "\nBox bwd: ", showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap $ boxConstrBwd br),
              "\nWitnesses: ", showIMap (\v  -> "(" ++ showMap_lits2 v ++ ")") "\n " (toMap $ brWitnesses br),
              "\nDia rule chart: ", show (diaRlCh br),
              "\nIndividual patterns: ", show (individualPattern br),
              "\nDown rule chart: ", show (downRlCh br),
              "\n@ rule chart: ", show (list $ atRlCh br),
              "\nExist rule chart: ", show (list $ existRlCh br),
              "\nDiff dia rule chart: ", show (dDiaRlCh br),
              "\nDown var relevant chart: ", show (downVarRelevantCh br),
              "\nUniv constraints: ", show (univCons br),
              "\nPrefix to dependency set: ", showIMap  dsShow "\n " (prToDepSet br),
              "\nPrefix to formulas: ", showIMap  (show . Set.toList) "\n " (prefToForms br),
              "\nParent: ", show (prefParent br),
              "\nBlocking mode: ", show (blockMode br),
              "\nPrefix-Nominal classes : ", showMap ", " (nomPrefClasses br),
              "\nModel-relevant nominals : ", unwords $ map showLit $ list $ relevantNominals br,
              "\nlastPref : ", show (lastPref br),
              " nextnom : ", showLit (nextNom br),
              " nextprop : ", showLit (nextProp br)
           ]
              where
               showIMap :: (a -> String) -> String -> IntMap a -> String
               showIMap vShow sep = IntMap.foldWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) ""
               showMap sep        = Map.foldrWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ show v )) ""
               showMap_lits       = IntMap.foldWithKey (\l d   -> (++ showLit l ++ " " ++ dsShow d  ++ ", ")) ""
               showMap_lits2      = IntMap.foldWithKey (\l fs  -> (++ showLit l ++ " " ++ ":" ++ show fs ++ ", ")) ""
               showMap_rel        = IntMap.foldWithKey (\r dxs -> (++ "-" ++ showRel r ++ "-> " ++ show dxs ++ ", ")) ""

data TodoList= TodoList{disjTodo :: Set PrFormula,
                         diaTodo :: Set PrFormula,
                       existTodo :: Set PrFormula,
                          atTodo :: Set PrFormula,
                        downTodo :: Set PrFormula,
                        diffTodo :: Set PrFormula,
                       mergeTodo :: Set (DependencySet, Prefix, DS.Pointer),
                     roleIncTodo :: Set (DependencySet, Prefix, Prefix, [Rel]) }
 deriving Show

emptyTodoList :: TodoList
emptyTodoList =
      TodoList {  disjTodo = Set.empty,
                   diaTodo = Set.empty,
                 existTodo = Set.empty,
                    atTodo = Set.empty,
                  downTodo = Set.empty,
                  diffTodo = Set.empty,
                 mergeTodo = Set.empty,
               roleIncTodo = Set.empty
               }

{-
   "add formula" functions, that handle
   prefixes and nominals
-}

addFormulas :: Params -> [PrFormula] -> Branch -> BranchInfo
addFormulas p fs br =
 foldr (\f bi ->
          case bi of
           BranchOK br2 -> addFormula p br2 f
           clash -> clash
       )
       (BranchOK br)
       fs

addFormula :: Params -> Branch -> PrFormula -> BranchInfo
addFormula p br pf
 =   putAwayFormula  p pf
   $ bookKeepFormula p pf br

bookKeepFormula :: Params -> PrFormula -> Branch -> Branch
bookKeepFormula p pf_ br
 =   addToPrefToForms         pf
   $ rescheduleLazyBranching  p pf
   $ rescheduleBlockedDias    ur br
  where
    (ur,pf) = toUrfather br pf_

rescheduleLazyBranching :: Params -> PrFormula -> Branch -> Branch
rescheduleLazyBranching p (PrFormula pr ds (Lit l)) br   -- pr already urfather
 | lazyBranching p && isProp l
   =
     let (Just innerMap) = DMap.lookup1 pr (brWitnesses br)
     in

     case DMap.lookup pr l (brWitnesses br) of
      Just _
        -> let innerMap2 = IntMap.delete l innerMap
               newBrW = DMap.insert1 pr innerMap2 (brWitnesses br)
               newBr = br{brWitnesses = newBrW}
           in
            newBr -- forget  the disjunctions, they are really satisfied
      Nothing
       -> case DMap.lookup pr (negLit l) (brWitnesses br) of
           Just fs
             -> let innerMap2 = IntMap.delete (negLit l) innerMap
                    newBrW = DMap.insert1 pr innerMap2 (brWitnesses br)
                    newBr = br{brWitnesses = newBrW}
                in
                 foldr addToTodo newBr (map (addDeps ds) fs) --reschedule
           Nothing
            -> br -- do nothing

rescheduleLazyBranching _ _ br = br


putAwayFormula :: Params -> PrFormula -> Branch -> BranchInfo
putAwayFormula p pf@(PrFormula pr ds f2) br =
 case f2 of
   Con fs     -> addFormulas p (prefix pr ds fs) br
   Dis _      -> putAwayDisjunction p pf br
   Dia _ _    -> BranchOK $ addToTodo pf br
   Box r f    -> addBoxConstraint      pr r f ds p br
   A f        -> addUnivConstraint          f ds p br
   B f        -> bRule                pr   f ds p br
   E _        -> BranchOK $ addToTodo pf br
   D _        -> BranchOK $ addToTodo pf br
   At _ _     -> BranchOK $ addToTodo pf br
   Down _ _   -> BranchOK $ addToTodo pf br
   Lit l | isPositiveNom l -> addToClashable pr ds l $ addToTodo pf br
   Lit l                   -> addToClashable pr ds l br

putAwayDisjunction :: Params -> PrFormula -> Branch -> BranchInfo
putAwayDisjunction p pf@(PrFormula pr ds f@(Dis fs)) br
 | lazyBranching p && blockMode br /= ChainTwinBlocking
  = case reduceDisjunctionProposeLazy br pr fs of
     Contradiction dsClash -> BranchClash br pr (dsUnion ds dsClash) f
     Triviality -> BranchOK br
     Reduced new_ds disjuncts mProposed
      -> let fNew = PrFormula pr (dsUnion ds new_ds) (Dis disjuncts) --todo if there was no reduction, leave ds
         in
          case mProposed of
            Nothing -> BranchOK $ addToTodo fNew br
            Just lit -- add pr, lit, ((++) disjuncts) aux witnesses
             -> doLazyBranching ur lit [fNew] br
 | otherwise
  = BranchOK $ addToTodo pf br
 where ur = getUrfather br (DS.Prefix pr)

putAwayDisjunction _ pf _ = error ("putAwayDisjunction " ++ show pf)

-- assume the tests have been done beforehand, always returns BranchOK
doLazyBranching :: Prefix -> Literal -> [PrFormula] -> Branch -> BranchInfo
doLazyBranching pr lit pfs br
 = case DMap.lookup1 pr (brWitnesses br) of
    Nothing -> let newBrW = DMap.insert pr lit pfs (brWitnesses br)
               in BranchOK br{brWitnesses = newBrW}
    Just innerMap
     -> case IntMap.lookup lit innerMap of -- assume this is the only place where l or (negLit l) occur
         Nothing -> let newInner = IntMap.insert lit pfs innerMap
                        newBrW = DMap.insert1 pr newInner (brWitnesses br)
                    in BranchOK br{brWitnesses = newBrW}
         Just fs -- assume the test was already done
          -> let newInner = IntMap.insert lit (pfs++fs) innerMap
                 newBrW = DMap.insert1 pr newInner (brWitnesses br)
             in BranchOK br{brWitnesses = newBrW}


-- TODO
-- when doing a merge, do all the witness checks!
-- when formula is sat and doing model building, add all witnesses!

{- todo list functions -}

addToTodo :: PrFormula -> Branch -> Branch
addToTodo pf@(PrFormula p ds f2) br =
  if alreadyDone
   then br
   else brWithSaturation{todoList = newTodoList}
  where
   utodo = todoList br
   newTodoList =
       case f2 of
         Dis _              -> utodo{ disjTodo = Set.insert pf ( disjTodo utodo)}
         Dia _ _            -> utodo{  diaTodo = Set.insert pf (  diaTodo utodo)}
         E _                -> utodo{existTodo = Set.insert pf (existTodo utodo)}
         D _                -> utodo{ diffTodo = Set.insert pf ( diffTodo utodo)}
         At _ _             -> utodo{   atTodo = Set.insert pf (   atTodo utodo)}
         Down _ _           -> utodo{ downTodo = Set.insert pf ( downTodo utodo)}
         Lit l
          | isPositiveNom l -> utodo{mergeTodo = Set.insert (ds,p,DS.Nominal l) (mergeTodo utodo)}
         _                  -> error $ "addToTodo: " ++ show f2
   alreadyDone =
    case f2 of
     E  _               -> existAlreadyDone br f2
     D _                -> False
     At _ _             -> atAlreadyDone br f2
     Down _ _           -> downAlreadyDone br pf
     Dia  _ _           -> False -- the test happens later, when the todo list is processed
     Dis _              -> False -- the test happens later, when the todo list is processed
     Lit l
      | isPositiveNom l -> inSameClass br p l
     _                  -> error $ "alreadyDone: " ++ show f2
   brWithSaturation =
    case f2 of
     E _         -> br{existRlCh = Set.insert f2 (existRlCh br)}
     At _ _      -> br{atRlCh    = Set.insert f2 (atRlCh br)}
     _           -> br

rescheduleBlockedDias :: Prefix -> Branch -> Branch
rescheduleBlockedDias  pr br
 = foldr addToTodo br2 toAdd
  where toAdd =  IntMap.findWithDefault [] pr (blockedDias br)
        br2 = br{blockedDias = IntMap.delete pr $ blockedDias br}

addToBlockedDias :: PrFormula -> Branch -> BranchInfo
addToBlockedDias f@(PrFormula pr _ _) br
 = BranchOK br{blockedDias = IntMap.insertWith (++) ur [f] (blockedDias br)}
   where ur = getUrfather br (DS.Prefix pr)

{-    helper functions for equivalence class merge     -}

merge :: Params -> Prefix -> DependencySet -> DS.Pointer -> Branch -> BranchInfo
merge p pr fDs pointer br -- pointer is a nominal or a prefix
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
               clashableInfoSlots       = mapMaybe (\ur -> DMap.lookup1 ur (clashStr br))  [ur1,ur2]
               currentDeps              = dsUnions $ fDs:(map (findDeps br) [ur1,ur2])
               newPrToDepSet            = IntMap.insert newUr currentDeps (prToDepSet br)
               newClashableSlotUrfather = cisAddDeps currentDeps $ cisUnions clashableInfoSlots
            in
             case newClashableSlotUrfather of
              SlotUpdateFailure clashingDeps ->
                  let newBr = br{nomPrefClasses = classes3} in
                  BranchClash newBr pr (dsUnion clashingDeps currentDeps) (neg taut)

              SlotUpdateSuccess urfatherSlot ->
                  let newClashStr     = DMap $ IntMap.delete oldUr $ IntMap.insert newUr urfatherSlot (toMap $ clashStr br)

                      -- structures that merge
                      newPrefToForms  = moveInMap (prefToForms br) oldUr newUr Set.union
                      newBoxConstrFwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrFwd br) oldUr newUr
                      newBoxConstrBwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrBwd br) oldUr newUr
                      newAccStr       = mergePrefixes (accStr br) oldUr newUr fDs
                      newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
                      newBlockedDias  = moveInMap (blockedDias br) oldUr newUr (++)
                      (newBrWitnesses,unwitnessedToAdd) = mergeWitnesses oldUr newUr urfatherSlot (brWitnesses br)

                      -- structures that combine
                      mapBoxFwd = map (\idx -> IntMap.findWithDefault IntMap.empty idx (toMap $ boxConstrFwd br) ) [ur1,ur2]
                      mapAccFwd = map (successors (accStr br)) [ur1,ur2]
                      formulasToSend1 = concatMap (boxRule currentDeps) $ almostCartesianProduct mapBoxFwd mapAccFwd

                      mapBoxBwd = map (\idx -> IntMap.findWithDefault IntMap.empty idx (toMap $ boxConstrBwd br) ) [ur1,ur2]
                      mapAccBwd = map (predecessors (accStr br)) [ur1,ur2]
                      formulasToSend2 = concatMap (boxRule currentDeps) $ almostCartesianProduct mapBoxBwd mapAccBwd

                      formulasToAdd   = nubAndMergeDeps $     formulasToSend1
                                                           ++ formulasToSend2
                                                           ++ unwitnessedToAdd

                      newBr           = br{nomPrefClasses = classes3,
                                           boxConstrFwd   = newBoxConstrFwd,
                                           boxConstrBwd   = newBoxConstrBwd,
                                           accStr         = newAccStr,
                                           prToDepSet     = newPrToDepSet,
                                           prefToForms    = newPrefToForms,
                                           diaRlCh        = newDiaRlCh,
                                           blockedDias    = newBlockedDias,
                                           clashStr       = newClashStr,
                                           brWitnesses    = newBrWitnesses}
                  in
                      addFormulas p formulasToAdd newBr

mergeWitnesses :: Prefix -> Prefix -> ClashableInfoSlot -> BranchingWitnesses -> (BranchingWitnesses, [PrFormula])
mergeWitnesses oldUr newUr urfatherSlot dbrWits@(DMap brWits)
 =( DMap.insert1 newUr newDest2 ( DMap.delete oldUr dbrWits ), toAdd1 ++ toAdd2 )
  where
   srcInnerMap  = IntMap.findWithDefault IntMap.empty oldUr brWits
   destInnerMap = IntMap.findWithDefault IntMap.empty newUr brWits
   (newDest1,toAdd1) = mergeWitnessesWitnessesMap srcInnerMap destInnerMap
   (newDest2,toAdd2) = mergeWitnessesAgainstClashable newDest1 urfatherSlot

mergeWitnessesWitnessesMap :: IntMap [PrFormula] -> IntMap [PrFormula] -> (IntMap [PrFormula], [PrFormula])
mergeWitnessesWitnessesMap srcWitMap destWitMap
 = foldr go (destWitMap,[]) $ IntMap.assocs srcWitMap
   where
      go (l,fs) (destMap,toAddAgain)
         = case IntMap.lookup l destMap of
            Just fs2 -> (IntMap.insert l (fs2++fs) destMap, toAddAgain)
            Nothing
             -> case IntMap.lookup (negLit l) destMap of -- (negLit l) is just one bit away from l in the map, but we don't use it
                  Just fs2 -> (IntMap.delete (negLit l) destMap, fs++fs2++toAddAgain)
                  Nothing ->  (IntMap.insert l fs destMap, toAddAgain)

mergeWitnessesAgainstClashable :: IntMap [PrFormula] -> ClashableInfoSlot -> (IntMap [PrFormula],[PrFormula])
mergeWitnessesAgainstClashable  witMap cis
 = foldr go (witMap,[]) $ IntMap.assocs witMap
   where
    go (lit,fs) (destMap,toAddAgain)
      | lit `IntMap.member` cis = (IntMap.delete lit destMap,toAddAgain)
      | negLit lit `IntMap.member` cis = (IntMap.delete lit destMap,fs++toAddAgain) -- same remark as above
      | otherwise = (destMap,toAddAgain)

nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added to a branch
-- as several prefixed formulas with different branching dependencies. This functions takes
-- a list of prefixes formulas, looks which inner formulas are the same and merge their
-- branching dependencies.
nubAndMergeDeps prfs =  namd prfs (Map.empty::Map (Prefix,Formula) DependencySet)

namd :: [PrFormula] -> Map (Prefix,Formula) DependencySet -> [PrFormula]
namd ((PrFormula p ds f):prfs) theMap =
  namd prfs (Map.insertWith dsUnion (p,f) ds theMap)

namd [] theMap = map (\((p,f),ds) -> PrFormula p ds f) (Map.assocs theMap)

{-
   Functions related to nom, prefixes and nominals ...
-}

toUrfather :: Branch -> PrFormula -> (Prefix,PrFormula)
toUrfather br f@(PrFormula pr ds f2)
 = (urfather, newF)
   where
     (urfather,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
     newF  = if urfather == pr
                 then f else PrFormula urfather (dsUnion ds ds2) f2

addToPrefToForms :: PrFormula -> Branch -> Branch
addToPrefToForms (PrFormula pr _ f) br
 | blockMode br == PatternBlocking = br
 | forInclusion br f               = br{prefToForms = newMap}
 | otherwise                       = br
 where currentPtf = prefToForms br
       newMap = IntMap.insertWith Set.union pr (Set.singleton f) currentPtf

{-     handling nominal urfathers, equivalence classes and dependencies     -}

isNominalUrfather :: Branch -> Prefix -> Bool
isNominalUrfather b p = DS.isRoot (DS.Prefix p) classes
                         where classes = nomPrefClasses b


-- May look redundant with getUrfatherAndDeps, but it is important not
-- to make the test isRoot for performance
getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather br p =
    ur
  where
        (DS.Prefix ur) = DS.onlyFind p (nomPrefClasses br)

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
findDeps br pr = IntMap.findWithDefault dsEmpty pr (prToDepSet br)

addClassDeps :: Prefix -> DependencySet -> Branch -> Branch
addClassDeps pr ds br = br { prToDepSet = IntMap.insertWith dsUnion pr ds (prToDepSet br) }

inSameClass :: Branch -> Prefix -> Int -> Bool
inSameClass br p n
 = case fst $ DS.find (DS.Nominal (atom n)) (nomPrefClasses br) of
    DS.Nominal _ -> False
    DS.Prefix p2 -> getUrfather br (DS.Prefix p) == p2

{-     box-related constraints     -}

boxRule :: DependencySet -> (IntMap {- Rel -} [(Formula,DependencySet)], IntMap {- Rel -} [(Prefix,DependencySet)]) -> [PrFormula]
boxRule deps (mapBox, mapAcc)
 = [PrFormula p (dsUnions [deps,ds1,ds2]) f |
                      r1 <- IntMap.keys mapBox,
                      r2 <- IntMap.keys mapAcc,
                      r1 == r2,
                      (f,ds1) <- (IntMap.!) mapBox r1,
                      (p,ds2) <- (IntMap.!) mapAcc r2     ]

addBoxConstraint :: Prefix -> Rel -> Formula -> DependencySet -> Params -> Branch -> BranchInfo
addBoxConstraint pr_ r f ds p br
 | boxAlreadyDone br pr (r,f) = BranchOK br
 | isForward r
    = let    newBr = br{boxConstrFwd = updateBoxConstr pr r f ds (boxConstrFwd br)}
             accessiblePrDs   = IntMap.findWithDefault [] r $ successors (accStr br) pr
             toAdd = symApplications ++ transApplications ++ boxApplications
             transApplications = if isTransitive (relInfo br) r
                                 then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) accessiblePrDs
                                 else []
             symApplications = [PrFormula pr ds $ Box (invRel r) f | isSymmetric (relInfo br) r]
             boxApplications = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) accessiblePrDs
    -- todo check again with new pattern, create successor if new pattern not realized
      in
         addFormulas p toAdd newBr

 | otherwise
   = let    newBr = br{boxConstrBwd = updateBoxConstr pr (atom r) f ds (boxConstrBwd br)}
            accessiblePrDs          = IntMap.findWithDefault [] (atom r) $ predecessors (accStr br) pr
            toAdd = transApplications ++ boxApplications -- no symApplications cause inv rewritten as forward during parsing
            transApplications = if isTransitive (relInfo br) (atom r)
                                then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) accessiblePrDs
                                else []
            boxApplications = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) accessiblePrDs
     in
        addFormulas p toAdd newBr
 where pr = getUrfather br (DS.Prefix pr_)

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> BoxConstraints -> BoxConstraints
updateBoxConstr p1_ r_ f_ ds_ (DMap boxConstr_) =
  case IntMap.lookup p1_ boxConstr_ of
    Nothing       -> DMap $ IntMap.insert p1_ (IntMap.singleton r_ [(f_,ds_)]) boxConstr_
    Just innerMap ->
       case IntMap.lookup r_ innerMap of
        Nothing             -> DMap $ IntMap.insert p1_ (IntMap.insert r_ [(f_,ds_)] innerMap)                boxConstr_
        Just innerInnerList -> DMap $ IntMap.insert p1_ (IntMap.insert r_ ((f_,ds_):innerInnerList) innerMap) boxConstr_

boxAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
boxAlreadyDone br ur (r,f)
 | isForward r  = case ( do inner <- IntMap.lookup ur (toMap $ boxConstrFwd br)
                            boxes <- map fst <$> IntMap.lookup r inner
                            return (f `elem` boxes) ) of
                    Just True -> True
                    _         -> False
 | otherwise    = case ( do inner <- IntMap.lookup ur (toMap $ boxConstrBwd br)
                            boxes <- map fst <$> IntMap.lookup (atom r) inner
                            return (f `elem` boxes) ) of
                    Just True -> True
                    _         -> False

-- accessibility Formulas

addAccFormula :: Params -> (DependencySet,Rel,Prefix,Prefix) -> Branch -> BranchInfo
addAccFormula p (ds, r, p1_, p2_) br
 | isBackwards r = addAccFormula p (ds, invRel r, p2_, p1_) br
 | otherwise -- forward
   = addFormulas p toAdd newBr
     where toAdd = transApplications ++ boxApplications
           transApplications = if isTransitive (relInfo br) r
                                then
                                 (  ( map (\(f,ds2) -> PrFormula p2 (dsUnion ds ds2) (Box r f)) toSendFwd )
                                 ++ ( map (\(f,ds2) -> PrFormula p1 (dsUnion ds ds2) (Box r f)) toSendBwd )  )
                                else []
           boxApplications =  (  ( map (\(f,ds2) -> PrFormula p2 (dsUnion ds ds2) f) toSendFwd )
                              ++ ( map (\(f,ds2) -> PrFormula p1 (dsUnion ds ds2) f) toSendBwd )  )
           p1 = getUrfather br (DS.Prefix p1_)
           p2 = getUrfather br (DS.Prefix p2_)
           toSendFwd = IntMap.findWithDefault [] r $ IntMap.findWithDefault IntMap.empty p1 (toMap $ boxConstrFwd br)
           toSendBwd = IntMap.findWithDefault [] r $ IntMap.findWithDefault IntMap.empty p2 (toMap $ boxConstrBwd br)
           newBr = scheduleInclusionRule p1 p2 r ds $ insertRelationBranch br p1 r p2 ds


scheduleInclusionRule :: Prefix -> Prefix -> Rel -> DependencySet -> Branch -> Branch
scheduleInclusionRule p1 p2 r ds br -- todo get all included
 = if null toschedule
    then br
    else br{todoList = newTodoList}
   where parentss = case Map.lookup r (relInfo br) of
                      Nothing -> []
                      Just props -> [ rs | SubsetOf rs <- props]
         toschedule = map (\parents -> (ds,p1,p2,parents)) $ filter (not . alreadyDone) parentss
         alreadyDone = any (`elem` linksFromTo (accStr br) p1 p2)
         utodo       = todoList br
         newTodoList = utodo{roleIncTodo = Set.fromList toschedule `Set.union` roleIncTodo utodo}

insertRelationBranch :: Branch -> Prefix -> Rel -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 r p2 ds
 = br{accStr = insertRelation (accStr br) p1 r p2 ds}


{- blocking conditions -}

isNotBlocked :: Branch -> PrFormula -> Bool
isNotBlocked br pf@(PrFormula pr _ _) =
 case blockMode br of
   PatternBlocking    -> not $ patternBlocked br pf
   AnywhereBlocking   -> not $ any isSubsumer labels
                           where ur = getUrfather br (DS.Prefix pr)
                                 fs = formulasOf br ur
                                 isSubsumer fs_ = fs `Set.isSubsetOf` fs_
                                 labels = map snd $ takeWhile ((< ur).fst) $  ascPrefToForm br
   ChainTwinBlocking  -> isNotChainTwinBlocked br pr

isNotChainTwinBlocked :: Branch -> Prefix -> Bool
isNotChainTwinBlocked br pr = not $ test2equal $ map (formulasOf br) (getAllParents br pr)

getAllParents :: Branch -> Prefix -> [Prefix]
-- getAllParents up to one that has an input nominal
getAllParents br pr = getUrfather br (DS.Prefix pr):rest
 where rest = case IntMap.lookup pr (prefParent br) of
                Nothing     -> []
                Just parent -> if isNominalUrfather br parent
                                then getAllParents br parent
                                else [getUrfather br (DS.Prefix parent)]


test2equal :: (Ord a) => [Set a] -> Bool -- inefficient
test2equal (s:sets) = any (s ==) sets || test2equal sets
test2equal [] = False


{- model building -}

isInTheModel :: Branch -> Prefix -> Bool
isInTheModel br pr | isNominalUrfather br pr
 = case blockMode br of
    PatternBlocking   ->  True
    AnywhereBlocking  ->  True
    ChainTwinBlocking ->  case findModelRepresentativeChainTwinBlocking br pr of
                                 Nothing   -> False
                                 Just repr -> repr == pr
isInTheModel _ _ = False

relationIsInTheModel :: Branch -> (Prefix,Rel,Prefix) -> Bool
relationIsInTheModel br (p1,_,p2)
 = case blockMode br of
     PatternBlocking              -> True
     AnywhereBlocking             -> True
     ChainTwinBlocking            -> hasIdentityUrfather br p1 && hasIdentityUrfather br p2
   where hasIdentityUrfather br_ pr_
          = case findModelRepresentativeChainTwinBlocking br_ pr_ of {Nothing -> False ; _ -> True }

getModelRepresentative :: Branch -> Prefix -> Prefix
getModelRepresentative br pr
 = case blockMode br of
    PatternBlocking -> ur
    AnywhereBlocking-> ur
    ChainTwinBlocking -> fromMaybe ( error $ "interesting counter example " ++ show pr)
                                   $ findModelRepresentativeChainTwinBlocking br pr
   where ur = getUrfather br (DS.Prefix pr)

findModelRepresentativeChainTwinBlocking :: Branch -> Prefix -> Maybe Prefix
findModelRepresentativeChainTwinBlocking br pr
 =  go br pr 0
     where
       go :: Branch -> Prefix -> Prefix -> Maybe Prefix
       go br_ initial current =
          let urCurrent =  getUrfather br (DS.Prefix current) in
           if urCurrent == initial
            then if isNotChainTwinBlocked br initial then Just initial else Nothing
            else if areTwins br_ initial urCurrent && isNotChainTwinBlocked br urCurrent
                   then Just urCurrent
                   else go br_ initial (current+1)

areTwins :: Branch -> Prefix -> Prefix -> Bool
areTwins br p1 p2 = formulasOf br p1 == formulasOf br p2


ascPrefToForm :: Branch -> [(Prefix,Set Formula)]
ascPrefToForm br = [ (pr,formulasOf br pr) | pr <- prefixes br ]


-- <r>f is pattern blocked if its pattern is a subset
-- of one pattern of the branch's pattern store
patternBlocked :: Branch -> PrFormula -> Bool
patternBlocked br f = not $ IntMap.null $ IntMap.filter lookForSuperset (individualPattern br) 
 where lookForSuperset = Set.isSubsetOf (patternOf br f)

-- given a p:<r>f formula, return the pattern:
-- { f } U { f' | p:[r]f' in branch }
-- r has to be forward
patternOf :: Branch -> PrFormula -> Set Formula
patternOf br (PrFormula pr _ (Dia r f))
 = Set.insert f boxes
     where ur = getUrfather br (DS.Prefix pr)
           boxes = if isTransitive (relInfo br) r
                    then boxesOf br ur r `Set.union` (Set.map (Box r) $ boxesOf br ur r)
                    else boxesOf br ur r

patternOf _ _ = error "patternOf called with a non diamond formula"

boxesOf :: Branch -> Prefix -> Rel -> Set Formula
boxesOf br p r
 = set $ map fst $ IntMap.findWithDefault [] r $ IntMap.findWithDefault IntMap.empty p (toMap $ boxConstrFwd br)

findByPattern :: Branch -> Set Formula -> Prefix
findByPattern br pattern
 | blockMode br == PatternBlocking  =
       head $ map fst
            $ filter (\(_,pat2) -> pattern `Set.isSubsetOf` pat2)
            $ IntMap.toList $ individualPattern br
 | blockMode br == AnywhereBlocking =
       head $ map fst
            $ filter (\(_,pat2) -> pattern `Set.isSubsetOf` pat2)
            $ IntMap.toList $ prefToForms br
 | otherwise = error "findByPattern called with ChainTwinBlocking"

-- maybe should get the urfather of given prefix, so that the caller functions won't have to do it
formulasOf :: Branch -> Prefix -> Set Formula
formulasOf br p = IntMap.findWithDefault Set.empty p (prefToForms br)

-- is the formula useful to calculate inclusion urfathers ?
forInclusion :: Branch -> Formula -> Bool
forInclusion br (Lit l)
      | isProp l    = True
      | isNominal l = Set.member (atom l) (relevantNominals br)
      | otherwise   = False -- top, bottom
forInclusion _ (Con _) = False
forInclusion _ (Dis _) = False
forInclusion _ (At _ _) = False
forInclusion _ (Down _ _) = False
forInclusion _ (Box _ _) = True
forInclusion _ (Dia _ _) = True
forInclusion _ (A _) = False
forInclusion _ (E _) = False
forInclusion _ (D _) = False
forInclusion _ (B _) = False

addParentPrefix :: Prefix -> Prefix -> Branch -> BranchInfo
addParentPrefix son father br = BranchOK br{prefParent = IntMap.insert son father (prefParent br)}

{-     modifications done by rule application     -}

addDiaRuleCheck :: Prefix -> (Rel,Formula) -> Prefix -> Branch -> BranchInfo
addDiaRuleCheck pr (r,f) newPr br =
  BranchOK br2
   where pattern = patternOf br (PrFormula ur dsEmpty (Dia r f))
         br1 = case blockMode br of
                 PatternBlocking -> br{individualPattern = IntMap.insert newPr pattern (individualPattern br)}
                 _ -> br
         br2 = br1{diaRlCh=IntMap.insertWith Set.union ur (Set.singleton (r,f)) (diaRlCh br1)}
         ur = getUrfather br (DS.Prefix pr)

diaAlreadyDone :: Branch -> PrFormula -> Bool
diaAlreadyDone b (PrFormula p _ (Dia r f)) =
  case IntMap.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member (r,f) fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ = error "dia already done : wrong formula kind"
--

addDownRuleCheck :: Prefix -> Formula -> Branch -> BranchInfo
addDownRuleCheck pr f br =
  BranchOK br{downRlCh=IntMap.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

downAlreadyDone :: Branch -> PrFormula -> Bool
downAlreadyDone b (PrFormula p _ f@(Down _ _)) =
  case IntMap.lookup ur (downRlCh b) of
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

addUnivConstraint :: Formula -> DependencySet -> Params -> Branch -> BranchInfo
addUnivConstraint f ds p br
 = addFormulas p
               ( map (\pr -> PrFormula pr ds f) urfathers )
               newBr
   where newBr = br{univCons = (ds,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

--

bRule :: Prefix -> Formula -> DependencySet -> Params -> Branch -> BranchInfo
bRule  pr f ds p br
 = addFormula p br2 (PrFormula pr ds $ Down newNom $ A (Lit newNom `disj` f))
    where newNom = nextNom br
          br2 = br{nextNom = nextNom br + 4}
--

addDiffRuleCheck :: Formula -> Maybe Prop -> Branch -> BranchInfo
addDiffRuleCheck f mp br = BranchOK br{dDiaRlCh=Map.insert f mp (dDiaRlCh br)}

--

createNewNode :: Params -> Branch -> BranchInfo
createNewNode p br
 = addFormulas p
               ( map (\(ds,f) -> PrFormula newPr ds f) univConstraints )
               newBrWithRefl
   where newPr = lastPref br + 1
         newBr = br{lastPref = newPr}
         univConstraints = univCons br
         newBrWithRefl = addReflexiveLinks newPr newBr

addReflexiveLinks :: Prefix -> Branch -> Branch
addReflexiveLinks pr br
 = foldr (\rel_ br_ -> insertRelationBranch br_ pr rel_ pr dsEmpty) br reflRels
   where reflRels = Map.keys $ Map.filter (elem Reflexive) (relInfo br)


--

createNewProp :: Branch -> BranchInfo
createNewProp br = BranchOK br{nextProp = nextProp br + 4}

createNewNomTestRelevance :: Formula -> Branch -> BranchInfo
createNewNomTestRelevance f br
 = BranchOK
    br{nextNom = nextNom br + 4,
       relevantNominals = if relevant then Set.insert newNom (relevantNominals br) else relevantNominals br,
       downVarRelevantCh = newDVRC
      }
   where (relevant, newDVRC) = doMemoize checkIfVariableNegatedOnce f (downVarRelevantCh br)
         newNom = nextNom br

--

-- preparation of the branch at the beginning of the calculus:
--  - add the input formula at prefix 0
--  - add a nominal formula at a fresh prefix for each nominal of the input language
--    (even if the nominal was filtered out during lexical normalisation) -- <= TODO currently not the case. Get the nominals from the encoding 
--  - add reflexive links for prefixes 0 and nominal witnesses
addFirstFormulas :: Params -> Branch -> LanguageInfo -> Formula -> BranchInfo
addFirstFormulas p br_ fLang f
 = addFormulas p [pf] br3
    where ns = languageNoms fLang
          nbNs = length ns
          nomWitnesses = [1..nbNs]
          br =  foldr addReflexiveLinks (  br_{lastPref = nbNs} ) (0:nomWitnesses)
          pf = firstPrefixedFormula f
          newClasses = foldr (\(pr,n) -> DS.union (DS.Prefix pr) (DS.Nominal n))
                             (nomPrefClasses br)
                             (zip [1..] ns)
          newClashStr = foldr (\(pr,n) -> DMap.insert pr n dsEmpty)
                              DMap.empty
                              (zip [1..] ns)
          br2 = br{nomPrefClasses = newClasses,
                         clashStr = newClashStr}
          br3 = foldr (\(pr,n) -> bookKeepFormula p (PrFormula pr dsEmpty (Lit n)))
                      br2
                      (zip [1..] ns)

{-     functions to handle the "clashable information", ie literals associated to prefixes     -}

data UpdateResult = UpdateSuccess ClashableInfo | UpdateFailure DependencySet

addToClashable :: Prefix -> DependencySet -> Literal -> Branch -> BranchInfo
addToClashable pr_ ds1 l br
  = case updateMap (clashStr br) pr ds l of
     UpdateSuccess cs  -> BranchOK br{clashStr = cs}
     UpdateFailure dsf -> BranchClash br pr dsf (Lit l)
   where (pr,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr_)
         ds = ds1 `dsUnion` ds2


-- Insert a piece of clashable information into all the clashable information of a branch

updateMap :: ClashableInfo -> Prefix -> DependencySet -> Literal -> UpdateResult
updateMap cs  _  ds l | isTop l    = UpdateSuccess cs
                      | isBottom l = UpdateFailure ds
updateMap (DMap cs) pre ds l
  = case IntMap.lookup pre cs of
       Nothing   -> UpdateSuccess $ DMap $ IntMap.insert pre (IntMap.singleton l ds) cs
       Just slot -> case cisUpdate slot l ds of
                     SlotUpdateSuccess updatedSlot -> UpdateSuccess $ DMap $ IntMap.insert pre updatedSlot cs
                     SlotUpdateFailure failureDeps -> UpdateFailure failureDeps


type ClashableInfoSlot = IntMap {- Literal -} DependencySet
data SlotUpdateResult =   SlotUpdateSuccess ClashableInfoSlot
                         | SlotUpdateFailure DependencySet


-- Union a list of clashable info slots
cisUnions :: [ClashableInfoSlot] -> SlotUpdateResult
cisUnions []              = SlotUpdateSuccess IntMap.empty
cisUnions [cis]           = SlotUpdateSuccess cis
cisUnions (cis1:cis2:tl)
 = case cisUnion cis1 cis2 of
     failure@(SlotUpdateFailure _) -> failure
     SlotUpdateSuccess newCis      -> cisUnions (newCis:tl)

-- Union two clashable info slots

-- if there is a clash, the result reports the set of dependencies whose earliest dependency is the earliest
-- among all dependencies sets that caused the clash
cisUnion :: ClashableInfoSlot -> ClashableInfoSlot -> SlotUpdateResult
cisUnion cis1 cis2
 = ucis_helper cis1 (IntMap.assocs cis2)
    where ucis_helper :: ClashableInfoSlot -> [(Literal,DependencySet)] -> SlotUpdateResult
          ucis_helper cis l_ds_s =
             let (updateStatus,clashing_ds_s)
                  = foldr (\(l,ds) (upResult,clashingBps_s)
                           -> case upResult of
                               SlotUpdateSuccess cis_ ->  (cisUpdate cis_ l ds,      clashingBps_s)
                               SlotUpdateFailure ds_s ->  (cisUpdate cis  l ds, ds_s:clashingBps_s)
                                                                 -- we reuse the input Clashabe Info Slot
                          )
                          (SlotUpdateSuccess cis,[])   l_ds_s
                 result = case clashing_ds_s of
                              []   -> updateStatus                                    -- is 'success'
                              ds_s -> SlotUpdateFailure $ findEarliestSet ds_s
                                         where findEarliestSet = minimumBy compareBPSets
                                               compareBPSets ds1 ds2 = comparing dsMin ds1 ds2
             in
                result


-- Insert a piece of information in a clashable info slot

cisUpdate :: ClashableInfoSlot -> Literal -> DependencySet -> SlotUpdateResult
cisUpdate cis l ds  | isTop l     = SlotUpdateSuccess cis
                    | isBottom l  = SlotUpdateFailure ds
cisUpdate cis l ds  -- nominals, propositional symbols
 = case IntMap.lookup (negLit l) cis of
    Just ds2         -> SlotUpdateFailure $ dsUnion ds ds2
    Nothing          -> SlotUpdateSuccess $ IntMap.insertWith mergeDeps l ds cis
                         where mergeDeps d1 d2  = if dsMin d1 < dsMin d2 then d1 else d2
                                -- if the same information is caused by an earlier
                                -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

cisAddDeps :: DependencySet -> SlotUpdateResult -> SlotUpdateResult
cisAddDeps ds res_cis =
 case res_cis of
  SlotUpdateSuccess cis -> SlotUpdateSuccess $ IntMap.map (dsUnion ds) cis
  failure                -> failure



cisQuery :: Branch -> Prefix -> Literal -> Maybe (Bool,DependencySet)
-- Output : Nothing = nevermind ; Just True = already there ; Just False = contrary there
cisQuery _ _ l | isTop l    = Just (True,dsEmpty)
               | isBottom l = Just (False,dsEmpty)
cisQuery br pr l
  = case DMap.lookup pr l (clashStr br) of
      Just ds    -> Just (True,ds)
      Nothing    -> case DMap.lookup pr (negLit l) (clashStr br) of
                      Just ds -> Just (False,ds)
                      Nothing -> Nothing

{-     function used for unit propagation     -}

data ReducedDisjunct
 =   Triviality
   | Contradiction DependencySet
   | Reduced DependencySet (Set Formula) (Maybe Prop) -- proposable witness for lazy branching
 deriving Show

reduceDisjunctionProposeLazy :: Branch -> Prefix -> Set Formula -> ReducedDisjunct
reduceDisjunctionProposeLazy br pr fs
 =  case Set.fold go (Just ( Set.empty , dsEmpty, Nothing )) fs of
     Nothing -> Triviality
     Just (disjuncts,ds,proposed)
       | Set.null disjuncts -> Contradiction ds
       | otherwise -> Reduced ds disjuncts proposed -- what if not reduced ? and no proposed witness ?
   where
      ur = getUrfather br (DS.Prefix pr)
      go _ Nothing = Nothing
      go l@(Lit current) (Just (disjuncts,ds_,proposed))
       = case (cisQuery br ur current, proposed) of
          (Just (True,_)    ,_) -> Nothing
          (Just (False,ds2) ,_) -> Just (disjuncts,dsUnion ds_ ds2, proposed)
          (Nothing, Nothing)
           -> if isPositiveNom current
               then Just (Set.insert l disjuncts,ds_,Nothing) -- no lazy branching with positive nominals
               else case DMap.lookup ur (negLit current) (brWitnesses br) of
                      -- if current is a negated nominal, we know the "just" case is impossible
                     Just _  -> Just (Set.insert l disjuncts,ds_,Nothing) -- there's an opposed witness
                     Nothing -> Just (Set.insert l disjuncts,ds_, Just current) -- propose for witness
          _ {- already a proposed witness -}
           -> Just (Set.insert l disjuncts,ds_,proposed)
      go f               (Just (disjuncts,ds_,proposed)) = Just (Set.insert f disjuncts, ds_,proposed)


{-     other functions     -}
prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]

oneIs :: RelInfo -> RelProperty -> Bool
oneIs relI p = any ( elem p . snd) $ Map.toList relI

hasProperty :: RelProperty -> RelInfo -> Rel -> Bool
hasProperty p relI r = case Map.lookup r relI of
                        Nothing         -> False
                        Just properties -> p `elem` properties

isSymmetric :: RelInfo -> Rel -> Bool
isSymmetric = hasProperty Symmetric

isTransitive :: RelInfo -> Rel -> Bool
isTransitive = hasProperty Transitive

almostCartesianProduct :: [a] -> [b] -> [(a,b)]
almostCartesianProduct [] _  = error "almostCartesianProduct: first list empty"
almostCartesianProduct _  [] = error "almostCartesianProduct: second list empty"
almostCartesianProduct as bs = [(a,b) | (idxA,a) <- zip [(0::Int)..] as,
                                        (idxB,b) <- zip [(0::Int)..] bs,
                                        idxA /= idxB]

moveInMap :: IntMap b -> Int -> Int -> (b -> b -> b) -> IntMap b
moveInMap m origKey destKey mergeF
 = result
   where mOrigValue = IntMap.lookup origKey m
         prunedM    = IntMap.delete origKey m
         result = case mOrigValue of
                   Nothing -> m
                   Just origValue -> IntMap.insertWith mergeF destKey origValue prunedM

doMemoize :: Ord a => (a -> b) -> a -> Map.Map a b -> (b, Map.Map a b)
doMemoize f e m = case Map.lookup e m of
                   Nothing     -> let result = f e in (result, Map.insert e result m)
                   Just result -> (result, m)

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList
