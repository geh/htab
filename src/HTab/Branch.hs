{-# OPTIONS_GHC -fglasgow-exts #-}

----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module HTab.Branch
(
Branch(..), createNewProp, createNewPref, createNewNomTestRelevance, BranchInfo(..),
addFormulas, addFormula, addAccFormula,
addDiaRuleCheck, addDiaXRuleCheck, addDownRuleCheck, addDiffRuleCheck,
addParentPrefix, addFirstFormulas,
TodoList(..),
emptyBranch,prefixes,
reduceDisjunctionProposeLazy, doLazyBranching,
merge,
getUrfather, getUrfatherAndDeps, isInTheModel, relationIsInTheModel,
getModelRepresentative, isNotBlocked,
BlockingMode(..), diaAlreadyDone, diaXAlreadyDone,
downAlreadyDone,
unfulfilledEventualities, ReducedDisjunct(..),
isSymmetric, isTransitive,
deleteUEV, insertUEV_addFormula
) where

import Data.List(minimumBy)
import Data.Maybe( mapMaybe )
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
import qualified HTab.Relations as Relations

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

type Clashable_info      = DMap {- Prefix Literal -} DependencySet
type Box_constraints     = DMap {- Prefix Rel -} [(Formula,DependencySet)]
type Branching_witnesses = DMap {- Prefix Literal -} [PrFormula]
type EquivClasses = DS.DisjSet DS.Pointer
data BlockingMode = AnywhereBlocking | ChainTwinBlocking  deriving (Eq,Show)

data Branch =
              Branch {clashStr :: Clashable_info,
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- immediate rules constraints
                  boxConstrFwd :: Box_constraints,
                  boxConstrBwd :: Box_constraints,
                      univCons :: [(DependencySet,Formula)],
                 -- saturation of rules
                       diaRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                      diaXRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                       boxRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                      boxXRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                      downRlCh :: IntMap {- Prefix -} (Set Formula),
                        atRlCh :: Set Formula,
                     existRlCh :: Set Formula,
                      dDiaRlCh :: Map Formula (Maybe Prop),
                 -- formulas true in an equivalence class
                   prefToForms :: IntMap {- Prefix -} (Set Formula),
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: IntMap {- Prefix -} DependencySet,
                 -- other data
                        accStr :: Relations,
                 -- equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       nextNom :: Nom,
                      nextProp :: Prop,
                 eventualities :: IntMap DependencySet,
                 -- lazy branching
                   brWitnesses :: Branching_witnesses,
                 -- caching / memoisation data
             downVarRelevantCh :: Map Formula Bool,
                 -- information about language of input formula and blocking mode
                 inputLanguage :: LanguageInfo,
                     blockMode :: BlockingMode,
             unblockedPrefsLim :: Prefix,
                   blockedDias :: IntMap {- Prefix -} [PrFormula],
                    prefParent :: IntMap {- Prefix -} Prefix,
              relevantNominals :: Set Nom,
                       relInfo :: RelInfo,
                      encoding :: Encoding}

--

emptyBranch :: LanguageInfo -> RelInfo -> Encoding -> Branch
emptyBranch fLang relInfo_ encoding_ =
                Branch
                { clashStr          = DMap.empty,
                  todoList          = emptyTodoList,
                  accStr            = emptyRels,
                  boxConstrBwd      = DMap.empty,
                  boxConstrFwd      = DMap.empty,
                  diaRlCh           = IntMap.empty,
                  diaXRlCh          = IntMap.empty,
                  boxRlCh           = IntMap.empty,
                  boxXRlCh          = IntMap.empty,
                  downRlCh          = IntMap.empty,
                  atRlCh            = Set.empty,
                  existRlCh         = Set.empty,
                  dDiaRlCh          = Map.empty,
                  downVarRelevantCh = Map.empty,
                  univCons          = [],
                  lastPref          = 0,
                  nextNom           = maxNom encoding_ + 4,
                  nextProp          = maxProp encoding_ + 4,
                  prefToForms       = IntMap.empty,
                  prToDepSet        = IntMap.empty,
                  eventualities     = IntMap.empty,
                  brWitnesses       = DMap.empty,
                  nomPrefClasses    = DS.mkDSet,
                  inputLanguage     = fLang,
                  blockMode         = blockingMode,
                  unblockedPrefsLim = 0,
                  blockedDias       = IntMap.empty,
                  prefParent        = IntMap.empty,
                  relevantNominals  = set $ relevantNoms fLang,
                  relInfo           = relInfo_,
                  encoding          = encoding_
                }
 where blockingMode =
         if    languagePast fLang
            || languageTrans fLang
            || relInfo_ `oneIs` Symmetric
            || relInfo_ `oneIs` Functional
            || relInfo_ `oneIs` Injective
           then ChainTwinBlocking
           else AnywhereBlocking

instance Show Branch where
 show br
  = concat [  show (inputLanguage br),
              "\nClashable formulas:", showIMap (\v -> "(" ++ showMap_lits v ++ ")") "\n " (toMap $ clashStr br),
              "\n", show (todoList br),
              showl "\nRelations: "       (accStr br),
              ifNotEmpty (boxConstrFwd br)
                         (\c -> "\nBox fwd: " ++ showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap c)),
              ifNotEmpty (boxConstrBwd br)
                         (\c -> "\nBox bwd: " ++ showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (toMap c)),
              ifNotEmpty (brWitnesses br)
                         (\c -> "\nWitnesses: " ++ showIMap (\v  -> "(" ++ showMap_lits2 v ++ ")") "\n " (toMap c)),
              showl "\nDia rule chart: "  (diaRlCh br),
              showl "\nDown rule chart: " (downRlCh br),
              showl "\n@ rule chart: "     (list $ atRlCh br),
              showl "\nExist rule chart: " (list $ existRlCh br),
              showl "\nDiff dia rule chart: "   (dDiaRlCh br),
              showl "\nDown var relevant chart: " (downVarRelevantCh br),
              showl "\nUniv constraints: " (univCons br),
              ifNotEmpty (prToDepSet br) (\m -> "\nPrefix to dependency set:" ++ showIMap  dsShow "\n " m),
              ifNotEmpty (prefToForms br) (\m -> "\nPrefix to formulas:"       ++ showIMap  (show . Set.toList) "\n " m),
              showl "\nEventualities: "  (eventualities br),
              showl "\nParent: " (prefParent br),
              "\nBlocking mode: ", show (blockMode br),
              "\nPrefix-Nominal classes : ", showMap show ", " (nomPrefClasses br),
              "\nModel-relevant nominals : " ++ (unwords $  map showLit $ list $ relevantNominals br),
              "\nlastPref : " ++ show (lastPref br) ++
              " nextnom : "  ++ showLit (nextNom br) ++
              " nextprop : " ++ showLit (nextProp br)
           ]
              where
                  ifNotEmpty b f = if empty b then "" else f b
                  showl intro b  = if empty b then "" else intro ++ show b

                  showIMap vShow sep = IntMap.foldWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) ""
                  showMap vShow sep  = Map.foldWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) ""
                  showMap_lits       = IntMap.foldWithKey (\l d   -> (++ showLit l ++ " " ++ dsShow d  ++ ", ")) ""
                  showMap_lits2      = IntMap.foldWithKey (\l fs  -> (++ showLit l ++ " " ++ ":" ++ show fs ++ ", ")) ""
                  showMap_rel        = IntMap.foldWithKey (\r dxs -> (++ "-" ++ showRel r ++ "-> " ++ show dxs ++ ", ")) ""

class Emptyable a where
 empty :: a -> Bool

instance Emptyable [a] where
 empty [] = True
 empty _  = False

instance Emptyable (Map a b) where
 empty = Map.null

instance Emptyable (IntMap b) where
 empty = IntMap.null

instance Emptyable (DMap c) where
 empty (DMap m) = IntMap.null m

instance Emptyable Relations where
 empty = Relations.null

instance Emptyable (Set a) where
 empty = Set.null


data TodoList= TodoList{disjTodo :: Set PrFormula,
                         diaTodo :: Set PrFormula,
                        diaXTodo :: Set PrFormula,
                       existTodo :: Set PrFormula,
                          atTodo :: Set PrFormula,
                        downTodo :: Set PrFormula,
                        diffTodo :: Set PrFormula,
                       mergeTodo :: Set (DependencySet, Prefix, DS.Pointer),
                     roleIncTodo :: Set (DependencySet, Prefix, Prefix, [Rel]) }

instance Show TodoList where
 show (TodoList disjs dias diaxs es ars downs diffs merges rolein)
   = "Todo lists:" ++ concatMap (\el -> "\n" ++ show (list el)) [disjs, dias, diaxs, es, ars, downs, diffs]
                   ++ "\n" ++ show (list merges)
                   ++ "\n" ++ show (list rolein)

emptyTodoList :: TodoList
emptyTodoList =
      TodoList {  disjTodo = Set.empty,
                   diaTodo = Set.empty,
                  diaXTodo = Set.empty,
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

addFormulas :: Params -> Branch -> [PrFormula] -> BranchInfo
addFormulas p br fs =
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
   Con fs     -> addFormulas p br (prefix pr ds fs)
   Dis _      -> putAwayDisjunction p pf br
   Dia _ _    -> BranchOK $ addToTodo pf br
   DiaX _ _ _ -> BranchOK $ addToTodo pf br
   Box r f    -> addBoxConstraint      pr r f ds p br
   BoxX r f   -> addBoxXConstraint     pr r f ds p br
   A f        -> addUnivConstraint          f ds p br
   B f        -> b_rule                pr   f ds p br
   E _        -> BranchOK $ addToTodo pf br
   D _        -> BranchOK $ addToTodo pf br
   At _ _     -> BranchOK $ addToTodo pf br
   Down _ _   -> BranchOK $ addToTodo pf br
   Lit l | isPositiveNom l -> addToClashable pr ds l $ addToTodo pf br
   Lit l                   -> addToClashable pr ds l br

putAwayDisjunction :: Params -> PrFormula -> Branch -> BranchInfo
putAwayDisjunction p pf@(PrFormula pr ds f@(Dis fs)) br
 | lazyBranching p && ur <= unblockedPrefsLim br
  = case reduceDisjunctionProposeLazy br pr fs of
     Contradiction dsClash -> BranchClash br pr (dsUnion ds dsClash) f
     Triviality -> BranchOK br
     Reduced new_ds disjuncts mProposed
      -> let fNew = PrFormula pr (dsUnion ds new_ds) (Dis disjuncts) --todo if there was no reduction, leave ds
         in
          case mProposed of
            Nothing -> BranchOK $ addToTodo fNew br
            Just lit -- add pr, lit, ((++) disjuncts) aux witnesses
             -> BranchOK $ doLazyBranching ur lit [fNew] br
 | otherwise
  = BranchOK $ addToTodo pf br
 where ur = getUrfather br (DS.Prefix pr)

putAwayDisjunction _ pf _ = error ("putAwayDisjunction " ++ show pf)

doLazyBranching :: Prefix -> Literal -> [PrFormula] -> Branch -> Branch
doLazyBranching pr lit pfs br -- assume the tests have been done beforehand
 = case DMap.lookup1 pr (brWitnesses br) of
    Nothing -> let newBrW = DMap.insert pr lit pfs (brWitnesses br)
               in br{brWitnesses = newBrW}
    Just innerMap
     -> case IntMap.lookup lit innerMap of -- assume this is the only place where l or (negLit l) occur
         Nothing -> let newInner = IntMap.insert lit pfs innerMap
                        newBrW = DMap.insert1 pr newInner (brWitnesses br)
                    in br{brWitnesses = newBrW}
         Just fs -- assume the test was already done
          -> let newInner = IntMap.insert lit (pfs++fs) innerMap
                 newBrW = DMap.insert1 pr newInner (brWitnesses br)
             in br{brWitnesses = newBrW}


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
         DiaX _ _ _         -> utodo{ diaXTodo = Set.insert pf ( diaXTodo utodo)}
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
     DiaX _ r ev        -> diaXAlreadyDone br p (r,ev)
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

{-    helper functions for equivalence class merge     -}

merge :: Params -> Branch -> Prefix -> DependencySet -> DS.Pointer -> BranchInfo
merge p br pr fDs pointer -- pointer is a nominal or a prefix
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
              Slot_UpdateFailure clashingDeps ->
                  let newBr = br{nomPrefClasses = classes3} in
                  BranchClash newBr pr (dsUnion clashingDeps currentDeps) (neg taut)

              Slot_UpdateSuccess urfatherSlot ->
                  let newClashStr     = DMap $ IntMap.delete oldUr $ IntMap.insert newUr urfatherSlot (toMap $ clashStr br)

                      -- structures that merge
                      newPrefToForms  = moveInMap (prefToForms br) oldUr newUr Set.union
                      newBoxConstrFwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrFwd br) oldUr newUr
                      newBoxConstrBwd = DMap.moveInnerDataDMapPlusDeps fDs (boxConstrBwd br) oldUr newUr
                      newAccStr       = mergePrefixes (accStr br) oldUr newUr fDs
                      newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
                      newDiaXRlCh     = moveInMap (diaXRlCh br) oldUr newUr Set.union
                      newBoxRlCh      = moveInMap (boxRlCh br)  oldUr newUr Set.union
                      newBoxXRlCh     = moveInMap (boxXRlCh br) oldUr newUr Set.union
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
                                           diaXRlCh       = newDiaXRlCh,
                                           boxRlCh        = newBoxRlCh,
                                           boxXRlCh       = newBoxXRlCh,
                                           blockedDias    = newBlockedDias,
                                           clashStr       = newClashStr,
                                           brWitnesses    = newBrWitnesses}
                  in
                      addFormulas p newBr formulasToAdd

mergeWitnesses :: Prefix -> Prefix -> Clashable_info_slot -> Branching_witnesses -> (Branching_witnesses, [PrFormula])
mergeWitnesses oldUr newUr urfatherSlot dbrWits@(DMap brWits)
 =( DMap.insert1 newUr newDest2 ( DMap.delete oldUr dbrWits ), toAdd1 ++ toAdd2 )
  where
   srcInnerMap  = maybe IntMap.empty id (IntMap.lookup oldUr brWits)
   destInnerMap = maybe IntMap.empty id (IntMap.lookup newUr brWits)
   (newDest1,toAdd1) = mergeWitnesses_WitnessesMap srcInnerMap destInnerMap
   (newDest2,toAdd2) = mergeWitnesses_AgainstClashable newDest1 urfatherSlot

mergeWitnesses_WitnessesMap :: IntMap [PrFormula] -> IntMap [PrFormula] -> (IntMap [PrFormula], [PrFormula])
mergeWitnesses_WitnessesMap srcWitMap destWitMap
 = foldr go (destWitMap,[]) $ IntMap.assocs srcWitMap
   where
      go (l,fs) (destMap,toAddAgain)
         = case IntMap.lookup l destMap of
            Just fs2 -> (IntMap.insert l (fs2++fs) destMap, toAddAgain)
            Nothing
             -> case IntMap.lookup (negLit l) destMap of -- (negLit l) is just one bit away from l in the map, but we don't use it
                  Just fs2 -> (IntMap.delete (negLit l) destMap, fs++fs2++toAddAgain)
                  Nothing ->  (IntMap.insert l fs destMap, toAddAgain)

mergeWitnesses_AgainstClashable :: IntMap [PrFormula] -> Clashable_info_slot -> (IntMap [PrFormula],[PrFormula])
mergeWitnesses_AgainstClashable  witMap cis
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
addToPrefToForms (PrFormula pr _ f) br | forInclusion br f =
  br{prefToForms = newMap}
 where currentPtf = prefToForms br
       newMap = IntMap.insertWith Set.union pr (Set.singleton f) currentPtf
addToPrefToForms _ br = br

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

-- <*>-related functions

deleteUEV :: Branch -> Int -> Branch
deleteUEV br idx = br{eventualities = IntMap.delete idx (eventualities br)}

insertUEV_addFormula :: Branch -> Params -> Maybe Int -> DependencySet -> (Int -> PrFormula) -> BranchInfo
insertUEV_addFormula br p mi ds ff
 = addFormula p br2 f
  where idxToUse = case mi of
                    Nothing   -> case IntMap.maxViewWithKey $ eventualities br of
                                   Nothing        -> 0
                                   Just ((i,_),_) -> i+1
                    Just idx  -> idx
        newEvs = IntMap.insertWith dsUnion idxToUse ds $ eventualities br
        br2 = br{eventualities= newEvs}
        f = ff idxToUse

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
addBoxConstraint pr_ r f ds p br_
 | boxAlreadyDone br_ pr (r,f) = BranchOK br_
 | isForward r
    = let    newBr = br{boxConstrFwd = updateBoxConstr pr r f ds (boxConstrFwd br)}
             accessiblePrDs   = IntMap.findWithDefault [] r $ successors (accStr br) pr
             toAdd = symApplications ++ transApplications ++ boxApplications
             transApplications = if isTransitive (relInfo br) r
                                 then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) accessiblePrDs
                                 else []
             symApplications = [PrFormula pr ds $ Box (invRel r) f | isSymmetric (relInfo br) r]
             boxApplications = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) accessiblePrDs
      in
         addFormulas p newBr toAdd

 | otherwise
   = let    newBr = br{boxConstrBwd = updateBoxConstr pr (atom r) f ds (boxConstrBwd br)}
            accessiblePrDs          = IntMap.findWithDefault [] (atom r) $ predecessors (accStr br) pr
            toAdd = transApplications ++ boxApplications -- no symApplications cause inv rewritten as forward during parsing
            transApplications = if isTransitive (relInfo br) (atom r)
                                then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) accessiblePrDs
                                else []
            boxApplications = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) accessiblePrDs
     in
        addFormulas p newBr toAdd
 where pr = getUrfather br_ (DS.Prefix pr_)
       br = addBoxRuleCheck br_ pr (r,f)

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> Box_constraints -> Box_constraints
updateBoxConstr p1_ r_ f_ ds_ (DMap boxConstr_) =
  case IntMap.lookup p1_ boxConstr_ of
    Nothing       -> DMap $ IntMap.insert p1_ (IntMap.singleton r_ [(f_,ds_)]) boxConstr_
    Just innerMap ->
       case IntMap.lookup r_ innerMap of
        Nothing             -> DMap $ IntMap.insert p1_ (IntMap.insert r_ [(f_,ds_)] innerMap)                boxConstr_
        Just innerInnerList -> DMap $ IntMap.insert p1_ (IntMap.insert r_ ((f_,ds_):innerInnerList) innerMap) boxConstr_

addBoxRuleCheck :: Branch -> Prefix -> (Rel,Formula) -> Branch
addBoxRuleCheck br ur (r,f) =
  br{boxRlCh=IntMap.insertWith Set.union ur (Set.singleton (r,f)) (boxRlCh br)}

boxAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
boxAlreadyDone b ur (r,f) =
  case IntMap.lookup ur (boxRlCh b) of
     Nothing  -> False
     Just fset -> Set.member (r,f) fset

-- [*]phi --> phi & [][*]phi
-- need not to do all that addBoxConstraint does
addBoxXConstraint :: Prefix -> Rel -> Formula -> DependencySet -> Params ->  Branch -> BranchInfo
addBoxXConstraint pr r f ds p br
 | boxXAlreadyDone br ur (r,f) = BranchOK br
 | otherwise = addFormulas p br2 [PrFormula pr ds f, PrFormula pr ds (Box r (BoxX r f))]
   where ur = getUrfather br (DS.Prefix pr)
         br2 = addBoxXRuleCheck br ur (r,f)

addBoxXRuleCheck :: Branch -> Prefix -> (Rel,Formula) -> Branch
addBoxXRuleCheck br ur (r,f) =
  br{boxXRlCh=IntMap.insertWith Set.union ur (Set.singleton (r,f)) (boxXRlCh br)}

boxXAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
boxXAlreadyDone b ur (r,f) =
  case IntMap.lookup ur (boxXRlCh b) of
     Nothing  -> False
     Just fset -> Set.member (r,f) fset

addAccFormula :: Params -> Branch -> AccFormula -> BranchInfo
addAccFormula p br (AccFormula ds r p1_ p2_)
 | isBackwards r = addAccFormula p br (AccFormula ds (invRel r) p2_ p1_)
 | otherwise -- forward
   = addFormulas p newBr toAdd
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
         newTodoList = utodo{roleIncTodo  = Set.union (Set.fromList toschedule) (roleIncTodo utodo)}

insertRelationBranch :: Branch -> Prefix -> Rel -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 r p2 ds
 = br{accStr = insertRelation (accStr br) p1 r p2 ds}


{- blocking conditions -}

isNotBlocked :: Branch -> Prefix -> Bool
isNotBlocked br pr
 | pr <= unblockedPrefsLim br = True
 | otherwise =
 case blockMode br of
   AnywhereBlocking   -> null $ filter isSubsumer labels
                           where ur = getUrfather br (DS.Prefix pr)
                                 fs = formulasOf br ur
                                 isSubsumer fs_ = fs `Set.isSubsetOf` fs_
                                 labels = map snd $ takeWhile ((< ur).fst) $  ascPrefToForm br
   ChainTwinBlocking  -> isNotChainTwinBlocked br pr

isNotChainTwinBlocked :: Branch -> Prefix -> Bool
isNotChainTwinBlocked br pr = not $ test2equal $ map (formulasOf br) (getAllParents br pr)

getAllParents :: Branch -> Prefix -> [Prefix]
-- getAllParents up to one that has an input nominal
getAllParents br pr = (getUrfather br (DS.Prefix pr)):rest
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
    AnywhereBlocking  ->  getModelRepresentative br pr == pr
    ChainTwinBlocking ->  case findModelRepresentativeChainTwinBlocking br pr of
                                 Nothing   -> False
                                 Just repr -> repr == pr
isInTheModel _ _ = False

relationIsInTheModel :: Branch -> (Prefix,Rel,Prefix) -> Bool
relationIsInTheModel br (p1,_,p2)
 = case blockMode br of
     ChainTwinBlocking            -> hasIdentityUrfather br p1 && hasIdentityUrfather br p2
     AnywhereBlocking             -> isInTheModel br p1
   where hasIdentityUrfather br_ pr_
          = case findModelRepresentativeChainTwinBlocking br_ pr_ of {Nothing -> False ; _ -> True }

getModelRepresentative :: Branch -> Prefix -> Prefix  -- which is also an inclusion representative
getModelRepresentative br pr
 = case blockMode br of
    AnywhereBlocking-> case map fst $ filter (Set.isSubsetOf fs . snd) $ ascPrefToForm br of
                         []     -> pr
                         (hd:_) -> hd
                         where ur = getUrfather br (DS.Prefix pr)
                               fs = formulasOf br ur
    ChainTwinBlocking -> case findModelRepresentativeChainTwinBlocking br pr of
                          Nothing -> error ("found an interesting counter example " ++ show pr)
                          Just repr -> repr


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
forInclusion _ (BoxX _ _)   = False
forInclusion _ (DiaX _ _ _) = False
forInclusion _ (A _) = False
forInclusion _ (E _) = False
forInclusion _ (D _) = False
forInclusion _ (B _) = False

addParentPrefix :: Branch -> Prefix -> Prefix -> Branch
addParentPrefix br son father =  br{prefParent = IntMap.insert son father (prefParent br)}

{-     modifications done by rule application     -}

addDiaRuleCheck :: Branch -> Prefix -> (Rel,Formula) -> Branch
addDiaRuleCheck br pr (r,f) =
  br{diaRlCh=IntMap.insertWith Set.union ur (Set.singleton (r,f)) (diaRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaAlreadyDone :: Branch -> PrFormula -> Bool
diaAlreadyDone b (PrFormula p _ (Dia r f)) =
  case IntMap.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member (r,f) fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ = error "dia already done : wrong formula kind"
--

addDiaXRuleCheck :: Branch -> Prefix -> (Rel, Formula) -> Branch
addDiaXRuleCheck br pr f =
  br{diaXRlCh=IntMap.insertWith Set.union ur (Set.singleton f) (diaXRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

diaXAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
diaXAlreadyDone b p f =
  case IntMap.lookup ur (diaXRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)



unfulfilledEventualities :: Branch -> Maybe DependencySet
unfulfilledEventualities br
 = if IntMap.null $ eventualities br
    then Nothing
    else Just $ dsUnions $ IntMap.elems $ eventualities br

--

addDownRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDownRuleCheck br pr f =
  br{downRlCh=IntMap.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
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
 = addFormulas p newBr
               ( map (\pr -> PrFormula pr ds f) urfathers )
   where newBr = br{univCons = (ds,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

--

b_rule :: Prefix -> Formula -> DependencySet -> Params -> Branch -> BranchInfo
b_rule  pr f ds p br
 = addFormula p br2 (PrFormula pr ds $ Down newNom $ A (Lit newNom `disj` f))
    where newNom = nextNom br
          br2 = br{nextNom = nextNom br + 4}
--

addDiffRuleCheck :: Branch -> Formula -> Maybe Prop -> Branch
addDiffRuleCheck br f mp = br{dDiaRlCh=Map.insert f mp (dDiaRlCh br)}

--

createNewPref :: Params -> Branch -> BranchInfo
createNewPref p br
 = addFormulas p newBrWithRefl
                         ( map (\(ds,f) -> PrFormula newPr ds f) univConstraints )
   where newPr = lastPref br + 1
         newBr = br{lastPref = newPr}
         univConstraints = univCons br
         newBrWithRefl = addReflexiveLinks newPr newBr

addReflexiveLinks :: Prefix -> Branch -> Branch
addReflexiveLinks pr br
 = foldr (\rel_ br_ -> insertRelationBranch br_ pr rel_ pr dsEmpty) br reflRels
   where reflRels = Map.keys $ Map.filter (elem Reflexive) (relInfo br)


--

createNewProp :: Branch -> Branch
createNewProp br = br{nextProp = nextProp br + 4}

createNewNomTestRelevance :: Branch -> Formula -> Branch
createNewNomTestRelevance br f
 = br{nextNom = nextNom br + 4,
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
--  - add functionality and injectivitty down-arrow formulas
addFirstFormulas :: Params -> Branch -> LanguageInfo -> Formula -> BranchInfo
addFirstFormulas p br_ fLang f
 = addFormulas p br5 ([pf]++funUniv++injUniv)
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
          funUniv = map (\r -> PrFormula 0 dsEmpty
                                $ A $ Down newNom $ Box (inv r (relInfo br)) $ Box r (Lit newNom)) funRels
                       where funRels = Map.keys $ Map.filter (elem Functional) (relInfo br)
          injUniv = map (\r -> PrFormula 0 dsEmpty
                                $ A $ Down newNom $ Box r $ Box (inv r (relInfo br)) (Lit newNom)) injRels
                       where injRels = Map.keys $ Map.filter (elem Injective) (relInfo br)
          newNom = nextNom br3
          br4 = br3{nextNom = nextNom br3 + 4}
          br5 = br4{unblockedPrefsLim = nbNs}

{-     functions to handle the "clashable information", ie literals associated to prefixes     -}

data UpdateResult = UpdateSuccess Clashable_info | UpdateFailure DependencySet

addToClashable :: Prefix -> DependencySet -> Literal -> Branch -> BranchInfo
addToClashable pr_ ds1 l br
  = case updateMap (clashStr br) pr ds l of
     UpdateSuccess cs  -> BranchOK br{clashStr = cs}
     UpdateFailure dsf -> BranchClash br pr dsf (Lit l)
   where (pr,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr_)
         ds = ds1 `dsUnion` ds2


-- Insert a piece of clashable information into all the clashable information of a branch

updateMap :: Clashable_info -> Prefix -> DependencySet -> Literal -> UpdateResult
updateMap cs  _  ds l | isTop l    = UpdateSuccess cs
                      | isBottom l = UpdateFailure ds
updateMap (DMap cs) pre ds l
  = case IntMap.lookup pre cs of
       Nothing            -> UpdateSuccess $ DMap $ IntMap.insert pre (IntMap.singleton l ds) cs
       Just slot          -> case cisUpdate slot l ds of
                              Slot_UpdateSuccess updatedSlot -> UpdateSuccess $ DMap $ IntMap.insert pre updatedSlot cs
                              Slot_UpdateFailure failureDeps -> UpdateFailure failureDeps


type Clashable_info_slot = IntMap {- Literal -} DependencySet
data Slot_UpdateResult =   Slot_UpdateSuccess Clashable_info_slot
                         | Slot_UpdateFailure DependencySet


-- Union a list of clashable info slots
cisUnions :: [Clashable_info_slot] -> Slot_UpdateResult
cisUnions []              = Slot_UpdateSuccess IntMap.empty
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
 = ucis_helper cis1 (IntMap.assocs cis2)
    where ucis_helper :: Clashable_info_slot -> [(Literal,DependencySet)] -> Slot_UpdateResult
          ucis_helper cis l_ds_s =
             let (updateStatus,clashing_ds_s)
                  = foldr (\(l,ds) (upResult,clashingBps_s)
                           -> case upResult of
                               Slot_UpdateSuccess cis_ ->  (cisUpdate cis_ l ds,      clashingBps_s)
                               Slot_UpdateFailure ds_s ->  (cisUpdate cis  l ds, ds_s:clashingBps_s)
                                                                 -- we reuse the input Clashabe Info Slot
                          )
                          (Slot_UpdateSuccess cis,[])   l_ds_s
                 result = case clashing_ds_s of
                              []   -> updateStatus                                    -- is 'success'
                              ds_s -> Slot_UpdateFailure $ findEarliestSet ds_s
                                         where findEarliestSet = minimumBy compareBPSets
                                               compareBPSets ds1 ds2 = comparing dsMin ds1 ds2
             in
                result


-- Insert a piece of information in a clashable info slot

cisUpdate :: Clashable_info_slot -> Literal -> DependencySet -> Slot_UpdateResult
cisUpdate cis l ds  | isTop l     = Slot_UpdateSuccess cis
                    | isBottom l  = Slot_UpdateFailure ds
cisUpdate cis l ds  -- nominals, propositional symbols
 = case IntMap.lookup (negLit l) cis of
    Just ds2         -> Slot_UpdateFailure $ dsUnion ds ds2
    Nothing          -> Slot_UpdateSuccess $ IntMap.insertWith mergeDeps l ds cis
                         where mergeDeps d1 d2  = if dsMin d1 < dsMin d2 then d1 else d2
                                -- if the same information is caused by an earlier
                                -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

cisAddDeps :: DependencySet -> Slot_UpdateResult -> Slot_UpdateResult
cisAddDeps ds res_cis =
 case res_cis of
  Slot_UpdateSuccess cis -> Slot_UpdateSuccess $ IntMap.map (dsUnion ds) cis
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
-- example:
-- acp [a1,a2,a3] [b1,b2,b3] = [(a1,b2),(a1,b3),(a2,b1),(a2,b3),(a3,b1),(a3,b2)]
--
-- require : as and bs must be of the same size
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
