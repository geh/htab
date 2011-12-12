module HTab.Branch
(
Branch(..), BranchInfo(..), TodoList(..), BlockingMode(..),
createNewNode, createNewNomTestRelevance,
addFormulas, addAccFormula,
addToBlockedDias,
addDiaRuleCheck, addDownRuleCheck,
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
import qualified Data.IntMap as I

import HTab.DMap ( DMap )
import qualified HTab.DMap as D
import qualified HTab.DisjSet as DS
import HTab.CommandLine(Params(..))
import HTab.Formula
import HTab.Relations ( Relations(..), emptyRels, insertRelation, mergePrefixes,
                        successors, predecessors, linksFromTo )

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

type Literals           = DMap {- Prefix Literal -} DependencySet
type BoxConstraints     = DMap {- Prefix Rel -} [(Formula,DependencySet)]
type BranchingWitnesses = DMap {- Prefix Literal -} [PrFormula]
type EquivClasses = DS.DisjSet DS.Pointer
data BlockingMode =   PatternBlocking
                    | AnywhereBlocking
                    | ChainTwinBlocking
                    deriving (Eq,Show)

data Branch =
              Branch {
                 -- the premodel
                      literals :: Literals,
                        accStr :: Relations,
                 -- immediate rules constraints
                        boxFwd :: BoxConstraints,
                        boxBwd :: BoxConstraints,
                      univCons :: [(DependencySet,Formula)],
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- saturation of rules
                       diaRlCh :: IntMap {- Prefix -} (Set (Rel,Formula)),
                      downRlCh :: IntMap {- Prefix -} (Set Formula),
                        atRlCh :: Set Formula,
                     existRlCh :: Set Formula,
                 -- pattern blocking
                      patterns :: IntMap (Set Formula),
                 -- set of formulas true at each point of the premodel
                   prefToForms :: IntMap {- Prefix -} (Set Formula),
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: IntMap {- Prefix -} DependencySet,
                 -- prefix/nominal equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       nextNom :: Nom,
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
                { literals          = D.empty,
                  accStr            = emptyRels,
                  todoList          = emptyTodoList,
                  boxBwd            = D.empty,
                  boxFwd            = D.empty,
                  diaRlCh           = I.empty,
                  downRlCh          = I.empty,
                  atRlCh            = Set.empty,
                  existRlCh         = Set.empty,
                  downVarRelevantCh = Map.empty,
                  patterns          = I.empty,
                  univCons          = [],
                  lastPref          = 0,
                  nextNom           = maxNom encoding_ + 4,
                  prefToForms       = I.empty,
                  prToDepSet        = I.empty,
                  brWitnesses       = D.empty,
                  nomPrefClasses    = DS.mkDSet,
                  inputLanguage     = fLang,
                  blockMode         = blockingMode,
                  blockedDias       = I.empty,
                  prefParent        = I.empty,
                  relevantNominals  = set $ relevantNoms fLang,
                  relInfo           = relInfo_,
                  encoding          = encoding_
                }
 where blockingMode
        | languagePast fLang || relInfo_ `oneIs` Symmetric = ChainTwinBlocking
        | patternBlocking p = PatternBlocking
        | otherwise         = AnywhereBlocking

instance Show Branch where
 show br = concat
  [  show (inputLanguage br),
     "\nLiterals:", showIMap (\v -> "(" ++ showMap_lits v ++ ")") "\n " (literals br),
     "\nRelations: ", show (accStr br),
     "\nBoxes: ", showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (boxFwd br),
     "\nBoxes inv: ", showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (boxBwd br),
     "\n", show (todoList br),
     "\nWitnesses: ",
     showIMap (\v -> "(" ++ showMap_lits2 v ++ ")") "\n " (brWitnesses br),
     "\nDia rule chart: ", show (diaRlCh br),
     "\nIndividual patterns: ", show (patterns br),
     "\nDown rule chart: ", show (downRlCh br),
     "\n@ rule chart: ", show (list $ atRlCh br),
     "\nExist rule chart: ", show (list $ existRlCh br),
     "\nDown var relevant chart: ", show (downVarRelevantCh br),
     "\nUniv constraints: ", show (univCons br),
     "\nPrefix to dependency set: ", showIMap  dsShow "\n " (prToDepSet br),
     "\nPrefix to formulas: ", showIMap  (show . Set.toList) "\n " (prefToForms br),
     "\nParent: ", show (prefParent br),
     "\nBlocking mode: ", show (blockMode br),
     "\nPrefix-Nominal classes : ", showMap ", " (nomPrefClasses br),
     "\nModel-relevant nominals : ", unwords $ map showLit $ list $ relevantNominals br,
     "\nlastPref : ", show (lastPref br),
     " nextnom : ", showLit (nextNom br)
  ]
   where
    showIMap :: (a -> String) -> String -> IntMap a -> String
    showIMap vShow sep
     = I.foldWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) ""
    showMap sep = Map.foldrWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ show v )) ""
    showMap_lits = I.foldWithKey (\l d -> (++ showLit l ++ " " ++ dsShow d  ++ ", ")) ""
    showMap_lits2 = I.foldWithKey (\l fs -> (++ showLit l ++ " :" ++ show fs ++ ", ")) ""
    showMap_rel
     = I.foldWithKey (\r dxs -> (++ "-" ++ showRel r ++ "-> " ++ show dxs ++ ", ")) ""

data TodoList= TodoList{disjTodo :: Set PrFormula,
                         diaTodo :: Set PrFormula,
                       existTodo :: Set PrFormula,
                          atTodo :: Set PrFormula,
                        downTodo :: Set PrFormula,
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
     let (Just innerMap) = D.lookup1 pr (brWitnesses br)
     in

     case D.lookup pr l (brWitnesses br) of
      Just _
        -> let innerMap2 = I.delete l innerMap
               newBrW = D.insert1 pr innerMap2 (brWitnesses br)
               newBr = br{brWitnesses = newBrW}
           in
            newBr -- forget  the disjunctions, they are really satisfied
      Nothing
       -> case D.lookup pr (negLit l) (brWitnesses br) of
           Just fs
             -> let innerMap2 = I.delete (negLit l) innerMap
                    newBrW = D.insert1 pr innerMap2 (brWitnesses br)
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
   E _        -> BranchOK $ addToTodo pf br
   At _ _     -> BranchOK $ addToTodo pf br
   Down _ _   -> BranchOK $ addToTodo pf br
   Lit l | isPositiveNom l -> addToLiterals pr ds l $ addToTodo pf br
   Lit l                   -> addToLiterals pr ds l br

putAwayDisjunction :: Params -> PrFormula -> Branch -> BranchInfo
putAwayDisjunction p pf@(PrFormula pr ds f@(Dis fs)) br
 | lazyBranching p && blockMode br /= ChainTwinBlocking
  = case reduceDisjunctionProposeLazy br pr fs of
     Contradiction dsClash -> BranchClash br pr (dsUnion ds dsClash) f
     Triviality -> BranchOK br
     Reduced new_ds disjuncts mProposed
      -> let fNew = PrFormula pr (dsUnion ds new_ds) (Dis disjuncts)
              -- TODO if there was no reduction, leave ds
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
 = case D.lookup1 pr (brWitnesses br) of
    Nothing -> let newBrW = D.insert pr lit pfs (brWitnesses br)
               in BranchOK br{brWitnesses = newBrW}
    Just innerMap
     -> case I.lookup lit innerMap of
        -- assume this is the only place where l or (negLit l) occur
         Nothing -> let newInner = I.insert lit pfs innerMap
                        newBrW = D.insert1 pr newInner (brWitnesses br)
                    in BranchOK br{brWitnesses = newBrW}
         Just fs -- assume the test was already done
          -> let newInner = I.insert lit (pfs++fs) innerMap
                 newBrW = D.insert1 pr newInner (brWitnesses br)
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
         At _ _             -> utodo{   atTodo = Set.insert pf (   atTodo utodo)}
         Down _ _           -> utodo{ downTodo = Set.insert pf ( downTodo utodo)}
         Lit l
          | isPositiveNom l -> utodo{mergeTodo = Set.insert (ds,p,DS.Nominal l)
                                                            (mergeTodo utodo)}
         _                  -> error $ "addToTodo: " ++ show f2
   alreadyDone =
    case f2 of
     E  _               -> existAlreadyDone br f2
     At _ _             -> atAlreadyDone br f2
     Down _ _           -> downAlreadyDone br pf
     Dia  _ _           -> False -- test happens when the todo list is processed
     Dis _              -> False -- test happens when the todo list is processed
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
  where toAdd = get [] pr (blockedDias br)
        br2 = br{blockedDias = I.delete pr $ blockedDias br}

addToBlockedDias :: PrFormula -> Branch -> BranchInfo
addToBlockedDias f@(PrFormula pr _ _) br
 = BranchOK br{blockedDias = I.insertWith (++) ur [f] (blockedDias br)}
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
     DS.Nominal _   -> BranchOK $ addClassDeps ur1 fDs $ br { nomPrefClasses = classes3 }
                         -- nominal not yet in the equivalence classes
     DS.Prefix ur2
      | ur1 == ur2 -> BranchOK $ addClassDeps ur1 fDs br
      | otherwise
         ->
          let
           oldUr           = max ur1 ur2
           newUr           = min ur1 ur2
           literalSlots    = mapMaybe (\ur -> D.lookup1 ur (literals br)) [ur1,ur2]
           currentDeps     = dsUnions $ fDs:(map (findDeps br) [ur1,ur2])
           newPrToDepSet   = I.insert newUr currentDeps (prToDepSet br)
           newUrfatherSlot = lsAddDeps currentDeps $ lsUnions literalSlots
          in
           case newUrfatherSlot of
            SlotUpdateFailure clashingDeps ->
             let newBr = br{nomPrefClasses = classes3} in
             BranchClash newBr pr (dsUnion clashingDeps currentDeps) (neg taut)

            SlotUpdateSuccess slot ->
             let
              newLiterals = I.delete oldUr $ I.insert newUr slot $ literals br

              -- structures that merge
              newPrefToForms  = moveInMap (prefToForms br) oldUr newUr Set.union
              newBoxFwd = D.moveInnerDataDMapPlusDeps fDs (boxFwd br) oldUr newUr
              newBoxBwd = D.moveInnerDataDMapPlusDeps fDs (boxBwd br) oldUr newUr
              newAccStr       = mergePrefixes (accStr br) oldUr newUr fDs
              newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
              newBlockedDias  = moveInMap (blockedDias br) oldUr newUr (++)
              (newBrWit,unwitnessed) = mergeWitnesses oldUr newUr slot (brWitnesses br)

              -- structures that combine
              mapBoxFwd = map (\idx -> get I.empty idx (boxFwd br) ) [ur1,ur2]
              mapAccFwd = map (successors (accStr br)) [ur1,ur2]
              forms1    = concatMap (boxRule currentDeps) $ combine mapBoxFwd mapAccFwd

              mapBoxBwd = map (\idx -> get I.empty idx (boxBwd br) ) [ur1,ur2]
              mapAccBwd = map (predecessors (accStr br)) [ur1,ur2]
              forms2    = concatMap (boxRule currentDeps) $ combine mapBoxBwd mapAccBwd

              formulasToAdd = nubAndMergeDeps $ forms1 ++ forms2 ++ unwitnessed

              newBr           = br{nomPrefClasses = classes3,
                                   boxFwd         = newBoxFwd,
                                   boxBwd         = newBoxBwd,
                                   accStr         = newAccStr,
                                   prToDepSet     = newPrToDepSet,
                                   prefToForms    = newPrefToForms,
                                   diaRlCh        = newDiaRlCh,
                                   blockedDias    = newBlockedDias,
                                   literals       = newLiterals,
                                   brWitnesses    = newBrWit}
             in
              addFormulas p formulasToAdd newBr

mergeWitnesses :: Prefix -> Prefix -> LiteralSlot -> BranchingWitnesses
                   -> (BranchingWitnesses, [PrFormula])
mergeWitnesses oldUr newUr urfatherSlot brWits
 =( D.insert1 newUr newDest2 ( D.delete oldUr brWits ), toAdd1 ++ toAdd2 )
  where
   srcInnerMap  = get I.empty oldUr brWits
   destInnerMap = get I.empty newUr brWits
   (newDest1,toAdd1) = mergeWitnessesWitnessesMap srcInnerMap destInnerMap
   (newDest2,toAdd2) = mergeWitnessesAgainstLiterals newDest1 urfatherSlot

mergeWitnessesWitnessesMap :: IntMap [PrFormula] -> IntMap [PrFormula]
                               -> (IntMap [PrFormula], [PrFormula])
mergeWitnessesWitnessesMap srcWitMap destWitMap
 = foldr go (destWitMap,[]) $ I.assocs srcWitMap
   where
      go (l,fs) (destMap,toAddAgain)
         = case I.lookup l destMap of
            Just fs2 -> (I.insert l (fs2++fs) destMap, toAddAgain)
            Nothing
             -> case I.lookup (negLit l) destMap of
       -- (negLit l) is just one bit away from l in the map, but we don't use it
                  Just fs2 -> (I.delete (negLit l) destMap, fs++fs2++toAddAgain)
                  Nothing ->  (I.insert l fs destMap, toAddAgain)

mergeWitnessesAgainstLiterals :: IntMap [PrFormula] -> LiteralSlot
                                   -> (IntMap [PrFormula],[PrFormula])
mergeWitnessesAgainstLiterals  witMap ls
 = foldr go (witMap,[]) $ I.assocs witMap
   where
    go (lit,fs) (destMap,toAddAgain)
      | lit `I.member` ls = (I.delete lit destMap,toAddAgain)
      | negLit lit `I.member` ls = (I.delete lit destMap,fs++toAddAgain)
          -- same remark as above
      | otherwise = (destMap,toAddAgain)

nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added
-- to a branch as several prefixed formulas with different branching dependencies.
-- This functions takes a list of prefixed formulas, looks which inner formulas
-- are the same and merge their branching dependencies.
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
       newMap = I.insertWith Set.union pr (Set.singleton f) currentPtf

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
findDeps br pr = get dsEmpty pr (prToDepSet br)

addClassDeps :: Prefix -> DependencySet -> Branch -> Branch
addClassDeps pr ds br = br { prToDepSet = I.insertWith dsUnion pr ds (prToDepSet br) }

inSameClass :: Branch -> Prefix -> Int -> Bool
inSameClass br p n
 = case fst $ DS.find (DS.Nominal (atom n)) (nomPrefClasses br) of
    DS.Nominal _ -> False
    DS.Prefix p2 -> getUrfather br (DS.Prefix p) == p2

{-     box-related constraints     -}

boxRule :: DependencySet
            -> (IntMap {- Rel -} [(Formula,DependencySet)],
                IntMap {- Rel -} [(Prefix,DependencySet)] )
            -> [PrFormula]
boxRule deps (mapBox, mapAcc)
 = [PrFormula p (dsUnions [deps,ds1,ds2]) f |
                      r1 <- I.keys mapBox,
                      r2 <- I.keys mapAcc,
                      r1 == r2,
                      (f,ds1) <- (I.!) mapBox r1,
                      (p,ds2) <- (I.!) mapAcc r2     ]

addBoxConstraint :: Prefix -> Rel -> Formula -> DependencySet -> Params -> Branch
                     -> BranchInfo
addBoxConstraint pr_ r f ds p br
 | boxAlreadyDone br pr (r,f) = BranchOK br
 | isForward r
    = let newBr = br{boxFwd = updateBoxConstr pr r f ds (boxFwd br)}
          succs  = get [] r $ successors (accStr br) pr
          toAdd = fromSym ++ fromTrans ++ fromBox
          fromTrans
           = if isTransitive (relInfo br) r
              then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) succs
              else []
          fromSym = [PrFormula pr ds $ Box (invRel r) f | isSymmetric (relInfo br) r]
          fromBox = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) succs
    -- todo check again with new pattern, create successor if new pattern not realized
      in
         addFormulas p toAdd newBr

 | otherwise
   = let newBr = br{boxBwd = updateBoxConstr pr (atom r) f ds (boxBwd br)}
         preds = get [] (atom r) $ predecessors (accStr br) pr
         toAdd = fromTrans ++ fromBox
          -- no symApplications cause inv rewritten as forward during parsing
         fromTrans
          = if isTransitive (relInfo br) (atom r)
             then map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) (Box r f)) preds
             else []
         fromBox = map (\(pr2,ds2) -> PrFormula pr2 (dsUnion ds ds2) f) preds
     in
        addFormulas p toAdd newBr
 where pr = getUrfather br (DS.Prefix pr_)

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> BoxConstraints
                    -> BoxConstraints
updateBoxConstr p1_ r_ f_ ds_ boxConstr_ =
  case I.lookup p1_ boxConstr_ of
    Nothing       -> I.insert p1_ (I.singleton r_ [(f_,ds_)]) boxConstr_
    Just innerMap ->
       case I.lookup r_ innerMap of
        Nothing
         -> I.insert p1_ (I.insert r_ [(f_,ds_)] innerMap)                boxConstr_
        Just innerInnerList
         -> I.insert p1_ (I.insert r_ ((f_,ds_):innerInnerList) innerMap) boxConstr_

boxAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
boxAlreadyDone br ur (r,f)
 | isForward r  = case ( do inner <- I.lookup ur (boxFwd br)
                            boxes <- map fst <$> I.lookup r inner
                            return (f `elem` boxes) ) of
                    Just True -> True
                    _         -> False
 | otherwise    = case ( do inner <- I.lookup ur (boxBwd br)
                            boxes <- map fst <$> I.lookup (atom r) inner
                            return (f `elem` boxes) ) of
                    Just True -> True
                    _         -> False

-- accessibility Formulas

addAccFormula :: Params -> (DependencySet,Rel,Prefix,Prefix) -> Branch -> BranchInfo
addAccFormula p (ds, r, p1_, p2_) br
 | isBackwards r = addAccFormula p (ds, invRel r, p2_, p1_) br
 | otherwise -- forward
   = addFormulas p toAdd newBr
     where
      toAdd = transApplications ++ boxApplications
      transApplications =
       if isTransitive (relInfo br) r
        then
          (  ( map (\(f,ds2) -> PrFormula p2 (dsUnion ds ds2) (Box r f)) toSendFwd )
          ++ ( map (\(f,ds2) -> PrFormula p1 (dsUnion ds ds2) (Box r f)) toSendBwd )  )
        else []
      boxApplications =
          (   ( map (\(f,ds2) -> PrFormula p2 (dsUnion ds ds2) f) toSendFwd )
           ++ ( map (\(f,ds2) -> PrFormula p1 (dsUnion ds ds2) f) toSendBwd )  )
      p1 = getUrfather br (DS.Prefix p1_)
      p2 = getUrfather br (DS.Prefix p2_)
      toSendFwd = get [] r $ get I.empty p1 (boxFwd br)
      toSendBwd = get [] r $ get I.empty p2 (boxBwd br)
      newBr = scheduleInclusionRule p1 p2 r ds $ insertRelationBranch br p1 r p2 ds


scheduleInclusionRule :: Prefix -> Prefix -> Rel -> DependencySet -> Branch -> Branch
scheduleInclusionRule p1 p2 r ds br -- todo get all included
 = if null toschedule
    then br
    else br{todoList = newTodoList}
   where parentss = case Map.lookup r (relInfo br) of
                      Nothing -> []
                      Just props -> [ rs | SubsetOf rs <- props]
         toschedule = map (\parents -> (ds,p1,p2,parents)) $ filter (not . alreadyDone)
                          parentss
         alreadyDone = any (`elem` linksFromTo (accStr br) p1 p2)
         utodo       = todoList br
         newTodoList = utodo{roleIncTodo = Set.fromList toschedule
                                           `Set.union` roleIncTodo utodo}

insertRelationBranch :: Branch -> Prefix -> Rel -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 r p2 ds
 = br{accStr = insertRelation (accStr br) p1 r p2 ds}


{- blocking conditions -}

isNotBlocked :: Branch -> PrFormula -> Bool
isNotBlocked br pf@(PrFormula pr _ _) =
 case blockMode br of
   PatternBlocking
     -> not $ patternBlocked br pf
   AnywhereBlocking
     -> not $ any isSubsumer labels
         where ur = getUrfather br (DS.Prefix pr)
               fs = formulasOf br ur
               isSubsumer fs_ = fs `Set.isSubsetOf` fs_
               labels = map snd $ takeWhile ((< ur).fst) $  ascPrefToForm br
   ChainTwinBlocking
     -> isNotChainTwinBlocked br pr

isNotChainTwinBlocked :: Branch -> Prefix -> Bool
isNotChainTwinBlocked br pr
 = not $ test2equal $ map (formulasOf br) (getAllParents br pr)

getAllParents :: Branch -> Prefix -> [Prefix]
-- getAllParents up to one that has an input nominal
getAllParents br pr = getUrfather br (DS.Prefix pr):rest
 where rest = case I.lookup pr (prefParent br) of
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
    ChainTwinBlocking ->  case findModelReprChain br pr of
                                 Nothing   -> False
                                 Just repr -> repr == pr
isInTheModel _ _ = False

relationIsInTheModel :: Branch -> (Prefix,Rel,Prefix) -> Bool
relationIsInTheModel br (p1,_,p2)
 = case blockMode br of
     PatternBlocking    -> True
     AnywhereBlocking   -> True
     ChainTwinBlocking  -> hasIdentityUrfather br p1 && hasIdentityUrfather br p2
   where hasIdentityUrfather br_ pr_
          = case findModelReprChain br_ pr_ of {Nothing -> False ; _ -> True }

getModelRepresentative :: Branch -> Prefix -> Prefix
getModelRepresentative br pr
 = case blockMode br of
    PatternBlocking -> ur
    AnywhereBlocking-> ur
    ChainTwinBlocking -> fromMaybe (error $ "interesting counter example " ++ show pr)
                                  $ findModelReprChain br pr
   where ur = getUrfather br (DS.Prefix pr)

findModelReprChain :: Branch -> Prefix -> Maybe Prefix
findModelReprChain br pr
 = go br pr 0
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
patternBlocked br f = not $ I.null $ I.filter lookForSuperset (patterns br)
 where lookForSuperset = Set.isSubsetOf (patternOf br f)

-- given a p:<r>f formula, return the pattern:
-- { f } U { f' | p:[r]f' in branch }
-- r has to be forward
patternOf :: Branch -> PrFormula -> Set Formula
patternOf br (PrFormula pr _ (Dia r f))
 = Set.insert f boxes
    where ur = getUrfather br (DS.Prefix pr)
          boxes = if isTransitive (relInfo br) r
                   then boxesOf br ur r
                          `Set.union` (Set.map (Box r) $ boxesOf br ur r)
                   else boxesOf br ur r

patternOf _ _ = error "patternOf called with a non diamond formula"

boxesOf :: Branch -> Prefix -> Rel -> Set Formula
boxesOf br p r
 = set $ map fst $ get [] r $ get I.empty p (boxFwd br)

findByPattern :: Branch -> Set Formula -> Prefix
findByPattern br pattern
 | blockMode br == PatternBlocking  =
       head $ map fst
            $ filter (\(_,pat2) -> pattern `Set.isSubsetOf` pat2)
            $ I.toList $ patterns br
 | blockMode br == AnywhereBlocking =
       head $ map fst
            $ filter (\(_,pat2) -> pattern `Set.isSubsetOf` pat2)
            $ I.toList $ prefToForms br
 | otherwise = error "findByPattern called with ChainTwinBlocking"

-- maybe should get the urfather of given prefix,
-- so that the caller functions won't have to do it
formulasOf :: Branch -> Prefix -> Set Formula
formulasOf br p = get Set.empty p (prefToForms br)

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

addParentPrefix :: Prefix -> Prefix -> Branch -> BranchInfo
addParentPrefix son father br
 = BranchOK br{prefParent = I.insert son father (prefParent br)}

{-     modifications done by rule application     -}

addDiaRuleCheck :: Prefix -> (Rel,Formula) -> Prefix -> Branch -> BranchInfo
addDiaRuleCheck pr (r,f) newPr br =
  BranchOK br2
   where pattern = patternOf br (PrFormula ur dsEmpty (Dia r f))
         br1 = case blockMode br of
                PatternBlocking ->
                 br{patterns = I.insert newPr pattern (patterns br)}
                _ -> br
         br2 = br1{diaRlCh=I.insertWith Set.union ur (Set.singleton (r,f)) (diaRlCh br1)}
         ur = getUrfather br (DS.Prefix pr)

diaAlreadyDone :: Branch -> PrFormula -> Bool
diaAlreadyDone b (PrFormula p _ (Dia r f)) =
  case I.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member (r,f) fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ = error "dia already done : wrong formula kind"
--

addDownRuleCheck :: Prefix -> Formula -> Branch -> BranchInfo
addDownRuleCheck pr f br =
  BranchOK br{downRlCh=I.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

downAlreadyDone :: Branch -> PrFormula -> Bool
downAlreadyDone b (PrFormula p _ f@(Down _ _)) =
  case I.lookup ur (downRlCh b) of
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

createNewNomTestRelevance :: Formula -> Branch -> BranchInfo
createNewNomTestRelevance f br
 = BranchOK
    br{nextNom = nextNom br + 4,
       relevantNominals = if relevant
                           then Set.insert newNom (relevantNominals br)
                           else relevantNominals br,
       downVarRelevantCh = newDVRC
      }
   where (relevant, newDVRC) = doMemoize checkIfVarNegated f (downVarRelevantCh br)
         newNom = nextNom br

-- preparation of the branch at the beginning of the calculus:
--  - add the input formula at prefix 0
--  - add a nominal formula at a fresh prefix for each nominal of the input language
--    (even if the nominal was filtered out during lexical normalisation)
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
          newLiterals = foldr (\(pr,n) -> D.insert pr n dsEmpty)
                              D.empty
                              (zip [1..] ns)
          br2 = br{nomPrefClasses = newClasses,
                           literals = newLiterals}
          br3 = foldr (\(pr,n) -> bookKeepFormula p (PrFormula pr dsEmpty (Lit n)))
                      br2
                      (zip [1..] ns)

{- functions for literals associated to prefixes -}

data UpdateResult = UpdateSuccess Literals | UpdateFailure DependencySet

addToLiterals :: Prefix -> DependencySet -> Literal -> Branch -> BranchInfo
addToLiterals pr_ ds1 l br
  = case updateMap (literals br) pr ds l of
     UpdateSuccess ls  -> BranchOK br{literals = ls}
     UpdateFailure dsf -> BranchClash br pr dsf (Lit l)
   where (pr,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr_)
         ds = ds1 `dsUnion` ds2

-- Insert a literal into a literal slot

updateMap :: Literals -> Prefix -> DependencySet -> Literal -> UpdateResult
updateMap ls  _  ds l | isTop l    = UpdateSuccess ls
                      | isBottom l = UpdateFailure ds
updateMap ls pre ds l
  = case I.lookup pre ls of
     Nothing   -> UpdateSuccess $ I.insert pre (I.singleton l ds) ls
     Just slot ->
       case lsUpdate slot l ds of
        SlotUpdateSuccess updatedSlot -> UpdateSuccess $ I.insert pre updatedSlot ls
        SlotUpdateFailure failureDeps -> UpdateFailure failureDeps


type LiteralSlot = IntMap {- Literal -} DependencySet
data SlotUpdateResult =   SlotUpdateSuccess LiteralSlot
                        | SlotUpdateFailure DependencySet


-- Union a list of literals slots
lsUnions :: [LiteralSlot] -> SlotUpdateResult
lsUnions []              = SlotUpdateSuccess I.empty
lsUnions [ls]            = SlotUpdateSuccess ls
lsUnions (ls1:ls2:tl)
 = case lsUnion ls1 ls2 of
     failure@(SlotUpdateFailure _) -> failure
     SlotUpdateSuccess newLs       -> lsUnions (newLs:tl)

-- Union two literals slots

-- if there is a clash, the result reports the set of dependencies whose
-- earliest dependency is the earliest among all dep. sets that caused the clash
lsUnion :: LiteralSlot -> LiteralSlot -> SlotUpdateResult
lsUnion ls1 ls2
 = uls_helper ls1 (I.assocs ls2)
    where uls_helper :: LiteralSlot -> [(Literal,DependencySet)]
                           -> SlotUpdateResult
          uls_helper ls l_ds_s =
           let (updateStatus,clashing_ds_s)
                = foldr
                   (\(l,ds) (upResult,clashingBps_s)
                    -> case upResult of
                        SlotUpdateSuccess ls_  -> (lsUpdate ls_ l ds,      clashingBps_s)
                        SlotUpdateFailure ds_s -> (lsUpdate ls  l ds, ds_s:clashingBps_s)
                           -- we reuse the input LiteralSlot
                   )
                   (SlotUpdateSuccess ls,[])   l_ds_s
           in
            case clashing_ds_s of
              []   -> updateStatus      -- is 'success'
              ds_s -> SlotUpdateFailure $ findEarliestSet ds_s
                       where findEarliestSet = minimumBy compareBPSets
                             compareBPSets ds1 ds2 = comparing dsMin ds1 ds2


-- Insert a piece of information in a literal slot

lsUpdate :: LiteralSlot -> Literal -> DependencySet -> SlotUpdateResult
lsUpdate ls l ds  | isTop l     = SlotUpdateSuccess ls
                  | isBottom l  = SlotUpdateFailure ds
lsUpdate ls l ds  -- nominals, propositional symbols
 = case I.lookup (negLit l) ls of
    Just ds2 -> SlotUpdateFailure $ dsUnion ds ds2
    Nothing  -> SlotUpdateSuccess $ I.insertWith mergeDeps l ds ls
                 where mergeDeps d1 d2  = if dsMin d1 < dsMin d2 then d1 else d2
                  -- if the same information is caused by an earlier
                  -- branching, only keep the information of the earliest
                  -- set of dependencies

-- Other functions related to literals slots

lsAddDeps :: DependencySet -> SlotUpdateResult -> SlotUpdateResult
lsAddDeps ds res_ls =
 case res_ls of
  SlotUpdateSuccess ls -> SlotUpdateSuccess $ I.map (dsUnion ds) ls
  failure              -> failure



lsQuery :: Branch -> Prefix -> Literal -> Maybe (Bool,DependencySet)
-- Output : Nothing    = nevermind
--          Just True  = already there
--          Just False = contrary there
lsQuery _ _ l | isTop l    = Just (True,dsEmpty)
              | isBottom l = Just (False,dsEmpty)
lsQuery br pr l
  = case D.lookup pr l (literals br) of
      Just ds    -> Just (True,ds)
      Nothing    -> case D.lookup pr (negLit l) (literals br) of
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
       | otherwise -> Reduced ds disjuncts proposed
            -- what if not reduced ? and no proposed witness ?
   where
      ur = getUrfather br (DS.Prefix pr)
      go _ Nothing = Nothing
      go l@(Lit current) (Just (disjuncts,ds_,proposed))
       = case (lsQuery br ur current, proposed) of
          (Just (True,_)    ,_) -> Nothing
          (Just (False,ds2) ,_) -> Just (disjuncts,dsUnion ds_ ds2, proposed)
          (Nothing, Nothing)
           -> if isPositiveNom current
               then Just (Set.insert l disjuncts,ds_,Nothing)
                    -- no lazy branching with positive nominals
               else case D.lookup ur (negLit current) (brWitnesses br) of
                      -- if current is a negated nominal,
                      -- we know the "just" case is impossible
                     Just _  -> Just (Set.insert l disjuncts,ds_,Nothing)
                      -- there's an opposed witness
                     Nothing -> Just (Set.insert l disjuncts,ds_, Just current)
                      -- propose for witness
          _ {- already a proposed witness -}
           -> Just (Set.insert l disjuncts,ds_,proposed)
      go f (Just (disjuncts,ds_,proposed)) = Just (Set.insert f disjuncts, ds_,proposed)


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

combine :: [a] -> [b] -> [(a,b)]
combine [] _  = error "combine: first list empty"
combine _  [] = error "combine: second list empty"
combine as bs = [(a,b) | (idxA,a) <- zip [(0::Int)..] as,
                         (idxB,b) <- zip [(0::Int)..] bs,
                         idxA /= idxB]

moveInMap :: IntMap b -> Int -> Int -> (b -> b -> b) -> IntMap b
moveInMap m origKey destKey mergeF
 = result
   where mOrigValue = I.lookup origKey m
         prunedM    = I.delete origKey m
         result = case mOrigValue of
                   Nothing -> m
                   Just origValue -> I.insertWith mergeF destKey origValue prunedM

doMemoize :: Ord a => (a -> b) -> a -> Map.Map a b -> (b, Map.Map a b)
doMemoize f e m = case Map.lookup e m of
                   Nothing     -> let result = f e in (result, Map.insert e result m)
                   Just result -> (result, m)

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList

get :: a -> Int -> IntMap a -> a
get = I.findWithDefault
