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
addDiaRuleCheck, addDownRuleCheck, addDiffRuleCheck,
addParentPrefix,
BranchData(..),branch_depth,
emptyBranch,initialBranchStateFor,
addZeroInPath,incPathHead,prefixes,
reduceDisjunctionAgainstBranch,
getUrfather, getUrfatherAndDeps, isInTheModel,
getModelRepresentative, hasUnivMod, hasDiffMod, isNotBlocked,
calculateStepInfo, BlockingMode(..), diaAlreadyDone,
downAlreadyDone, incPropSymbol, incNomSymbol,
ReducedDisjunct(..)
) where

import Control.Monad.State(StateT, MonadState, get)
import Data.List(delete, nub, minimumBy)

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set

import qualified HTab.DisjSet as DS

import Data.Maybe(fromJust)

import HTab.Statistics(Statistics)
import HTab.CommandLine(CmdLineParams, unitProp)

import HTab.Formula

import HTab.DMap
import HTab.Base(moveInMap, almostCartesianProduct, doMemoize)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix BranchingPrefixes Formula

type Clashable_info   = Map.Map Prefix (Map.Map Atom (Bool,BranchingPrefixes))
type Conj_structure   = Set.Set PrFormula
type Disj_structure   = Set.Set PrFormula
type Dia_structure    = Set.Set PrFormula
type At_structure     = Set.Set PrFormula
type Down_structure   = Set.Set PrFormula
type Exist_structure  = Set.Set PrFormula
type Diff_structure   = Set.Set PrFormula
type Acc_structure    = DMap Prefix Rel [(BranchingPrefixes,Prefix )]
type Box_constraints  = DMap Prefix Rel [(BranchingPrefixes,Formula)]

type Dia_rule_chart    = Map.Map Prefix (Set.Set Formula)
type Down_rule_chart   = Map.Map Prefix (Set.Set Formula)
type At_rule_chart     = Set.Set Formula
type Exist_rule_chart  = Set.Set Formula
type Diff_Dia_rule_chart  = Map.Map Formula (PropSymbol,Bool)
       -- maps D(phi) formulas to the prop symbol used to differentiate
       -- the current prefix from the one used to contain (phi) , and to a boolean indicating if a second
       -- different world has already been created
type DownVarRelevant_chart = Map.Map Formula Bool

type Diff_Box_constraints = [(BranchingPrefixes,Formula,NomSymbol)]

type Univ_constraints  = [(BranchingPrefixes,Formula)]    -- TODO try Map.Map Formula BranchingPrefixes for dependencies update

type PrefToFormulas    = Map.Map Prefix (Set.Set Formula)
type PrefToBrPrefs     = Map.Map Prefix BranchingPrefixes

type EquivClasses = DS.DisjSet DS.Pointer
type InclusionUrfathersMap = Map.Map Prefix Prefix

type AugmentedPrefixes = [Prefix] -- list of prefixes that received formulas during the previous step of the algorithm

type PrefixParent = Map.Map Prefix Prefix

data BlockingMode = InclusionBlockingGlobal | InclusionBlockingChain
 deriving (Eq,Show)

data Branch = Branch {clashStr :: Clashable_info,
                 -- pending formulas
                       conjStr :: Conj_structure,
                       disjStr :: Disj_structure,
                        diaStr :: Dia_structure,
                      existStr :: Exist_structure,
                         atStr :: At_structure,
                       downStr :: Down_structure,
                       diffStr :: Diff_structure, -- D
                 -- other data
                        accStr :: Acc_structure,
                     boxConstr :: Box_constraints,
                       diaRlCh :: Dia_rule_chart,    -- saturation of the diamond rule
                      downRlCh :: Down_rule_chart,   -- saturatino of the down-arrow rule
                        atRlCh :: At_rule_chart,     -- saturation of the @ rule
                     existRlCh :: Exist_rule_chart,  -- saturation of the exist rule
                      dDiaRlCh :: Diff_Dia_rule_chart, -- saturation of the diff diamond rule chart (D)
             downVarRelevantCh :: DownVarRelevant_chart,
                      univCons :: Univ_constraints,
                      dBoxCons :: Diff_Box_constraints, -- constraints of the (B) modality
                      lastPref :: Prefix,
                       lastNom :: Maybe NomSymbol,
                      lastProp :: Maybe PropSymbol,
                   prefToForms :: PrefToFormulas,
                   prToBrPrefs :: PrefToBrPrefs,
                nomPrefClasses :: EquivClasses,
                 inputLanguage :: LanguageInfo,
                     inclUrMap :: Maybe InclusionUrfathersMap,
                       incrPrs :: AugmentedPrefixes,
                     blockMode :: Maybe BlockingMode,
              defaultBlockMode :: BlockingMode,
                    prefParent :: PrefixParent,
              relevantNominals :: Set.Set NomSymbol}

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: LanguageInfo -> BlockingMode -> Bool -> Branch
emptyBranch l blockingMode immediate =
                Branch
                { clashStr= Map.empty::Clashable_info,
                  conjStr= Set.empty::Conj_structure,
                  disjStr= Set.empty::Disj_structure,
                  diaStr = Set.empty::Dia_structure,
                  existStr = Set.empty::Exist_structure,
                  atStr = Set.empty::At_structure,
                  downStr = Set.empty::Down_structure,
                  diffStr = Set.empty::Diff_structure,
                  accStr=Map.empty::Acc_structure,
                  boxConstr=Map.empty::Box_constraints,
                  diaRlCh=Map.empty::Dia_rule_chart,
                  downRlCh=Map.empty::Down_rule_chart,
                  atRlCh=Set.empty::At_rule_chart,
                  existRlCh=Set.empty::Exist_rule_chart,
                  dDiaRlCh = Map.empty::Diff_Dia_rule_chart,
                  downVarRelevantCh = Map.empty::DownVarRelevant_chart,
                  dBoxCons = [],
                  univCons=[],
                  lastPref = 0,
                  lastNom  = if null (languageNoms l) then Nothing else Just (maximum $ languageNoms l),   -- | TODO
                  lastProp = if null (languageProps l) then Nothing else Just (maximum $ languageProps l), -- |   avoid this
                  prefToForms= Map.empty::PrefToFormulas,
                  prToBrPrefs= Map.empty::PrefToBrPrefs,
                  nomPrefClasses= DS.mkDSet::EquivClasses,
                  inputLanguage = l,
                  inclUrMap = Nothing,
                  incrPrs = [],
                  blockMode = if immediate then Just blockingMode else Nothing,
                  defaultBlockMode = blockingMode,
                  prefParent = Map.empty::PrefixParent,
                  relevantNominals = Set.fromList $ languageNoms l
                }

instance Show Branch where
    show br = "Input language: " ++ show (inputLanguage br) ++
              "\nClashable formulas: " ++ prettyShowMap_ (clashStr br) (\v -> "(" ++ prettyShowMap_clashable v ++ ")") "\n " ++
              "\nConjunctions: "   ++ show (Set.toList $ conjStr br)  ++
              "\nDisjunctions: "   ++ show (Set.toList $ disjStr br)  ++
              "\nDiamonds: "       ++ show (Set.toList $ diaStr br)   ++
              "\nExists: "         ++ show (Set.toList $ existStr br) ++
              "\nAts: "            ++ show (Set.toList $ atStr br)    ++
              "\nDowns: "          ++ show (Set.toList $ downStr br)  ++
              "\nDiff exists: "    ++ show (Set.toList $ diffStr br)  ++
              "\nAccesibility: "    ++ prettyShowMap_ (accStr br) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n " ++
              "\nBox constraints: " ++ prettyShowMap_ (boxConstr br) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n " ++
              "\nDia rule chart: "  ++ prettyShowMap_ (diaRlCh br) (show . Set.toList) "\n " ++
              "\nDown rule chart: " ++ prettyShowMap_ (downRlCh br) (show . Set.toList) "\n " ++
              "\n@ rule chart: "   ++ show (Set.toList $ atRlCh br) ++
              "\nExist rule chart:" ++ show (Set.toList $ existRlCh br) ++
              "\nDiff dia rule chart: "  ++ prettyShowMap_ (dDiaRlCh br) show "\n " ++
              "\nDown var relevant chart: " ++ prettyShowMap_ (downVarRelevantCh br) show ", " ++
              "\nUniv constraints: "++ show (univCons br) ++
              "\nDiff box constraints: "++ show (dBoxCons br) ++
              "\nPrefix to branching prefixes: " ++ prettyShowMap_ (prToBrPrefs br) bps_show "\n " ++
              "\nPrefix to formulas: " ++ prettyShowMap_ (prefToForms br) (show . Set.toList) "\n " ++
              "\nParent: " ++ prettyShowMap (prefParent br) ", " ++
              "\nInclusion urfather map: "  ++ show (inclUrMap br) ++
              "\nIncreased prefixes: " ++ show (incrPrs br) ++
              "\nBlocking mode: " ++ show (blockMode br) ++
              "\nPrefix-Nominal classes : " ++ prettyShowMap (nomPrefClasses br) ", " ++
              "\nModel-relevant nominals : " ++ show (relevantNominals br)


prettyShowMap :: (Show x, Show y) => Map.Map x y -> String -> String
prettyShowMap dasMap separator = prettyShowMap_ dasMap show separator

prettyShowMap_ :: (Show x, Show y) => Map.Map x y -> (y -> String) -> String -> String
prettyShowMap_ dasMap valueShow separator
 = concat $ List.intersperse separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ Map.toList dasMap


prettyShowMap_clashable :: Map.Map Atom (Bool,BranchingPrefixes) -> String
prettyShowMap_clashable dasMap
 = concat $ List.intersperse ", " $ map (\(a,(bo,bp)) -> (if bo then "" else "!") ++ show a ++ " " ++ bps_show bp)
          $ Map.toList dasMap


prettyShowMap_rel_bps_x :: (Show a) => Map.Map Rel [(BranchingPrefixes,a)] -> String
prettyShowMap_rel_bps_x dasMap
 = concat $ List.intersperse ", " $ map (\(r,bp_x_s) -> (++) ("-" ++ show r ++ "-> ") $ concat $ List.intersperse ", "
                                           $ map (\(bp,x) -> show x ++ " " ++ bps_show bp) bp_x_s
                                        )
          $ Map.toList dasMap

--

{-
   "add formula(s)" functions, that handle all that is related
   to prefixes, nominals, and vId/nom rules
-}


addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> Bool -> BranchInfo
addFormulas clp br (hd:tl) afterClassMerge
       = case addFormula clp br hd afterClassMerge of
          BranchOK br2             -> addFormulas clp br2 tl afterClassMerge
          bi@(BranchClash _ _ _ _) -> bi

addFormulas _ br [] _ = BranchOK br


-- 3 main cases : adding a positive nominal, adding a disjunction, and otherwise.
addFormula :: CmdLineParams -> Branch -> PrFormula -> Bool -> BranchInfo
addFormula clp br f@(PrFormula pr newFormulaBprs f2@(Lit (PosLit (N (NomSymbol n))))) afterClassMerge
 | afterClassMerge = addFormulaBaseCase clp br f
 | not afterClassMerge
   = result
     where classes = nomPrefClasses br
           ((DS.Prefix rootP),classes2) = DS.find (DS.Prefix pr) classes

           (nomAncestor,classes3) = DS.find (DS.Nominal n) classes2

           involvedUrfathers = nub $ rootP : case nomAncestor of
                                              (DS.Nominal _) -> []            -- if the nominal was not yet in the classes
                                              (DS.Prefix rr) -> [rr]

           newUrfather = minimum involvedUrfathers
           exUrfathers = delete newUrfather involvedUrfathers

           classes4 = DS.union (DS.Prefix pr) (DS.Nominal n) classes3

           currentDependencies = bps_unions $ newFormulaBprs:(map (findDeps br) involvedUrfathers)
           newPrToBrPrefs = Map.insert newUrfather currentDependencies (prToBrPrefs br)

           -- get clashable formulas from ex urfathers, add the current dependencies, union and see if there is a clash or not
           mClashableInfoSlots = map        (\exUrfather -> Map.lookup exUrfather (clashStr br))  involvedUrfathers
           clashableInfoSlots  = concatMap  (\(mSlot) -> maybe [] (\slot -> [slot]) mSlot )       mClashableInfoSlots

           successOrFailure_newClashableSlotUrfather = addDepsToClashableSlot (clashableInfoSlotsUnions clashableInfoSlots) currentDependencies

           result = case successOrFailure_newClashableSlotUrfather of
                     Slot_UpdateFailure clashingDeps ->
{-clash-}                 BranchClash br pr (bps_union clashingDeps currentDependencies) f2 -- if clash, it's because of: clashable formulas deps, new formula desps, involved classes deps
                     Slot_UpdateSuccess urfatherSlot ->
{-success-}           let newClashable_info = let augmented = Map.insert newUrfather urfatherSlot (clashStr br) in
                                              foldr (\exUr cInfo -> Map.delete exUr cInfo) augmented exUrfathers

                          -- move formulas of the prefix-to-formula map  (to keep consistency for inclusion urfather calculation)
                          newPrefixToFormulas = if requireLocalFormulasTracking br
                                                  then foldr (\exUrfather prefToForms_ -> moveInMap prefToForms_ exUrfather newUrfather Set.union) (prefToForms br) exUrfathers
                                                  else (prefToForms br)

                          -- add the new formulas that should be sent to accessible prefixes to the branch
                          mapBoxs = map (\idx -> Map.findWithDefault (Map.empty) idx (boxConstr br) ) involvedUrfathers
                          mapAccs = map (\idx -> Map.findWithDefault (Map.empty) idx (accStr br)    ) involvedUrfathers
                          formulasToSend = concatMap (uncurry $ newFormulasToSend newFormulaBprs)
                                                     $ almostCartesianProduct mapBoxs mapAccs

                          -- move box constraint and accessibility relation data to the new urfather
                          newBoxConstr = foldr (\exUrfather boxStr_  -> moveInnerDataDMapPlusDeps newFormulaBprs boxStr_  exUrfather newUrfather)   (boxConstr br)  exUrfathers
                          newAccStr    = foldr (\exUrfather accStr_  -> moveInnerDataDMapPlusDeps newFormulaBprs accStr_  exUrfather newUrfather)   (accStr br)     exUrfathers

                          -- same for (<>) rule chart
                          newDiaRlCh = foldr (\exUrfather diaRlCh_ -> moveInMap diaRlCh_ exUrfather newUrfather Set.union)   (diaRlCh br) exUrfathers

                          nubbedNewFormulas = nubAndMergeDeps $ [PrFormula newUrfather newFormulaBprs f2] ++ formulasToSend
                          brUpdated         = br{nomPrefClasses = classes4,
                                                 boxConstr      = newBoxConstr,
                                                 accStr         = newAccStr,
                                                 prToBrPrefs    = newPrToBrPrefs,
                                                 prefToForms    = newPrefixToFormulas,
                                                 diaRlCh        = newDiaRlCh,
                                                 clashStr       = newClashable_info}
                         in
                             addFormulas clp brUpdated nubbedNewFormulas True

-- if Unit Propagation enabled : try to reduce disjunction
addFormula clp br pf@(PrFormula pr bprs disF@(Dis fs)) _
 = if not $ unitProp clp
    then addFormulaBaseCase clp br pf
    else case reduceDisjunctionAgainstBranch br pr fs of
           Triviality                 -> BranchOK br
           Contradiction brps_clash   -> BranchClash br pr (bps_union bprs brps_clash) disF
           Reduced new_bprs disjuncts -> addFormulaBaseCase clp br (PrFormula pr (bps_union bprs new_bprs) (Dis disjuncts))

addFormula clp br f _
 = addFormulaBaseCase clp br f

addFormulaBaseCase :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormulaBaseCase clp br f@(PrFormula pr bprs f2)
 = addFormula2 clp newBr fToAdd
    where
      (urfather,bprs2,newClasses) = getUrfatherAndDeps br (DS.Prefix pr)
      newBr = br{nomPrefClasses = newClasses}
      fToAdd = if urfather == pr -- always the case if we are in the modal language
                then f
                else (PrFormula urfather (bps_union bprs bprs2) f2)

addFormula2 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2 clp br pf@(PrFormula pr _ f) =
   addFormula3 clp updatedBr pf
 where
     br' = if requireLocalFormulasTracking br && forInclusion br f
             then addToPrefToForms br pf
             else br
     updatedBr  = addToAugmentedPrefixes pr br'

addFormula3 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula3 _ br pf@(PrFormula _ _ (Con _))
           = BranchOK $ br{conjStr = Set.insert pf (conjStr br)}

addFormula3 _ br pf@(PrFormula _ _ (Dis _))
           = BranchOK $ br{disjStr = Set.insert pf (disjStr br)}

addFormula3 clp br (PrFormula pr bprs (Box r f))
           = addBoxConstraint clp br pr r f bprs

addFormula3 _ br pf@(PrFormula pr _ f2@(Dia _ _))
           = BranchOK $ if diaAlreadyDone br pr f2
                          then br                  -- diamond rule saturation
                          else br{diaStr = Set.insert pf (diaStr br)}

addFormula3 clp br (PrFormula _ bprs (A f))
           = addUnivConstraint clp (block br) bprs f

addFormula3 clp br (PrFormula pr bprs (B f))
           = addDiffUnivConstraint clp (block br) bprs f pr

addFormula3 _ br pf@(PrFormula _ _ f2@(E _))
           = BranchOK $ if existAlreadyDone br f2  -- exist rule saturation
                         then br
                         else br{ existStr = Set.insert pf (existStr br),
                                 existRlCh = Set.insert f2 (existRlCh br)}

addFormula3 _ br pf@(PrFormula _ _ (D _))
           = BranchOK $ br{diffStr = Set.insert pf (diffStr br)}

addFormula3 _ br pf@(PrFormula _ _ f2@(At _ _))
           = BranchOK $ if atAlreadyDone br f2  -- at rule saturation
                         then br
                         else br{ atStr = Set.insert pf (atStr br),
                                 atRlCh = Set.insert f2 (atRlCh br)}

addFormula3 _ _ (PrFormula _ _ (Atv _ _)) = error "addFormula Atv : should not happen"

addFormula3 _ br pf@(PrFormula pr _ f2@(Down _ _))
           = BranchOK $ block $ if downAlreadyDone br pr f2
                                 then br                            -- down-arrow rule saturation
                                 else br{downStr =  Set.insert pf (downStr br)}

addFormula3 _ br (PrFormula pr bprs (Lit l)) = addAndUpdateMap br pr bprs l


{-    helper functions for equivalence class merge     -}

nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added to a branch
-- as several prefixed formulas with different branching dependencies. This functions takes
-- a list of prefixes formulas, looks which inner formulas are the same and merge their
-- branching dependencies.
nubAndMergeDeps prfs =  namd prfs (Map.empty::Map.Map (Prefix,Formula) BranchingPrefixes)

namd :: [PrFormula] -> Map.Map (Prefix,Formula) BranchingPrefixes -> [PrFormula]
namd ((PrFormula p bps f):prfs) theMap =
  namd prfs (Map.insertWith bps_union (p,f) bps theMap)

namd [] theMap = map (\((p,f),bps) -> PrFormula p bps f) (Map.assocs theMap)


{-
   Functions related to vId, nom, prefixes and nominals ...
-}

addToPrefToForms :: Branch -> PrFormula -> Branch
addToPrefToForms br (PrFormula pre _ f) =
  br{prefToForms = newMap}
 where currentPtf = prefToForms br
       newMap = Map.insertWith (Set.union) pre (Set.singleton f) currentPtf

isNominalUrfather :: Branch -> Prefix -> Bool
isNominalUrfather b p = DS.isRoot (DS.Prefix p) classes
                         where classes = nomPrefClasses b

getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather b p = u
                  where (u,_,_) = getUrfatherAndDeps b p

getUrfatherAndDeps :: Branch -> DS.Pointer -> (Prefix,BranchingPrefixes,EquivClasses)
getUrfatherAndDeps br p =
   if DS.isRoot p classes then defaultAnswer
                          else (ur,deps,newClasses)
  where classes = nomPrefClasses br
        (urfather, newClasses) = DS.find p classes
        (DS.Prefix ur) = urfather
        DS.Prefix unboxedP = p
        defaultAnswer = (unboxedP,bps_empty,classes)
        deps = findDeps br ur

findDeps :: Branch -> Prefix -> BranchingPrefixes
findDeps br pr = Map.findWithDefault bps_empty pr (prToBrPrefs br)

{-     box-related constraints     -}

newFormulasToSend :: BranchingPrefixes -> Map.Map Rel [(BranchingPrefixes,Formula)] -> Map.Map Rel [(BranchingPrefixes,Prefix)] -> [PrFormula]
newFormulasToSend deps mapBox mapAcc
 = [PrFormula p (bps_unions [deps,bps1,bps2]) f |
                      r1 <- Map.keys mapBox,
                      r2 <- Map.keys mapAcc,    r1 == r2,
                      (bps1,f) <- (Map.!) mapBox r1,
                      (bps2,p) <- (Map.!) mapAcc r2     ]

addBoxConstraint :: CmdLineParams -> Branch -> Prefix -> RelSymbol -> Formula -> BranchingPrefixes -> BranchInfo
addBoxConstraint clp br nonRepresentativePr (RelSymbol r) f bprs
 = addFormulas clp newBr
               ( map (\(bprs2,p) -> PrFormula p (bps_union bprs bprs2) f) accessibleBprsPrs )
               False
   where pr = getUrfather br (DS.Prefix nonRepresentativePr)
         newBr = br{boxConstr = updateBoxConstr pr r f bprs (boxConstr br)}
         updateBoxConstr p1_ r_ f_ bprs_ boxConstr_ =
           case Map.lookup p1_ boxConstr_ of
             Nothing       -> Map.insert p1_ (Map.singleton r_ [(bprs_,f_)]) boxConstr_
             Just innerMap -> case Map.lookup r_ innerMap of
                                Nothing             -> Map.insert p1_ (Map.insert r_ [(bprs_,f_)] innerMap)                boxConstr_
                                Just innerInnerList -> Map.insert p1_ (Map.insert r_ ((bprs_,f_):innerInnerList) innerMap) boxConstr_

         accessibleBprsPrs = Map.findWithDefault [] r $ Map.findWithDefault Map.empty pr (accStr br)  -- [(BranchingPrefixes,Prefix)]

addBoxConstraint _ _ _ (InvRelSymbol _) _ _ = error "inverse modality not handled"


addAccFormula :: CmdLineParams -> Branch -> AccFormula -> BranchInfo
addAccFormula clp br (AccFormula bprs (RelSymbol r) nonRepresentativeP1 p2)
 = addFormulas clp newBr
               ( map (\(bprs2,f) -> PrFormula p2 (bps_union bprs bprs2) f) formulasToSend )
               False
   where p1 = getUrfather br (DS.Prefix nonRepresentativeP1)
         newBr    =      br{accStr=updateAccStr p1 r bprs p2 (accStr br)}
         updateAccStr p1_ r_ bprs_ p2_ accStr_ =
          case Map.lookup p1_ accStr_ of
            Nothing       -> Map.insert p1_ (Map.singleton r_ [(bprs_,p2_)]) accStr_
            Just innerMap -> case Map.lookup r_ innerMap of
                               Nothing             -> Map.insert p1_ (Map.insert r_ [(bprs_,p2_)] innerMap)                accStr_
                               Just innerInnerList -> Map.insert p1_ (Map.insert r_ ((bprs_,p2_):innerInnerList) innerMap) accStr_
         formulasToSend = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p1 (boxConstr br) -- [(BranchingPrefixes,Prefix)]


addAccFormula _ _ (AccFormula _ (InvRelSymbol _) _ _ ) = error "inverse modality not handled"

{-  functions related to blocking conditions and model building -}

isNotBlocked :: Branch -> Prefix -> Bool
isNotBlocked br pr =
 case blockMode br of
   Nothing                      -> True
   Just InclusionBlockingGlobal -> let ur =  getUrfather br (DS.Prefix pr) in
                                   (getModelRepresentative br ur) == ur  -- i'm not happy to call this model related function
   Just InclusionBlockingChain  -> not $ isChainInclusionBlocked br pr

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


isInTheModel :: Branch -> Prefix -> Bool
isInTheModel br pr
 = case blockMode br of
    Nothing                      -> isNominalUrfather br pr -- could be just pr as well, but here we have a smaller model
    Just InclusionBlockingGlobal -> if isNominalUrfather br pr
                                       then (getModelRepresentative br pr) == pr
                                       else False
    Just InclusionBlockingChain  -> if isNominalUrfather br pr
                                       then (getModelRepresentative br pr) == pr
                                       else False


getModelRepresentative :: Branch -> Prefix -> Prefix  -- which is also an inclusion representative
getModelRepresentative br pr
 = case blockMode br of
    Nothing                      -> getUrfather br (DS.Prefix pr)
    Just InclusionBlockingGlobal -> giu_get_oldest (fromJust $ inclUrMap br) nomUrfather
                                     where nomUrfather = getUrfather br (DS.Prefix pr)
                                           giu_get_oldest :: InclusionUrfathersMap -> Prefix -> Prefix
                                            -- request "includer" prefix until fixpoint reached
                                           giu_get_oldest ium pr_
                                            = if parent == pr_ then pr_ else giu_get_oldest ium parent
                                               where parent = ium Map.! pr_
    Just InclusionBlockingChain  -> -- find the *oldest* inclusion urfather on the chain
                                      go br nomUrfather nomUrfather Nothing
                                     where nomUrfather = getUrfather br (DS.Prefix pr)
                                           go :: Branch -> Prefix -> Prefix -> Maybe Prefix -> Prefix
                                           go br_ initial current mBlocker =
                                              case fatherOf current of
                                                Nothing       -> maybe initial id mBlocker
                                                Just ancestor -> let urAncestor = getUrfather br (DS.Prefix ancestor) in
                                                                 if formulasIncluded br_ initial urAncestor
                                                                  then go br_ initial ancestor (Just urAncestor)
                                                                  else go br_ initial ancestor mBlocker
                                           parentMap    = prefParent br
                                           fatherOf pr_ = Map.lookup pr_ parentMap

calculateInclusionUrfathers :: Branch -> Branch
-- calculates the prefix -> inclusion urfather map incrementally, by
-- updating the map from the given prefix, which typically is the smallest augmented
-- prefix in the previous step

-- if the inclusion urfather blocking mode is enabled, we handle this map
-- if not, we let it as it is
calculateInclusionUrfathers br =
    br{inclUrMap = newInclUrMap}
     where newInclUrMap =  case blockMode br of
                            Nothing        -> Nothing
                            Just InclusionBlockingGlobal -> Just $ calculateInclusionUrfathersMap br
                            Just InclusionBlockingChain -> Nothing

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
-- is the set of formulas of the first prefix included in the set of the second prefix?
formulasIncluded br p1 p2 = Set.isSubsetOf (formulasOf p1) (formulasOf p2)
 where formulasOf p = Map.findWithDefault Set.empty p (prefToForms br)

-- is the formula useful to calculate inclusion urfathers ?
forInclusion :: Branch -> Formula -> Bool
forInclusion br (Lit (PosLit atom)) = forInclAtom br atom
forInclusion br (Lit (NegLit atom)) = forInclAtom br atom
forInclusion _ (Con _) = False
forInclusion _ (Dis _) = False
forInclusion _ (At _ _) = False
forInclusion _ (Atv _ _) = False
forInclusion _ (Down _ _) = False
forInclusion _ (Box _ _) = True
forInclusion _ (Dia _ _) = True
forInclusion _ (A _) = False
forInclusion _ (E _) = False
forInclusion _ (D _) = False
forInclusion _ (B _) = False

forInclAtom :: Branch -> Atom -> Bool
forInclAtom _  Taut  = False
forInclAtom br (N n) = Set.member n (relevantNominals br)
forInclAtom _  (P _) = True
forInclAtom _  (V _) = error "forInclAtom statevar : should not happen"

addParentPrefix :: Branch -> Prefix -> Prefix -> Branch
addParentPrefix br son father =  br{prefParent = Map.insert son father (prefParent br)}


{-     book-keeping that needs to be done before each step of the tableaux calculus     -}

calculateStepInfo :: Branch -> Branch
calculateStepInfo = wipeAugmentedPrefixes . calculateInclusionUrfathers

wipeAugmentedPrefixes :: Branch -> Branch
wipeAugmentedPrefixes br = br{incrPrs=[]}

addToAugmentedPrefixes :: Prefix -> Branch -> Branch
addToAugmentedPrefixes pr br = br{incrPrs = (pr:incrPrs br)}

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

addUnivConstraint :: CmdLineParams -> Branch -> BranchingPrefixes -> Formula -> BranchInfo
addUnivConstraint clp br bps f
 = addFormulas clp newBr
               ( map (\p -> PrFormula p bps f) $ urfathers )
               False
   where newBr = br{univCons = (bps,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

--

addDiffUnivConstraint :: CmdLineParams -> Branch -> BranchingPrefixes -> Formula -> Prefix -> BranchInfo
addDiffUnivConstraint clp br bprs f pr
 = addFormulas clp newBr
               ( (PrFormula pr bprs $ nom newNom)
                 :(map (\somePrefix -> PrFormula somePrefix bprs (Dis [f, nom newNom])) otherUrfathers)
               )
               False
   where currentUrfather = getUrfather br (DS.Prefix pr)
         prefs = [0..(lastPref br)]
         otherUrfathers = delete currentUrfather $ filter (isNominalUrfather br) prefs
         (updatedBr, newNom) = createNewNom br
         newBr = updatedBr{dBoxCons = (bprs,f,newNom):(dBoxCons updatedBr)}

--

addDiffRuleCheck :: Branch -> Formula -> PropSymbol -> Bool -> Branch
addDiffRuleCheck br f propsym b =
  br{dDiaRlCh=Map.insert f (propsym,b) (dDiaRlCh br)}

--

createNewPref :: CmdLineParams -> Branch -> BranchInfo
createNewPref clp br
 = addFormulas clp newBr (   map (\(bps,f) -> PrFormula newPr bps f) univConstraints
                          ++ map (\(bps,f,newNom) -> PrFormula newPr bps (Dis [f, nom newNom])) diffBoxConstraints)
                         False
   where newPr = (lastPref br) + 1
         newBr = br{lastPref = newPr}
         univConstraints = univCons br
         diffBoxConstraints = dBoxCons br


--

incPropSymbol :: PropSymbol -> PropSymbol
incPropSymbol (PropSymbol n) = PropSymbol (n+1)


createNewProp :: Branch -> Branch
createNewProp br
 = br{lastProp = Just newProp}
    where newProp = maybe (PropSymbol 0) incPropSymbol (lastProp br)

--

incNomSymbol :: NomSymbol -> NomSymbol
incNomSymbol (NomSymbol n) = NomSymbol (n+1)

createNewNom :: Branch -> (Branch, NomSymbol)
createNewNom br
 = (br{lastNom = Just newNom}, newNom)
    where newNom =  maybe (NomSymbol 0) incNomSymbol (lastNom br)


createNewNomTestRelevance :: Branch -> Formula -> Branch
createNewNomTestRelevance br f
 = br{lastNom = Just newNom ,
      relevantNominals = if relevant then Set.insert newNom (relevantNominals br) else (relevantNominals br),
      downVarRelevantCh = newDVRC
     }
   where (relevant, newDVRC) = doMemoize checkIfVariableNegatedOnce f (downVarRelevantCh br)
         newNom = maybe (NomSymbol 0) incNomSymbol (lastNom br)

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ _ (Con _))        = br{conjStr =(Set.delete f (conjStr br))}
remFormula br f@(PrFormula _ _ (Dia _ _))      = br{diaStr  =(Set.delete f (diaStr br))}
remFormula br f@(PrFormula _ _ (E _))          = br{existStr=(Set.delete f (existStr br))}
remFormula br f@(PrFormula _ _ (Dis _))        = br{disjStr =(Set.delete f (disjStr br))}
remFormula br f@(PrFormula _ _ (At _ _))       = br{atStr   =(Set.delete f (atStr br))}
remFormula br f@(PrFormula _ _ (D _))          = br{diffStr =(Set.delete f (diffStr br))}
remFormula br f@(PrFormula _ _ (Down _ _))     = br{downStr =(Set.delete f (downStr br))}
remFormula _    (PrFormula _ _ (Box _ _))      = error "that formula should never be deleted"
remFormula _    (PrFormula _ _ (Atv _ _))      = error "that formula should never be deleted"
remFormula _    (PrFormula _ _ (A _))          = error "that formula should never be deleted"
remFormula _    (PrFormula _ _ (B _))          = error "that formula should never be deleted"
remFormula _    (PrFormula _ _ (Lit (PosLit _))) = error "that formula should never be deleted"
remFormula _    (PrFormula _ _ (Lit (NegLit _))) = error "that formula should never be deleted"


{-     functions to handle the "clashable information", ie literals associated to prefixes     -}

data UpdateResult = UpdateSuccess Clashable_info | UpdateFailure BranchingPrefixes

addAndUpdateMap :: Branch -> Prefix -> BranchingPrefixes -> Literal -> BranchInfo
addAndUpdateMap br pr bprs l
  = case ( case l of PosLit a -> updateMap (clashStr br) pr bprs a True
                     NegLit a -> updateMap (clashStr br) pr bprs a False ) of
     UpdateSuccess cs    -> BranchOK br{clashStr = cs}
     UpdateFailure bprs2 -> BranchClash br pr bprs2 (Lit l)


-- Insert a piece of clashable information into all the clashable information of a branch

updateMap :: Clashable_info -> Prefix -> BranchingPrefixes -> Atom -> Bool -> UpdateResult
updateMap cs  _   _   Taut True  = UpdateSuccess cs
updateMap _   _  bprs Taut False = UpdateFailure bprs
updateMap cs pre bprs a bool
  = case Map.lookup pre cs of
       Nothing            -> UpdateSuccess $ Map.insert pre (Map.singleton a (bool,bprs)) cs
       Just slot          -> case updateClashableInfoSlot slot a bool bprs of
                              Slot_UpdateSuccess updatedSlot -> UpdateSuccess $ Map.insert pre updatedSlot cs
                              Slot_UpdateFailure failureDeps -> UpdateFailure failureDeps


type Clashable_info_slot = Map.Map Atom (Bool,BranchingPrefixes)
data Slot_UpdateResult =   Slot_UpdateSuccess Clashable_info_slot                     -- updated slot
                         | Slot_UpdateFailure BranchingPrefixes                       -- list of sets of branching prefixes


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
    where ucis_helper :: Clashable_info_slot -> [(Atom,(Bool,BranchingPrefixes))] -> Slot_UpdateResult
          ucis_helper cis a_b_bps_s =
             let (updateStatus,clashing_bps_s)
                                 = foldr (\(a,(bool,bps)) (upResult,clashingBps_s)
                                              -> case upResult of
                                                    Slot_UpdateSuccess cis_  ->  (updateClashableInfoSlot cis_ a bool bps, clashingBps_s      )
                                                    Slot_UpdateFailure bps_s ->  (updateClashableInfoSlot cis a bool bps, bps_s:clashingBps_s)  -- we reuse the input Clashabe Info Slot
                                         )
                                         (Slot_UpdateSuccess cis,[])   a_b_bps_s
                 result = case clashing_bps_s of
                              []    -> updateStatus                                    -- is 'success'
                              bps_s -> Slot_UpdateFailure $ findEarliestSet bps_s
                                         where findEarliestSet  bprs_s = minimumBy compareBPSets bprs_s
                                               compareBPSets bps1 bps2 = compare  (deps_min bps1) (deps_min bps2)
             in
                result


-- Insert a piece of information in a clashable info slot

updateClashableInfoSlot :: Clashable_info_slot -> Atom -> Bool -> BranchingPrefixes -> Slot_UpdateResult
updateClashableInfoSlot cis Taut True   _   = Slot_UpdateSuccess cis
updateClashableInfoSlot  _  Taut False bprs = Slot_UpdateFailure bprs
updateClashableInfoSlot cis a             bool  bprs  -- nominals, propositional symbols
 = case Map.lookup a cis of
    Nothing            -> Slot_UpdateSuccess $ Map.insert a (bool,bprs) cis
    Just (bool2,bprs2) -> if bool == bool2
                           then Slot_UpdateSuccess $ Map.insert a (bool,bprs_to_keep) cis
                           else Slot_UpdateFailure $ bps_union bprs bprs2
                             where bprs_to_keep = if (deps_min bprs2) <  (deps_min bprs) then bprs2 else bprs
                                  -- if the same information is caused by an earlier
                                  -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

addDepsToClashableSlot :: Slot_UpdateResult -> BranchingPrefixes -> Slot_UpdateResult
addDepsToClashableSlot res_cis bps =
 case res_cis of
  Slot_UpdateSuccess cis         ->  Slot_UpdateSuccess $ Map.map (\(a,currentBps) -> (a,bps_union currentBps bps)) cis
  failure@(Slot_UpdateFailure _) -> failure



queryClashableSlot :: Branch -> Prefix -> Literal -> Maybe (Bool,BranchingPrefixes)
-- Output : Nothing = nevermind ; Just True = already there ; Just False = contrary there
queryClashableSlot _ _ (PosLit Taut) = Just (True,bps_empty)
queryClashableSlot _ _ (NegLit Taut) = Just (False,bps_empty)
queryClashableSlot br pr (NegLit a)
  = do slot <- Map.lookup pr (clashStr br)
       case Map.lookup a slot of
         Nothing           -> Nothing
         Just (bool,bprs)  -> Just (not bool,bprs)
queryClashableSlot br pr (PosLit a)
  = do slot <- Map.lookup pr (clashStr br)
       case Map.lookup a slot of
         Nothing           -> Nothing
         Just (bool,bprs)  -> Just (bool,bprs)


{-     function used for unit propagation     -}

data ReducedDisjunct = Triviality | Contradiction BranchingPrefixes | Reduced BranchingPrefixes [Formula]

reduceDisjunctionAgainstBranch :: Branch -> Prefix -> [Formula] -> ReducedDisjunct
reduceDisjunctionAgainstBranch br pr fs =
         case foldr scanDisjunctAndTest (Just ( [] , bps_empty )) fs of
          Nothing                        ->  Triviality
          Just  (  []        , bprs )    ->  Contradiction bprs
          Just  (  disjuncts , bprs )    ->  Reduced       bprs disjuncts

         where -- for each removed literal of the disjunction, we have to add the dependencies of the literal that got it removed to the re-created formula
               -- and if the recreated formula is empty, then there is a clash, with all the branching dependencies
               -- if the formula is "trivial" (= one disjunct is already there) we just remove the formula, i guess...
           ur = getUrfather br (DS.Prefix pr)
           scanDisjunctAndTest :: Formula -> Maybe ([Formula],BranchingPrefixes) -> Maybe ([Formula],BranchingPrefixes)
           scanDisjunctAndTest       _                Nothing               =    Nothing
           scanDisjunctAndTest    l@(Lit current) (Just (disjuncts,bprs_))    =
             case queryClashableSlot br ur current of
                Nothing            -> Just ((l:disjuncts),bprs_)
                Just (True,_)      -> Nothing
                Just (False,bprs2) -> Just (disjuncts,bps_union bprs_ bprs2)
           scanDisjunctAndTest       f          (Just (disjuncts,bprs_))    =    Just ((f:disjuncts),bprs_)


{-     other functions     -}
block :: Branch -> Branch
block br = br{blockMode = Just $ defaultBlockMode br }

hasUnivMod :: Branch -> Bool
hasUnivMod br = languageUniv $ inputLanguage br

hasDiffMod :: Branch -> Bool
hasDiffMod br = languageDiff $ inputLanguage br

hasDownArrow :: Branch -> Bool
hasDownArrow br = languageDown $ inputLanguage br

requireLocalFormulasTracking :: Branch -> Bool
requireLocalFormulasTracking br = (hasUnivMod br) || (hasDiffMod br) || (hasDownArrow br) || (blockMode br /= Nothing)
-- TODO directly put a boolean for this in BranchData , and an explicit one


prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]


{-      Monad related stuff      -}

data BranchData = BranchData { branch_info :: BranchInfo,
                               branch_clp :: CmdLineParams,
                               branch_path :: [Int]}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

addZeroInPath :: BranchData -> BranchData
addZeroInPath bd = bd{branch_path=(0:(branch_path bd))}

incPathHead :: BranchData -> BranchData
incPathHead bd = bd{branch_path=(((head (branch_path bd))+1):(tail $ branch_path bd))}

