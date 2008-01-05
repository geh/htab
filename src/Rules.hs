module Rules
(
Rule(..),BranchModification(..),
applicableRules, applyRule, ruleToId,
applyMods
) where

import Formula( RelSymbol(..), Atom(..), Formula(..), PrFormula(..), neg,
                BranchingPrefix, BranchingPrefixes,
                bps_insert, bps_union, prefixList, AccFormula(..),
                Rel, Prefix )
import Branch( Branch(..), incLastPr, BranchInfo(..),
               addFormulas, addAccFormula, remFormula,
               addBoxRuleCheck, addDiaRuleCheck, addExistRuleCheck,
               addAtRuleCheck, addUnivRuleCheck, Box_rule_chart,
               isInclusionUrfather, BlockingMode(..), hasUnivMod )
import CommandLine(CmdLineParams, semBranch, fullClash)
import RuleMetadata(RuleId(..))
import LatexOutput()
import LatexOutputHelper
import qualified Data.Map as Map
import qualified Data.Set as Set
import Ix(range)

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddBoxRuleCheck (Prefix,Rel,Prefix,Formula)
                           | BM_AddDiaRuleCheck Prefix Formula
                           | BM_AddAtRuleCheck Prefix Formula
                           | BM_AddExistRuleCheck Prefix Formula
                           | BM_AddUnivRuleCheck (Formula,Prefix)
                           | BM_RemFormula PrFormula
                           | BM_IncLastPr

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula         -- creates a prefix
           | BoxRule    (Prefix,Rel,Prefix,Formula) PrFormula
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | NegRule    PrFormula PrFormula
           | AtRule     PrFormula PrFormula PrFormula          -- creates a prefix
           | UnivModRule   [PrFormula] (Formula,Prefix)
           | ExistModRule  PrFormula PrFormula                 -- creates a prefix

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ConjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds]]

getMods _ (DiaRule todelete@(PrFormula pr _ f) acctoadd toadd) =
 [[BM_RemFormula todelete, BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd],
   BM_AddDiaRuleCheck pr f,
   BM_IncLastPr]]

getMods _ (BoxRule checktoadd ftoadd) =
 [[BM_AddBoxRuleCheck checktoadd, BM_AddFormulas [ftoadd]]]

getMods _ (UnivModRule toadds tocheck) =
 [[BM_AddFormulas toadds, BM_AddUnivRuleCheck tocheck]]

getMods br (ExistModRule todelete@(PrFormula pr _ f) toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd],
   BM_IncLastPr]
   ++ if (hasUnivMod br) then [BM_AddExistRuleCheck pr f] else [] ]

getMods _ (DisjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule todelete toaddss) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (NegRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods br (AtRule todelete@(PrFormula pr _ f) toadd1 toadd2) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd1, toadd2], BM_IncLastPr]
  ++ if (hasUnivMod br) then [BM_AddAtRuleCheck pr f] else [] ]


instance Show Rule where
   show (ConjRule  todelete _ )    = "conjunction : " ++ (show todelete)
   show (DiaRule   todelete _ _ )  = "diamond : " ++ (show todelete)
   show (BoxRule   boxRuleCheck _ )= "box : " ++ (show boxRuleCheck)
   show (DisjRule  todelete _ )    = "disjunction : " ++ (show todelete)
   show (SemBrRule todelete _ )    = "semantic branching : " ++ (show todelete)
   show (NegRule   todelete _ )    = "negation : " ++ (show todelete)
   show (AtRule    todelete _ _ )  = "at : " ++ (show todelete)
   show (ExistModRule todelete _)  = "E : " ++ (show todelete)
   show (UnivModRule toadds _)     = "A : " ++ (show toadds)

instance ShowLatex Rule where
   showLatex (ConjRule   todelete _ ) = "conjunction : " ++  (math $ showLatex todelete)
   showLatex (DiaRule    todelete _ _ ) = "diamond : " ++  (math $ showLatex todelete)
   showLatex (BoxRule    boxRuleCheck _ ) = "box : " ++ (showLat boxRuleCheck)
    where showLat (p1,r,p2,f) = "(" ++ show p1 ++ "," ++ show r ++ "," ++ show p2 ++ "," ++ (math $ showLatex f) ++ ")"
   showLatex (DisjRule   todelete _ ) = "disjunction : " ++ (math $ showLatex todelete)
   showLatex (SemBrRule  todelete _ ) = "semantic branching : " ++ (math $ showLatex todelete)
   showLatex (NegRule    todelete _ ) = "negation : " ++ (math $ showLatex todelete)
   showLatex (AtRule     todelete _ _ ) = "at : " ++ (math $ showLatex todelete)
   showLatex (ExistModRule todelete _)  = "E : " ++ (math $ showLatex todelete)
   showLatex (UnivModRule toadds _)   = "A : " ++ (math $ showLatex toadds)


--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _ _)   -> R_Conj
              (DiaRule _ _ _)  -> R_Dia
              (BoxRule _ _)    -> R_Box
              (DisjRule _ _)   -> R_Disj
              (SemBrRule _ _)  -> R_SemBr
              (NegRule _ _)    -> R_Neg
              (AtRule _ _ _)   -> R_At
              (UnivModRule _ _)   -> R_Univ
              (ExistModRule _ _)  -> R_Exist

--

applicableRules :: Branch -> CmdLineParams -> BranchingPrefix -> [Rule]
applicableRules br clp d =
    ( if fullClash clp then (applicableNegRules br)
                       else [] )
 ++ (applicableConjRules br)
 ++ (applicableDiaRules br)
 ++ (applicableBoxRules br)
 ++ (applicableAtRules br)
 ++ (applicableExistRules br)
 ++ (applicableUnivRules br)
 ++ if semBranch clp then (applicableSemBrRules br d)
                     else (applicableDisjRules br d)

applicableConjRules :: Branch -> [Rule]
applicableConjRules br = [conjRule f br | f <- Set.toAscList $ conjStr br]

applicableDiaRules :: Branch -> [Rule]
applicableDiaRules br =
 if prefGenBlock
  then [diaRule f br | f@(PrFormula pr _ _) <- Set.toAscList $ diaStr br,
                       isInclusionUrfather br pr]
  else [diaRule f br | f <- Set.toAscList $ diaStr br]
 where prefGenBlock = (blockMode br) == InclusionBlocking

applicableBoxRules :: Branch -> [Rule]
applicableBoxRules br
  = [boxRule prF accF br | (prF,accF) <- (unCheckedBoxPairs br)]

applicableDisjRules :: Branch -> BranchingPrefix -> [Rule]
applicableDisjRules br d = [disjRule f br d | f <- Set.toAscList $ disjStr br]

applicableSemBrRules :: Branch -> BranchingPrefix -> [Rule]
applicableSemBrRules br d = [semBrRule f br d | f <- Set.toAscList $ disjStr br]

applicableNegRules :: Branch -> [Rule]
applicableNegRules br = [negRule f br | f <- Set.toAscList $ negStr br]

applicableAtRules :: Branch -> [Rule]
applicableAtRules br =
 if prefGenBlock
  then [atRule f br | f@(PrFormula pr _ _) <- Set.toAscList $ atStr br,
                      isInclusionUrfather br pr]
  else [atRule f br | f <- Set.toAscList $ atStr br]
 where prefGenBlock = (blockMode br) == InclusionBlocking


applicableExistRules :: Branch -> [Rule]
applicableExistRules br =
 if prefGenBlock
  then [existRule f br | f@(PrFormula pr _ _) <- Set.toAscList $ existStr br,
                         isInclusionUrfather br pr]
  else [existRule f br | f <- Set.toAscList $ existStr br]
 where prefGenBlock = (blockMode br) == InclusionBlocking


applicableUnivRules :: Branch -> [Rule]
applicableUnivRules br = [univRule f br | f@(PrFormula _ _ (A innerF)) <- Set.toAscList $ univStr br,
                                          let lastPr_ = lastPr br,
                                          let univRlCh_ = univRlCh br,
                                          maybe True (\appliedPr ->  appliedPr < lastPr_)
                                                (Map.lookup innerF univRlCh_)]

unCheckedBoxPairs :: Branch -> [(AccFormula,(BranchingPrefixes,Formula))]
unCheckedBoxPairs br
  = [(AccFormula bps2 (RelSymbol r2) p2 p3, (bps1,f))
                 | bk@(p1,r1) <- Map.keys (boxStr br),
                   ak@(p2,r2) <- Map.keys (accStr br),
                   p1 == p2 , r1 == r2,
                   (bps1,f) <- (Map.!) (boxStr br) bk,
                   (bps2,p3) <- (Map.!) (accStr br) ak,
                   reallyNotIn (p1,r1,p3,f) (boxRlCh br)]

reallyNotIn :: (Prefix,Rel,Prefix,Formula) -> Box_rule_chart -> Bool
reallyNotIn (p1,r,p2,f) brc =
 case (Map.lookup (p1,r,p2) brc) of
    Nothing -> True
    Just fs -> Set.notMember f fs


applyRule :: CmdLineParams -> Rule -> Branch -> [BranchInfo]
applyRule clp rule br = applySetOfMods clp br (getMods br rule)


applySetOfMods :: CmdLineParams -> Branch -> [[BranchModification]] -> [BranchInfo]
applySetOfMods clp br (hd:tl) = (applyMods clp br hd):(applySetOfMods clp br tl)
applySetOfMods _ _ [] = []


applyMods :: CmdLineParams -> Branch -> [BranchModification] -> BranchInfo
applyMods clp br (hd:tl) = case (applyMod clp br hd) of
                            BranchOK br2             -> applyMods clp br2 tl
                            si@(BranchClash _ _ _ _) -> si
applyMods _ br [] = BranchOK br


applyMod :: CmdLineParams -> Branch -> BranchModification -> BranchInfo
applyMod clp br (BM_AddFormulas li) = addFormulas clp br li
applyMod  _  br (BM_AddAccFormula accFor) = BranchOK (addAccFormula br accFor)
applyMod  _  br (BM_AddBoxRuleCheck check) = BranchOK (addBoxRuleCheck br check)
applyMod  _  br (BM_AddDiaRuleCheck pr f) = BranchOK (addDiaRuleCheck br pr f)
applyMod  _  br (BM_AddAtRuleCheck pr f) = BranchOK (addAtRuleCheck br pr f)
applyMod  _  br (BM_AddExistRuleCheck pr f) = BranchOK (addExistRuleCheck br pr f)
applyMod  _  br (BM_AddUnivRuleCheck check) = BranchOK (addUnivRuleCheck br check)
applyMod  _  br (BM_IncLastPr) = BranchOK (incLastPr br)
applyMod  _  br (BM_RemFormula f) = BranchOK (remFormula br f)

-- the actual rules and their helper functions

-- conjunction

-- takes 1 argument, the formula to remove
conjRule :: PrFormula -> Branch -> Rule
conjRule f _ = ConjRule f (breakConj f)

breakConj :: PrFormula -> [PrFormula]
breakConj (PrFormula pr bprs (Con formulaList)) = prefixList pr bprs formulaList
breakConj _ = error $ "breakConj error"


-- dia
diaRule :: PrFormula -> Branch -> Rule
diaRule f@(PrFormula pr bprs (Dia r f2)) br
  = DiaRule f (AccFormula bprs r pr newPr) (PrFormula newPr bprs f2)
      where newPr = getNewPr br
diaRule _ _ = error $ "diaRule"

--
getNewPr :: Branch -> Prefix
getNewPr br = (lastPr br)+1

-- box
boxRule :: AccFormula -> (BranchingPrefixes,Formula) -> Branch -> Rule
boxRule (AccFormula bprs1 (RelSymbol r1) pr1 pr2) (bprs2,f) _
 =  BoxRule (pr1,r1,pr2,f) (PrFormula pr2 (bps_union bprs1 bprs2) f)

boxRule (AccFormula _ (InvRelSymbol _) _ _) _ _
 = error "inverse modality not supported"

-- A
univRule :: PrFormula -> Branch -> Rule
univRule (PrFormula _ bprs (A f2)) br
  = UnivModRule (map (\p -> PrFormula p bprs f2) prefixesToHandle) check
     where m_currentPrefix = Map.lookup f2 (univRlCh br)
           prefixToStartWith = maybe 0 ((+)1) m_currentPrefix
           prefixToEndWith   = lastPr br
           prefixesToHandle  = range (prefixToStartWith,prefixToEndWith)
           check = (f2,prefixToEndWith)
univRule _ _ = error $ "univRule"

-- E
existRule :: PrFormula -> Branch -> Rule
existRule f@(PrFormula _ bprs (E f2)) br
  = ExistModRule f (PrFormula newPr bprs f2)
     where newPr = getNewPr br
existRule _ _ = error $ "existRule"

-- disjunction
disjRule :: PrFormula -> Branch -> BranchingPrefix -> Rule
disjRule df _ d = DisjRule df (breakDisj df d)

-- semantic branching
semBrRule :: PrFormula -> Branch -> BranchingPrefix -> Rule
semBrRule df _ d = SemBrRule df (sbModList disjointed [])
                     where disjointed = breakDisj df d

sbModList ::  [PrFormula] -> [PrFormula] -> [[PrFormula]]
sbModList (hd:tl) negated =
 (hd:negated)
  :(sbModList tl ((neg_ hd):negated))
     where neg_ (PrFormula pr bprs f) = PrFormula pr bprs (neg f)
sbModList [] _ = []

-- helper function for disjunction and semantic branching
-- updates the branching pointers of each formula
breakDisj :: PrFormula -> BranchingPrefix -> [PrFormula]
breakDisj (PrFormula pr bprs (Dis formulaList)) bpr = prefixList pr (bps_insert bpr bprs) formulaList
breakDisj _ _ = error $ "breakDisj error"

-- @
atRule :: PrFormula -> Branch -> Rule
atRule af@(PrFormula _ bprs (At n f)) br
 = AtRule af (PrFormula newPr bprs (PosLit (N n))) (PrFormula newPr bprs f)
    where newPr = getNewPr br

atRule _ _ = error "atRule error"

-- negation
negRule :: PrFormula -> Branch -> Rule
negRule nf@(PrFormula pr bprs (Neg f)) _ = NegRule nf (PrFormula pr bprs (neg1 f))

negRule _ _ = error $ "negRule error"

-- one-step negation
neg1 :: Formula -> Formula
neg1 (Con l)    = Dis (map neg l)
neg1 (Dis l)    = Con (map neg l)
neg1 (At n f)   = At n (neg f)
neg1 (Box n f)  = Dia n (neg f)
neg1 (Dia n f)  = Box n (neg f)
neg1 (A f)      = E (neg f)
neg1 (E f)      = A (neg f)
neg1 (Neg f)    = f
neg1 (PosLit a) = NegLit a
neg1 (NegLit a) = PosLit a

