module Rules where

import Formula
import Branch(Branch(..), incLastPr, BranchInfo(..),
              addFormulas, addAccFormula, remFormula, addBoxRuleCheck,Box_rule_chart)
import CommandLine(CmdLineParams, semBranch, fullClash)
import RuleMetadata(RuleId(..))
import LatexOutput()
import LatexOutputHelper
import qualified Data.Map as Map
import qualified Data.Set as Set

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddBoxRuleCheck (Prefix,Rel,Prefix,Formula)
                           | BM_RemFormula PrFormula
                           | BM_IncLastPr

data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula
           | BoxRule    (Prefix,Rel,Prefix,Formula) PrFormula
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | NegRule    PrFormula PrFormula
           | AtRule     PrFormula PrFormula PrFormula
           | NegNomRule PrFormula PrFormula

getMods :: Rule -> [[BranchModification]]
getMods (ConjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds]]

getMods (DiaRule todelete acctoadd toadd) =
 [[BM_RemFormula todelete, BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd], BM_IncLastPr]]

getMods (BoxRule checktoadd ftoadd) =
 [[BM_AddBoxRuleCheck checktoadd, BM_AddFormulas [ftoadd]]]

getMods (DisjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]] | toadd <- toadds]

getMods (SemBrRule todelete toaddss) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds] | toadds <- toaddss]

getMods (NegRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods (AtRule todelete toadd1 toadd2) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd1, toadd2], BM_IncLastPr]]

getMods (NegNomRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd], BM_IncLastPr]]


instance Show Rule where
   show (ConjRule  todelete _ )    = "conjunction : " ++ (show todelete)
   show (DiaRule   todelete _ _ )  = "diamond : " ++ (show todelete)
   show (BoxRule   boxRuleCheck _ )= "box : " ++ (show boxRuleCheck)
   show (DisjRule  todelete _ )    = "disjunction : " ++ (show todelete)
   show (SemBrRule todelete _ )    = "semantic branching : " ++ (show todelete)
   show (NegRule   todelete _ )    = "negation : " ++ (show todelete)
   show (AtRule    todelete _ _ )  = "at : " ++ (show todelete)
   show (NegNomRule todelete _ )   = "neg nom : " ++ (show todelete)


instance ShowLatex Rule where
   showLatex (ConjRule   todelete _ ) = "conjunction : " ++  (math $ showLatex todelete)
   showLatex (DiaRule    todelete _ _ ) = "diamond : " ++  (math $ showLatex todelete)
   showLatex (BoxRule    boxRuleCheck _ ) = "box : " ++ (showLat boxRuleCheck)
    where showLat (p1,r,p2,f) = "(" ++ show p1 ++ "," ++ show r ++ "," ++ show p2 ++ "," ++ (math $ showLatex f) ++ ")"
   showLatex (DisjRule   todelete _ ) = "disjunction : " ++ (math $ showLatex todelete)
   showLatex (SemBrRule  todelete _ ) = "semantic branching : " ++ (math $ showLatex todelete)
   showLatex (NegRule    todelete _ ) = "negation : " ++ (math $ showLatex todelete)
   showLatex (AtRule     todelete _ _ ) = "at : " ++ (math $ showLatex todelete)
   showLatex (NegNomRule todelete _ ) = "neg nom : " ++ (math $ showLatex todelete)


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
              (NegNomRule _ _) -> R_NegNom
--

applicableRules :: Branch -> CmdLineParams -> BranchingPrefix -> [Rule]
applicableRules br clp d =
    ( if fullClash clp then (applicableNegRules br)
                       else [] )
 ++ (applicableConjRules br)
 ++ (applicableDiaRules br)
 ++ (applicableBoxRules br)
 ++ (applicableAtRules br)
 ++ (applicableNegNomRules br)
 ++ if semBranch clp then (applicableSemBrRules br d)
                     else (applicableDisjRules br d)



applicableConjRules :: Branch -> [Rule]
applicableConjRules br = [conjRule f br | f <- Set.toAscList $ conjStr br]

applicableDiaRules :: Branch -> [Rule]
applicableDiaRules br = [diaRule f br | f <- Set.toAscList $ diaStr br]


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
applicableAtRules br = [atRule f br | f <- Set.toAscList $ atStr br]

applicableNegNomRules :: Branch -> [Rule]
applicableNegNomRules br = [negNomRule f br | f <- Set.toAscList $ negNomStr br]

unCheckedBoxPairs :: Branch -> [(AccFormula,(BranchingPrefixes,Formula))]
-- TODO consider privilegiating formulas with older branchings
unCheckedBoxPairs br
  = [(AccFormula bps2 r2 p2 p3, (bps1,f))
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
applyRule clp rule br = applySetOfMods clp (getMods rule) br


applySetOfMods :: CmdLineParams -> [[BranchModification]] -> Branch -> [BranchInfo]
applySetOfMods clp (hd:tl) br = (applyMods clp hd br):(applySetOfMods clp tl br)
applySetOfMods _ [] _ = []


applyMods :: CmdLineParams -> [BranchModification] -> Branch -> BranchInfo
applyMods clp (hd:tl) br = case (applyMod clp hd br) of
                            BranchOK br2             -> applyMods clp tl br2
                            si@(BranchClash _ _ _ _) -> si
applyMods _ [] br = BranchOK br


applyMod :: CmdLineParams -> BranchModification -> Branch -> BranchInfo
applyMod clp (BM_AddFormulas li) br = addFormulas clp br li
applyMod  _ (BM_AddAccFormula accFor) br = BranchOK (addAccFormula br accFor)
applyMod  _ (BM_AddBoxRuleCheck li) br = BranchOK (addBoxRuleCheck br li)
applyMod  _ (BM_IncLastPr) br = BranchOK (incLastPr br)
applyMod  _ (BM_RemFormula f) br = BranchOK (remFormula br f)

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
boxRule (AccFormula bprs1 r1 pr1 pr2) (bprs2,f) _
 =  BoxRule (pr1,r1,pr2,f) (PrFormula pr2 (bps_union bprs1 bprs2) f)

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

-- ¬a
negNomRule :: PrFormula -> Branch -> Rule
negNomRule f@(PrFormula _ bprs (NegLit n@(N _))) br
 = NegNomRule f (PrFormula newPr bprs (PosLit n))
    where newPr = getNewPr br

negNomRule _ _ = error "negNomRule error"

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
neg1 (Neg f)    = f
neg1 (PosLit a) = NegLit a
neg1 (NegLit a) = PosLit a

