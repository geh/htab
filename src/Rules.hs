module Rules
(
Rule(..),BranchModification(..),
applicableRules, applyRule, ruleToId,
applyMod
) where

import Formula( Formula(..), PrFormula(..), neg,
                BranchingPrefix,
                bps_insert, prefixList, AccFormula(..),
                Prefix, NomSymbol(..), bps_union )
import Branch( Branch(..), createNewPr, BranchInfo(..),
               addFormulas, addAccFormula, remFormula,
               addDiaRuleCheck, addExistRuleCheck,
               addAtRuleCheck, getUrfatherAndDeps,
               isInclusionUrfather, BlockingMode(..))
import CommandLine(CmdLineParams, semBranch, fullClash)
import RuleMetadata(RuleId(..))
import qualified DisjSet as DS
import LatexOutput()
import LatexOutputHelper
import qualified Data.Set as Set

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix Formula
                           | BM_AddAtRuleCheck Formula
                           | BM_AddExistRuleCheck Formula
                           | BM_RemFormula PrFormula
                           | BM_CreateNewPr

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula        -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | NegRule    PrFormula PrFormula
           | AtRule     PrFormula PrFormula
           | ExistModRule PrFormula PrFormula                 -- creates a prefix

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ConjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds]]

getMods _ (DiaRule todelete@(PrFormula pr _ f) acctoadd toadd) =
 [[BM_RemFormula todelete, BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd],
   BM_AddDiaRuleCheck pr f,
   BM_CreateNewPr]]

getMods _ (ExistModRule todelete@(PrFormula _ _ f) toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd],
   BM_CreateNewPr,BM_AddExistRuleCheck f]]

getMods _ (DisjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule todelete toaddss) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (NegRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods _ (AtRule todelete@(PrFormula _ _ f) toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd], BM_AddAtRuleCheck f]]


instance Show Rule where
   show (ConjRule  todelete _ )    = "conjunction : " ++ (show todelete)
   show (DiaRule   todelete _ _ )  = "diamond : " ++ (show todelete)
   show (DisjRule  todelete _ )    = "disjunction : " ++ (show todelete)
   show (SemBrRule todelete _ )    = "semantic branching : " ++ (show todelete)
   show (NegRule   todelete _ )    = "negation : " ++ (show todelete)
   show (AtRule    todelete _ )    = "at : " ++ (show todelete)
   show (ExistModRule todelete _)  = "E : " ++ (show todelete)

instance ShowLatex Rule where
   showLatex (ConjRule   todelete _ ) = "conjunction : " ++  (math $ showLatex todelete)
   showLatex (DiaRule    todelete _ _ ) = "diamond : " ++  (math $ showLatex todelete)
   showLatex (DisjRule   todelete _ ) = "disjunction : " ++ (math $ showLatex todelete)
   showLatex (SemBrRule  todelete _ ) = "semantic branching : " ++ (math $ showLatex todelete)
   showLatex (NegRule    todelete _ ) = "negation : " ++ (math $ showLatex todelete)
   showLatex (AtRule     todelete _ ) = "at : " ++ (math $ showLatex todelete)
   showLatex (ExistModRule todelete _)  = "E : " ++ (math $ showLatex todelete)

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _ _)   -> R_Conj
              (DiaRule _ _ _)  -> R_Dia
              (DisjRule _ _)   -> R_Disj
              (SemBrRule _ _)  -> R_SemBr
              (NegRule _ _)    -> R_Neg
              (AtRule _ _ )    -> R_At
              (ExistModRule _ _)  -> R_Exist

--


--the order matters, as the first rule is the one that will be applied at the next tableau step
applicableRules :: Branch -> CmdLineParams -> BranchingPrefix -> [Rule]
applicableRules br clp d =
    ( if fullClash clp then (applicableNegRules br)
                       else [] )
 ++ (applicableConjRules br)
 ++ (applicableDiaRules br)
 ++ (applicableAtRules br)
 ++ (applicableExistRules br)
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

applicableDisjRules :: Branch -> BranchingPrefix -> [Rule]
applicableDisjRules br d = [disjRule f br d | f <- Set.toAscList $ disjStr br]

applicableSemBrRules :: Branch -> BranchingPrefix -> [Rule]
applicableSemBrRules br d = [semBrRule f br d | f <- Set.toAscList $ disjStr br]

applicableNegRules :: Branch -> [Rule]
applicableNegRules br = [negRule f br | f <- Set.toAscList $ negStr br]

applicableAtRules :: Branch -> [Rule]
applicableAtRules br = [atRule f br | f <- Set.toAscList $ atStr br]

applicableExistRules :: Branch -> [Rule]
applicableExistRules br = [existRule f br | f <- Set.toAscList $ existStr br]

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
applyMod clp br (BM_AddAccFormula accFor) = addAccFormula clp br accFor
applyMod  _  br (BM_AddDiaRuleCheck pr f) = BranchOK (addDiaRuleCheck br pr f)
applyMod  _  br (BM_AddAtRuleCheck f) = BranchOK (addAtRuleCheck br f)
applyMod  _  br (BM_AddExistRuleCheck f) = BranchOK (addExistRuleCheck br f)
applyMod clp br (BM_CreateNewPr) = createNewPr clp br
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
atRule af@(PrFormula _ bprs (At (NomSymbol n) f)) br
 = AtRule af (PrFormula earliestPrefix (bps_union bprs bprs2) f)
    where (earliestPrefix,bprs2,_) = getUrfatherAndDeps br (DS.Nominal n)

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

