module HTab.Rules
(
Rule(..),BranchModification(..),
applicableRules, applyRule, ruleToId,
applyMod
) where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HTab.Formula( Formula(..), PrFormula(..), neg, Atom(..),
                     BranchingPrefix,
                     bps_insert, prefixList, AccFormula(..),
                     Prefix, NomSymbol(..), PropSymbol(..),
                     BranchingPrefixes, bps_union )
import HTab.Branch( Branch(..), createNewPref, createNewProp,
                    BranchInfo(..),
                    addFormulas, addAccFormula, remFormula,
                    addDiaRuleCheck, addDiffRuleCheck,
                    getUrfatherAndDeps,
                    isInInclusionUrfatherClass, BlockingMode(..),
                    diaAlreadyDone, incPropSymbol )
import HTab.CommandLine(CmdLineParams, semBranch, fullClash)
import HTab.RuleMetadata(RuleId(..))
import qualified HTab.DisjSet as DS
import HTab.LatexOutput()
import HTab.LatexOutputHelper

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix Formula
                           | BM_AddDiffRuleCheck Formula PropSymbol Bool
                           | BM_RemFormula PrFormula
                           | BM_CreateNewPref
                           | BM_CreateNewProp

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula        -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | NegRule    PrFormula PrFormula
           | AtRule     PrFormula PrFormula
           | DiffRule   (Prefix, BranchingPrefixes, Formula)
           | ExistModRule PrFormula PrFormula                 -- creates a prefix
           | DiscardRule PrFormula

-- from the description of a rule application, creates the list of lists of modifications to the branch
-- for certain rules, we need to look in the branch to see what modifications we do

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ConjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds]]

getMods _ (DiaRule todelete@(PrFormula pr _ f) acctoadd toadd) =
 [[BM_RemFormula todelete, BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd],
   BM_AddDiaRuleCheck pr f,
   BM_CreateNewPref]]

getMods _ (ExistModRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd],
   BM_CreateNewPref]]

getMods _ (DisjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule todelete toaddss) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (NegRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods _ (AtRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods br (DiffRule (pr, bprs , f2)) =
 case Map.lookup f2 (dDiaRlCh br) of
  Nothing -> [[BM_RemFormula todelete,
               BM_CreateNewPref, BM_CreateNewProp,
               BM_AddFormulas [PrFormula newPref bprs f2,
                               PrFormula newPref bprs (PosLit $ P newProp),
                               PrFormula pr      bprs (NegLit $ P newProp)],
               BM_AddDiffRuleCheck f2 newProp False
             ]]
              where newPref = getNewPref br
                    newProp = getNewProp br

  Just (diffProp,doneTwiceBool)
          -> -- the "different place" for this D-formula has already been created
                   case (do clashSlot <- Map.lookup pr (clashStr br)
                            Map.lookup (PosLit $ P diffProp) clashSlot ) of -- are we already at the "different place" ?
                    Nothing -> [[BM_RemFormula (PrFormula pr bprs (D f2)),
                                 BM_AddFormulas [PrFormula pr bprs (Dis [(NegLit $ P diffProp), D f2])]
                                 -- no, so mark oneself as different from the "different place"; and when it is no longer true,
                                 -- we will generate another different world
                               ]]
                    Just (bool_,bprs_) ->
                     if bool_
                      then  -- we are at the "different place"
                       if doneTwiceBool
                         then -- we have already created a "second different place"
                           [[BM_RemFormula todelete]]
                         else -- we need to create a "second different place"
                           let newPref = getNewPref br
                               newProp = getNewProp br
                           in
                           [[BM_RemFormula todelete,
                             BM_CreateNewPref, BM_CreateNewProp,
                             BM_AddFormulas [PrFormula newPref (bps_union bprs bprs_) f2,
                                             PrFormula newPref (bps_union bprs bprs_) (PosLit $ P newProp),
                                             PrFormula pr      (bps_union bprs bprs_) (NegLit $ P newProp)],
                             BM_AddDiffRuleCheck f2 newProp True
                           ]]
                      else [[BM_RemFormula todelete]] -- we are already marked as different from the "different place"

 where todelete = PrFormula pr bprs (D f2)

getMods _ (DiscardRule todelete) =
 [[BM_RemFormula todelete]]


instance Show Rule where
   show (ConjRule  todelete _ )    = "conjunction: " ++ (show todelete)
   show (DiaRule   todelete _ _ )  = "diamond: " ++ (show todelete)
   show (DisjRule  todelete _ )    = "disjunction: " ++ (show todelete)
   show (SemBrRule todelete _ )    = "semantic branching: " ++ (show todelete)
   show (NegRule   todelete _ )    = "negation: " ++ (show todelete)
   show (AtRule    todelete _ )    = "at: " ++ (show todelete)
   show (ExistModRule todelete _)  = "E: " ++ (show todelete)
   show (DiffRule todelete )       = "D: " ++ (show todelete)
   show (DiscardRule todelete)     = "Discard: " ++ (show todelete)

instance ShowLatex Rule where
   showLatex (ConjRule   todelete _ )  = "conjunction: " ++  (math $ showLatex todelete)
   showLatex (DiaRule    todelete _ _) = "diamond: " ++  (math $ showLatex todelete)
   showLatex (DisjRule   todelete _ )  = "disjunction: " ++ (math $ showLatex todelete)
   showLatex (SemBrRule  todelete _ )  = "semantic branching: " ++ (math $ showLatex todelete)
   showLatex (NegRule    todelete _ )  = "negation: " ++ (math $ showLatex todelete)
   showLatex (AtRule     todelete _ )  = "at: " ++ (math $ showLatex todelete)
   showLatex (ExistModRule todelete _) = "E: " ++ (math $ showLatex todelete)
   showLatex (DiffRule todelete )      = "D: " ++ (math $ showLatex todelete)
   showLatex (DiscardRule todelete)    = "Discard: " ++ (math $ showLatex todelete)

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _ _)   -> R_Conj
              (DiaRule _ _ _)  -> R_Dia
              (DisjRule _ _)   -> R_Disj
              (SemBrRule _ _)  -> R_SemBr
              (NegRule _ _)    -> R_Neg
              (AtRule _ _ )    -> R_At
              (ExistModRule _ _) -> R_Exist
              (DiffRule _ )    -> R_Diff
              (DiscardRule _)  -> R_Discard

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
 ++ (applicableDiffRules br)
 ++ if semBranch clp then (applicableSemBrRules br d)
                     else (applicableDisjRules br d)

applicableConjRules :: Branch -> [Rule]
applicableConjRules br = [conjRule f br | f <- Set.toAscList $ conjStr br]

applicableDiaRules :: Branch -> [Rule]
applicableDiaRules br =
 if prefGenBlock
  then [diaRule f br | f@(PrFormula pr _ _) <- Set.toAscList $ diaStr br,
                       isInInclusionUrfatherClass br pr]
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

applicableDiffRules :: Branch -> [Rule]
applicableDiffRules br = [diffRule f br | f <- Set.toAscList $ diffStr br]

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
applyMod clp br (BM_CreateNewPref) = createNewPref clp br
applyMod  _  br (BM_CreateNewProp) = BranchOK $ createNewProp br
applyMod  _  br (BM_RemFormula f) = BranchOK (remFormula br f)
applyMod  _  br (BM_AddDiffRuleCheck f prop b) = BranchOK (addDiffRuleCheck br f prop b)

-- the actual rules and their helper functions

-- conjunction

-- takes 1 argument, the formula to remove
conjRule :: PrFormula -> Branch -> Rule
conjRule f _ = ConjRule f (breakConj f)

breakConj :: PrFormula -> [PrFormula]
breakConj (PrFormula pr bprs (Con formulaList)) = prefixList pr bprs formulaList
breakConj _ = error $ "breakConj error"

-- dia (may create a discard rule)
diaRule :: PrFormula -> Branch -> Rule
diaRule f@(PrFormula pr bprs f1@(Dia r f2)) br
  = if (diaAlreadyDone br pr f1)
     then DiscardRule f
     else DiaRule f (AccFormula bprs r pr newPr) (PrFormula newPr bprs f2)
      where newPr = getNewPref br


diaRule _ _ = error $ "diaRule"

--

getNewPref :: Branch -> Prefix
getNewPref br = (lastPref br)+1

--

getNewProp :: Branch -> PropSymbol
getNewProp br = maybe (PropSymbol 0) incPropSymbol (lastProp br)

-- E
existRule :: PrFormula -> Branch -> Rule
existRule f@(PrFormula _ bprs (E f2)) br
  = ExistModRule f (PrFormula newPr bprs f2)
     where newPr = getNewPref br
existRule _ _ = error $ "existRule"

-- D
diffRule :: PrFormula -> Branch -> Rule
diffRule (PrFormula pr bprs (D f2)) _
  = DiffRule (pr, bprs, f2)

diffRule _ _ = error $ "diffRule"

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
neg1 (D f)      = B (neg f)
neg1 (B f)      = D (neg f)
neg1 (Neg f)    = f
neg1 (PosLit a) = NegLit a
neg1 (NegLit a) = PosLit a

