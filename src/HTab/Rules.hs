module HTab.Rules
(
Rule(..),BranchModification(..),
applicableRules, applyRule, ruleToId,
applyMod
) where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HTab.Formula( Formula(..), PrFormula(..), showLess, neg, Atom(..), Literal(..),
                     BranchingPrefix,
                     bps_insert, prefixList, AccFormula(..),
                     Prefix, NomSymbol(..), PropSymbol(..),
                     replaceVar,
                     BranchingPrefixes, bps_union )
import HTab.Branch( Branch(..), createNewPref, createNewProp, createNewNomTestRelevance,
                    BranchInfo(..),
                    addFormulas, addAccFormula, remFormula,
                    addDiaRuleCheck, addDownRuleCheck, addDiffRuleCheck,
                    addParentPrefix, reduceDisjunctionAgainstBranch,
                    getUrfatherAndDeps, isNotBlocked, 
                    diaAlreadyDone, incPropSymbol, incNomSymbol,
                    ReducedDisjunct(..) )
import HTab.CommandLine(CmdLineParams, semBranch, unitProp)
import HTab.RuleMetadata(RuleId(..))
import qualified HTab.DisjSet as DS
import HTab.LatexOutput()
import HTab.LatexOutputHelper

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddDiaRuleCheck Prefix Formula
                           | BM_AddDownRuleCheck Prefix Formula
                           | BM_AddDiffRuleCheck Formula PropSymbol Bool
                           | BM_RemFormula PrFormula
                           | BM_CreateNewPref
                           | BM_CreateNewProp
                           | BM_CreateNewNomTestRelevance Formula
                           | BM_AddParentPrefix Prefix Prefix
                           | BM_Clash BranchingPrefixes PrFormula

-- each rule constructor contains exactly the needed data to know the effect of the rule
data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula        -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [[PrFormula]]
           | AtRule     PrFormula PrFormula
           | DownRule   PrFormula PrFormula PrFormula
           | DiffRule   (Prefix, BranchingPrefixes, Formula)
           | ExistModRule PrFormula PrFormula                 -- creates a prefix
           | DiscardRule PrFormula
           | ClashRule BranchingPrefixes PrFormula

-- from the description of a rule application, creates the list of lists of modifications to the branch
-- for certain rules, we need to look in the branch to see what modifications we do

getMods :: Branch -> Rule -> [[BranchModification]]
getMods _ (ClashRule bprs f) = [[BM_Clash bprs f]]

getMods _ (ConjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds]]

getMods _ (DiaRule todelete@(PrFormula pr _ f) acctoadd@(AccFormula _ _ p1 p2) toadd) =
 [[BM_RemFormula todelete, BM_AddAccFormula acctoadd,
   BM_AddFormulas [toadd],
   BM_AddDiaRuleCheck pr f,
   BM_AddParentPrefix p2 p1,
   BM_CreateNewPref]]

getMods _ (ExistModRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd],
   BM_CreateNewPref]]

getMods _ (DisjRule todelete toadds) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]] | toadd <- toadds]

getMods _ (SemBrRule todelete toaddss) =
 [[BM_RemFormula todelete, BM_AddFormulas toadds] | toadds <- toaddss]

getMods _ (AtRule todelete toadd) =
 [[BM_RemFormula todelete, BM_AddFormulas [toadd]]]

getMods _ (DownRule todelete@(PrFormula pr _ f) toadd1 toadd2) =
 [[BM_RemFormula todelete,
   BM_CreateNewNomTestRelevance f,  --  order
   BM_AddFormulas [toadd1, toadd2], -- matters
   BM_AddDownRuleCheck pr f
 ]]

getMods br (DiffRule (pr, bprs , f2)) =
 case Map.lookup f2 (dDiaRlCh br) of
  Nothing -> [[BM_RemFormula todelete,
               BM_CreateNewPref, BM_CreateNewProp,
               BM_AddFormulas [PrFormula newPref bprs f2,
                               PrFormula newPref bprs (Lit $ PosLit $ P newProp),
                               PrFormula pr      bprs (Lit $ NegLit $ P newProp)],
               BM_AddDiffRuleCheck f2 newProp False
             ]]
              where newPref = getNewPref br
                    newProp = getNewProp br

  Just (diffProp,doneTwiceBool)
          -> -- the "different place" for this D-formula has already been created
                   case (do clashSlot <- Map.lookup pr (clashStr br)
                            Map.lookup (P diffProp) clashSlot ) of -- are we already at the "different place" ?
                    Nothing -> [[BM_RemFormula (PrFormula pr bprs (D f2)),
                                 BM_AddFormulas [PrFormula pr bprs (Dis [Lit $ NegLit $ P diffProp, D f2])]
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
                                             PrFormula newPref (bps_union bprs bprs_) (Lit $ PosLit $ P newProp),
                                             PrFormula pr      (bps_union bprs bprs_) (Lit $ NegLit $ P newProp)],
                             BM_AddDiffRuleCheck f2 newProp True
                           ]]
                      else [[BM_RemFormula todelete]] -- we are already marked as different from the "different place"

 where todelete = PrFormula pr bprs (D f2)

getMods _ (DiscardRule todelete) =
 [[BM_RemFormula todelete]]


instance Show Rule where
   show (ConjRule  todelete _ )    = "conjunction:        " ++ showLess todelete
   show (DiaRule   todelete _ _ )  = "diamond:            " ++ showLess todelete
   show (DisjRule  todelete _ )    = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )    = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete _ )    = "at:                 " ++ showLess todelete
   show (DownRule  todelete _ _ )  = "down:               " ++ showLess todelete
   show (ExistModRule todelete _)  = "E:                  " ++ showLess todelete
   show (DiffRule (pr,_,f) )       = "D:                  " ++ show pr ++ ":" ++ show f
   show (DiscardRule todelete)     = "Discard:            " ++ showLess todelete
   show (ClashRule bprs f)         = "Clash:              " ++ show bprs ++ " " ++ show f

instance ShowLatex Rule where
   showLatex (ConjRule   todelete _ )  = "conjunction: " ++  (math $ showLatex todelete)
   showLatex (DiaRule    todelete _ _) = "diamond: " ++  (math $ showLatex todelete)
   showLatex (DisjRule   todelete _ )  = "disjunction: " ++ (math $ showLatex todelete)
   showLatex (SemBrRule  todelete _ )  = "semantic branching: " ++ (math $ showLatex todelete)
   showLatex (AtRule     todelete _ )  = "at: " ++ (math $ showLatex todelete)
   showLatex (DownRule   todelete _ _) = "down: " ++ (math $ showLatex todelete)
   showLatex (ExistModRule todelete _) = "E: " ++ (math $ showLatex todelete)
   showLatex (DiffRule todelete )      = "D: " ++ (math $ showLatex todelete)
   showLatex (DiscardRule todelete)    = "Discard: " ++ (math $ showLatex todelete)
   showLatex (ClashRule bprs f)        = "Clash: " ++ (show bprs) ++ " " ++ (show f)


--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _ _)     -> R_Conj
              (DiaRule _ _ _)    -> R_Dia
              (DisjRule _ _)     -> R_Disj
              (SemBrRule _ _)    -> R_SemBr
              (AtRule _ _ )      -> R_At
              (DownRule _ _ _)   -> R_Down
              (ExistModRule _ _) -> R_Exist
              (DiffRule _ )      -> R_Diff
              (DiscardRule _)    -> R_Discard
              (ClashRule _ _)    -> R_Clash

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRules :: Branch -> CmdLineParams -> BranchingPrefix -> [Rule]
applicableRules br clp d = -- d = current depth in the tableau (add as dependency for branching rules)
                           (applicableConjRules br)
 ++                        (applicableAtRules br)
 ++                        (applicableDiaRules br)
 ++                        (applicableExistRules br)
 ++                        (applicableDiffRules br)
 ++                        (applicableDownRules br)
 ++  if semBranch clp then (applicableSemBrRules clp br d)
                      else (applicableDisjRules clp br d)

applicableConjRules :: Branch -> [Rule]
applicableConjRules br = [conjRule f br | f <- Set.toAscList $ conjStr br]

applicableDiaRules :: Branch -> [Rule]
applicableDiaRules br = [diaRule f br | f@(PrFormula pr _ _) <- Set.toAscList $ diaStr br, isNotBlocked br pr]
                        -- TODO memoization for the isNotBlocked call

applicableDisjRules :: CmdLineParams -> Branch -> BranchingPrefix -> [Rule]
applicableDisjRules clp br d = [disjRule clp f br d | f <- Set.toAscList $ disjStr br]

applicableSemBrRules :: CmdLineParams -> Branch -> BranchingPrefix -> [Rule]
applicableSemBrRules clp br d = [semBrRule clp f br d | f <- Set.toAscList $ disjStr br]

applicableAtRules :: Branch -> [Rule]
applicableAtRules br = [atRule f br | f <- Set.toAscList $ atStr br]

applicableDownRules :: Branch -> [Rule]
applicableDownRules br = [downRule f br | f <- Set.toAscList $ downStr br]

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
applyMod clp br (BM_AddFormulas li)              = addFormulas clp br li False
applyMod clp br (BM_AddAccFormula accFor)        = addAccFormula clp br accFor
applyMod  _  br (BM_AddDiaRuleCheck pr f)        = BranchOK (addDiaRuleCheck br pr f)
applyMod  _  br (BM_AddDownRuleCheck pr f)       = BranchOK (addDownRuleCheck br pr f)
applyMod clp br (BM_CreateNewPref)               = createNewPref clp br
applyMod  _  br (BM_CreateNewProp)               = BranchOK $ createNewProp br
applyMod  _  br (BM_CreateNewNomTestRelevance f) = BranchOK $ createNewNomTestRelevance br f
applyMod  _  br (BM_RemFormula f)                = BranchOK (remFormula br f)
applyMod  _  br (BM_AddDiffRuleCheck f prop b)   = BranchOK (addDiffRuleCheck br f prop b)
applyMod  _  br (BM_AddParentPrefix son father)  = BranchOK (addParentPrefix br son father)
applyMod  _  br (BM_Clash bprs (PrFormula pr bprs2 f)) = BranchClash br pr (bps_union bprs bprs2) f

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

--

getNewNom :: Branch -> NomSymbol
getNewNom br = maybe (NomSymbol 0) incNomSymbol (lastNom br)

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
disjRule :: CmdLineParams -> PrFormula -> Branch -> BranchingPrefix -> Rule
disjRule clp df@(PrFormula pr bprs (Dis fs)) br d
  = if not $ unitProp clp
     then DisjRule df (breakDisj df d)
     else case reduceDisjunctionAgainstBranch br pr fs of
             Triviality                 -> DiscardRule df
             Contradiction brps_clash   -> ClashRule (bps_union bprs brps_clash) df
             Reduced new_bprs disjuncts -> DisjRule df (prefixList pr (bps_insert d $ bps_union bprs new_bprs) disjuncts)
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"

-- semantic branching
semBrRule :: CmdLineParams -> PrFormula -> Branch -> BranchingPrefix -> Rule    -- todo : unit propagation, part 2 (b)
semBrRule clp df@(PrFormula pr bprs (Dis fs)) br d
-- = SemBrRule df (sbModList disjointed) where disjointed = breakDisj df d
 = if not $ unitProp clp
    then SemBrRule df (sbModList $ breakDisj df d)
    else case reduceDisjunctionAgainstBranch br pr fs of
            Triviality                 -> DiscardRule df
            Contradiction brps_clash   -> ClashRule (bps_union bprs brps_clash) df
            Reduced new_bprs disjuncts -> SemBrRule df (sbModList $ prefixList pr (bps_insert d $ bps_union bprs new_bprs) disjuncts)
-- todo same remark as above
semBrRule _ _ _ _ = error "sembrRule"


sbModList ::  [PrFormula] -> [[PrFormula]]
sbModList fs = go fs []
 where go :: [PrFormula] -> [PrFormula] -> [[PrFormula]]
       go (hd:tl) negated = 
           (hd:negated):(go tl ((neg_ hd):negated))
           where neg_ (PrFormula pr bprs f) = PrFormula pr bprs (neg f)
       go [] _ = []



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

-- down
downRule :: PrFormula -> Branch -> Rule
downRule df@(PrFormula pr bprs (Down v f)) br
 = DownRule df (PrFormula pr bprs (replaceVar v newNom f)) (PrFormula pr bprs $ Lit $ PosLit $ N newNom)
    where newNom = getNewNom br
downRule _ _ = error "downRule error"

