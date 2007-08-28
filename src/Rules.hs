module Rules where

import Formula
import Branch(Branch(..), incLastPr, BranchInfo(..),
              addFormulas, addAccFormula, remFormula, addBoxRuleCheck, BoxRuleCheck)
import CommandLine(CmdLineParams, semBranch, fullClash)
import RuleMetadata(RuleId(..))
import LatexOutput()
import LatexOutputHelper

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddBoxRuleCheck (PrFormula,AccFormula)
                           | BM_RemFormula PrFormula
                           | BM_IncLastPr

data Rule =  ConjRule   PrFormula [PrFormula]
           | DiaRule    PrFormula AccFormula PrFormula
           | BoxRule    BoxRuleCheck PrFormula
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
    where showLat (pr,acc) = "(" ++ (math $ showLatex pr) ++ "," ++ (math $ showLatex acc) ++ ")"
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

applicableRules :: Branch -> CmdLineParams -> [Rule]
applicableRules br clp =  ( if fullClash clp then (applicableNegRules br)
                                            else [] )
                        ++ (applicableConjRules br)
                        ++ (applicableDiaRules br)
                        ++ (applicableBoxRules br)
                        ++ (applicableAtRules br)
                        ++ (applicableNegNomRules br)
                        ++ if semBranch clp then (applicableSemBrRules br)
                                            else (applicableDisjRules br)



applicableConjRules :: Branch -> [Rule]
applicableConjRules br = [conjRule f br | f <- (conjStr br)]

applicableDiaRules :: Branch -> [Rule]
applicableDiaRules br = [diaRule f br | f <- (diaStr br)]


applicableBoxRules :: Branch -> [Rule]
applicableBoxRules br
  = [boxRule prF accF br | (prF,accF) <- (unCheckedBoxPairs br)]

applicableDisjRules :: Branch -> [Rule]
applicableDisjRules br = [disjRule f br | f <- (disjStr br)]

applicableSemBrRules :: Branch -> [Rule]
applicableSemBrRules br = [semBrRule f br | f <- (disjStr br)]

applicableNegRules :: Branch -> [Rule]
applicableNegRules br = [negRule f br | f <- (negStr br)]

applicableAtRules :: Branch -> [Rule]
applicableAtRules br = [atRule f br | f <- (atStr br)]

applicableNegNomRules :: Branch -> [Rule]
applicableNegNomRules br = [negNomRule f br | f <- (negNomStr br)]

unCheckedBoxPairs :: Branch -> [(PrFormula,AccFormula)]
unCheckedBoxPairs br
  = [(boxF,accF) | boxF@(PrFormula p1 (Box r1 _)) <- (boxStr br),
                   accF@(AccFormula r2 p2 _) <- (accStr br),
                   p1 == p2 , r1 == r2,
                   notElem (boxF,accF) (boxRlCh br)]
--

applyRule :: CmdLineParams -> Rule -> Branch -> [BranchInfo]
applyRule clp rule br = applySetOfMods clp (getMods rule) br


applySetOfMods :: CmdLineParams -> [[BranchModification]] -> Branch -> [BranchInfo]
applySetOfMods clp (hd:tl) br = (applyMods clp hd br):(applySetOfMods clp tl br)
applySetOfMods _ [] _ = []


applyMods :: CmdLineParams -> [BranchModification] -> Branch -> BranchInfo
applyMods clp (hd:tl) br = case (applyMod clp hd br) of
                            BranchOK br2         -> applyMods clp tl br2
                            si@(BranchClash _ _) -> si
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
breakConj (PrFormula pr (Con formulaList)) = prefixList pr formulaList
breakConj _ = error $ "breakConj error"


-- dia
diaRule :: PrFormula -> Branch -> Rule
diaRule f@(PrFormula pr (Dia r f2)) br
  = DiaRule f (AccFormula r pr newPr) (prefix newPr f2)
      where newPr = getNewPr br
diaRule _ _ = error $ "diaRule"

--
getNewPr :: Branch -> Prefix
getNewPr br = (lastPr br)+1

-- box
boxRule :: PrFormula -> AccFormula -> Branch -> Rule
boxRule bf@(PrFormula pr0 (Box r1 f2)) af@(AccFormula r2 pr1 pr2) _
 | (pr0 == pr1) && (r1 == r2) =
 BoxRule (bf,af) (prefix pr2 f2)

boxRule _ _ _ = error $ "boxrule error"

-- disjunction

disjRule :: PrFormula -> Branch -> Rule
disjRule df _ = DisjRule df (breakDisj df)

breakDisj :: PrFormula -> [PrFormula]
breakDisj (PrFormula pr (Dis formulaList)) = prefixList pr formulaList
breakDisj _ = error $ "breakDisj error"

-- disjunction with semantic branching

semBrRule :: PrFormula -> Branch -> Rule
semBrRule df _ = SemBrRule df (sbModList df disjointed [])
                  where disjointed = (breakDisj df)

sbModList :: PrFormula -> [PrFormula] -> [PrFormula] -> [[PrFormula]]
sbModList df (hd_disj:tl_disj) negated =  (hd_disj:negated):(sbModList df tl_disj ((negPr hd_disj):negated))
                                          where negPr (PrFormula pr f) = PrFormula pr (neg f)
sbModList _ [] _ = []

-- @
atRule :: PrFormula -> Branch -> Rule
atRule af@(PrFormula _ (At n f)) br
 = AtRule af (prefix newPr (PosLit (N n))) (prefix newPr f)
    where newPr = getNewPr br

atRule _ _ = error "atRule error"

-- ¬a
negNomRule :: PrFormula -> Branch -> Rule
negNomRule f@(PrFormula _ (NegLit n@(N _))) br
 = NegNomRule f (prefix newPr (PosLit n))
    where newPr = getNewPr br

negNomRule _ _ = error "negNomRule error"

-- negation
negRule :: PrFormula -> Branch -> Rule
negRule nf@(PrFormula pr (Neg f)) _ = NegRule nf (PrFormula pr (neg1 f))

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

