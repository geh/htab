module Rules where

import Formula
import Branch(Branch(..), BranchMonad, incLastPr, BranchInfo(..),
              addFormulas, addAccFormula, remFormula, addBoxRuleCheck,
              BranchData(..))
import CommandLine(CmdLineParams, semBranch, fullClash)
import Control.Monad.State(modify)
import RuleMetadata(RuleId(..))
import LatexOutput
import LatexOutputHelper

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddBoxRuleCheck (PrFormula,AccFormula)
                           | BM_RemFormula PrFormula
                           | BM_IncLastPr

data Rule =  ConjRule   [BranchModification]
           | DiaRule    [BranchModification]
           | BoxRule    [BranchModification]
           | DisjRule   [[BranchModification]]
           | SemBrRule  [[BranchModification]]
           | NegRule    [BranchModification]
           | AtRule     [BranchModification]
           | NegNomRule [BranchModification]

mods :: Rule -> [[BranchModification]]
mods (ConjRule setOfMods) = [setOfMods]
mods (DiaRule setOfMods) = [setOfMods]
mods (BoxRule setOfMods) = [setOfMods]
mods (DisjRule setOfSetOfMods) = setOfSetOfMods
mods (SemBrRule setOfSetOfMods) = setOfSetOfMods
mods (NegRule setOfMods) = [setOfMods]
mods (AtRule setOfMods) = [setOfMods]
mods (NegNomRule setOfMods) = [setOfMods]

instance Show Rule where
   show (ConjRule ((BM_RemFormula f):_)) = "conjunction : " ++ (show f)
   show (DiaRule ((BM_RemFormula f):_)) = "diamond : " ++ (show f)
   show (BoxRule ((BM_AddBoxRuleCheck f):_)) = "box : " ++ (show f)
   show (DisjRule (((BM_RemFormula f):((BM_AddFormulas l):_)):_)) = "disjunction : " ++ (show f) ++ " ,  " ++ (show l)
   show (SemBrRule (((BM_RemFormula f):_):_)) = "semantic branching : " ++ (show f)
   show (NegRule ((BM_RemFormula f):_)) = "negation : " ++ (show f)
   show (AtRule ((BM_RemFormula f):_)) = "at : " ++ (show f)
   show (NegNomRule ((BM_RemFormula f):_)) = "neg nom : " ++ (show f)
   show _ = error $ "show Rule"


instance ShowLatex Rule where
   showLatex (ConjRule ((BM_RemFormula f):_)) = "conjunction : " ++ (math $ showLatex f)
   showLatex (DiaRule ((BM_RemFormula f):_)) = "diamond : " ++ ( math $ showLatex f)
   showLatex (BoxRule ((BM_AddBoxRuleCheck f):_)) = "box : " ++ ( showLatex f)
   showLatex (DisjRule (((BM_RemFormula f):((BM_AddFormulas l):_)):_)) = "disjunction : " ++ (math $ showLatex f) ++ " ,  " ++ (math $ show l)
   showLatex (SemBrRule (((BM_RemFormula f):_):_)) = "semantic branching : " ++ (math $ showLatex f)
   showLatex (NegRule ((BM_RemFormula f):_)) = "negation : " ++ (math $ showLatex f)
   showLatex (AtRule ((BM_RemFormula f):_)) = "at : " ++ (math $ showLatex f)
   showLatex (NegNomRule ((BM_RemFormula f):_)) = "neg nom : " ++ (math $ showLatex f)
   showLatex _ = error $ "show Rule"


--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _)   -> R_Conj
              (DiaRule _)    -> R_Dia
              (BoxRule _)    -> R_Box
              (DisjRule _)   -> R_Disj
              (SemBrRule _)  -> R_SemBr
              (NegRule _)    -> R_Neg
              (AtRule _)     -> R_At
              (NegNomRule _) -> R_NegNom
--

howManyBranches :: Rule -> Int
howManyBranches (ConjRule _)  = 1
howManyBranches (DiaRule  _)  = 1
howManyBranches (BoxRule  _)  = 1
howManyBranches (NegRule _)   = 1
howManyBranches (AtRule _)   = 1
howManyBranches (NegNomRule _)   = 1
howManyBranches (DisjRule l)  = length l
howManyBranches (SemBrRule l) = length l


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
                   notElem (boxF,accF) (boxRlCh br),
                   r1 == r2 , p1 == p2]

--

applyRule :: CmdLineParams -> Rule -> Branch -> [BranchInfo]
applyRule clp rule br = applySetOfMods clp (mods rule) br


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
conjRule f _ = ConjRule [(BM_RemFormula f),
                         (BM_AddFormulas (breakConj f))]

breakConj :: PrFormula -> [PrFormula]
breakConj (PrFormula pr (Con formulaList)) = prefixList pr formulaList
breakConj _ = error $ "breakConj error"


-- dia
diaRule :: PrFormula -> Branch -> Rule
diaRule f@(PrFormula pr (Dia r f2)) br
  = DiaRule [(BM_RemFormula f),
             (BM_AddAccFormula (AccFormula r pr newPr)),
             (BM_AddFormulas [(prefix newPr f2)]),
             (BM_IncLastPr)]
            where newPr = getNewPr br
diaRule _ _ = error $ "diaRule"

--
getNewPr :: Branch -> Prefix
getNewPr br = (lastPr br)+1

-- box
boxRule :: PrFormula -> AccFormula -> Branch -> Rule
boxRule bf@(PrFormula pr0 (Box r1 f2)) af@(AccFormula r2 pr1 pr2) _
 | (pr0 == pr1) && (r1 == r2) = BoxRule [(BM_AddBoxRuleCheck (bf,af)),
                                   (BM_AddFormulas [(prefix pr2 f2)])]

boxRule _ _ _ = error $ "boxrule error"

-- disjunction

disjRule :: PrFormula -> Branch -> Rule
disjRule df _ = DisjRule [[(BM_RemFormula df),
                           (BM_AddFormulas [oneDisjointed])]
                          | oneDisjointed <- disjointed]
                where disjointed = (breakDisj df)

breakDisj :: PrFormula -> [PrFormula]
breakDisj (PrFormula pr (Dis formulaList)) = prefixList pr formulaList
breakDisj _ = error $ "breakDisj error"

-- disjunction with semantic branching

semBrRule :: PrFormula -> Branch -> Rule
semBrRule df _ = SemBrRule (sbModList df disjointed [])
                  where disjointed = (breakDisj df)

sbModList :: PrFormula -> [PrFormula] -> [PrFormula] -> [[BranchModification]]
sbModList df (hd_disj:tl_disj) negated =  [(BM_RemFormula df),
                                           (BM_AddFormulas [hd_disj]),
                                           (BM_AddFormulas negated)]:(sbModList df tl_disj ((negPr hd_disj):negated))

                                          where negPr (PrFormula pr f) = PrFormula pr (neg f)
sbModList _ [] _ = []

-- @
atRule :: PrFormula -> Branch -> Rule
atRule af@(PrFormula pr (At n f)) br
 = AtRule [(BM_RemFormula af),
           (BM_AddFormulas [(prefix newPr (PosLit (N n))),
                            (prefix newPr f)]),
           (BM_IncLastPr)]
    where newPr = getNewPr br

atRule _ _ = error "atRule error"

-- ¬a
negNomRule :: PrFormula -> Branch -> Rule
negNomRule f@(PrFormula pr (NegLit n@(N _))) br
 = NegNomRule [(BM_RemFormula f),
               (BM_AddFormulas [(prefix newPr (PosLit n))]),
               (BM_IncLastPr)]

    where newPr = getNewPr br

negNomRule _ _ = error "negNomRule error"

-- negation
negRule :: PrFormula -> Branch -> Rule
negRule nf@(PrFormula pr (Neg f)) _ = NegRule [(BM_RemFormula nf),
                                               (BM_AddFormulas [PrFormula pr (neg1 f)])]

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


{-
        Monad-related stuff
-}

applyNonBranchingRuleToMonad :: Rule -> BranchMonad ()
applyNonBranchingRuleToMonad r =
 modify (\bd -> case (branch_info bd) of
                 (BranchOK br) -> bd{branch_info=(applyMods (branch_clp bd) (head (mods r)) br)}
                 _             -> bd )
