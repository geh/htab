module Rules where

import Formula
import Branch(Branch, BranchMonad, lastPr, incLastPr, BranchInfo(..),
              diaStr, boxStr, accStr, boxRlCh, conjStr, disjStr,
              addFormulas, addAccFormula, remFormula, addBoxRuleCheck,
              BranchData(..))
import CommandLine(CmdLineParams, semBranch)
import Control.Monad.State(modify)
import RuleMetadata(RuleId(..))

-- a "rule" is basically a list of modifications of the structures

data BranchModification =    BM_AddFormulas   [PrFormula]
                           | BM_AddAccFormula AccFormula
                           | BM_AddBoxRuleCheck (PrFormula,AccFormula)
                           | BM_RemFormula PrFormula
                           | BM_IncLastPr

data Rule =  ConjRule  [BranchModification]
           | DiaRule   [BranchModification]
           | BoxRule   [BranchModification]
           | DisjRule  [[BranchModification]]
           | SemBrRule [[BranchModification]]


mods :: Rule -> [[BranchModification]]
mods (ConjRule setOfMods) = [setOfMods]
mods (DiaRule setOfMods) = [setOfMods]
mods (BoxRule setOfMods) = [setOfMods]
mods (DisjRule setOfSetOfMods) = setOfSetOfMods
mods (SemBrRule setOfSetOfMods) = setOfSetOfMods

instance Show Rule where
   show (ConjRule ((BM_RemFormula f):_)) = "conjunction : " ++ (show f)
   show (DiaRule ((BM_RemFormula f):_)) = "diamond : " ++ (show f)
   show (BoxRule _) = "box"
   show (DisjRule (((BM_RemFormula f):_):_)) = "disjunction : " ++ (show f)
   show (SemBrRule (((BM_RemFormula f):_):_)) = "semantic branching : " ++ (show f)
   show _ = error $ "show Rule"


--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (ConjRule _)  -> R_ConjRule
              (DiaRule _)   -> R_DiaRule
              (BoxRule _)   -> R_BoxRule
              (DisjRule _)  -> R_DisjRule
              (SemBrRule _) -> R_SemBrRule
--

howManyBranches :: Rule -> Int
howManyBranches (ConjRule _) = 1
howManyBranches (DiaRule  _) = 1
howManyBranches (BoxRule  _) = 1
howManyBranches (DisjRule l) = length l
howManyBranches (SemBrRule l) = length l

-- is it a good idea to generate all the modifications done by each application of rule ??
-- of is it better to just say : rule that there, rule that there .. yes!

applicableRules :: Branch -> CmdLineParams -> [Rule]
applicableRules br clp =   (applicableConjRules br)
                        ++ (applicableDiaRules br)
                        ++ (applicableBoxRules br)
                        ++ if semBranch clp then (applicableSemBr br)
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

applicableSemBr :: Branch -> [Rule]
applicableSemBr br = [semBr f br | f <- (disjStr br)]


unCheckedBoxPairs :: Branch -> [(PrFormula,AccFormula)]
unCheckedBoxPairs br
  = [(boxF,accF) | boxF@(PrFormula p1 (Box r1 _)) <- (boxStr br),
                   accF@(AccFormula r2 p2 _) <- (accStr br),
                   notElem (boxF,accF) (boxRlCh br),
                   r1 == r2 , p1 == p2]

--

applyRule :: Rule -> Branch -> [BranchInfo]
applyRule rule br = applyMods (mods rule) br


-- the functions names really suck here :
applyMods :: [[BranchModification]] -> Branch -> [BranchInfo]
applyMods (hd:tl) br = (applyMods2 hd br):(applyMods tl br)
applyMods [] _ = []


applyMods2 :: [BranchModification] -> Branch -> BranchInfo
applyMods2 (hd:tl) br = case (applyMod hd br) of
                         BranchOK br2         -> applyMods2 tl br2
                         si@(BranchClash _ _) -> si

applyMods2 [] br = BranchOK br


applyMod :: BranchModification -> Branch -> BranchInfo
applyMod (BM_AddFormulas li) br = addFormulas br li
applyMod (BM_AddAccFormula accFor) br = BranchOK (addAccFormula br accFor)
applyMod (BM_AddBoxRuleCheck li) br = BranchOK (addBoxRuleCheck br li)
applyMod (BM_IncLastPr) br = BranchOK (incLastPr br)
applyMod (BM_RemFormula f) br = BranchOK (remFormula br f)



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

getNewPr :: Branch -> Prefix
getNewPr br = (lastPr br)+1

-- box
boxRule :: PrFormula -> AccFormula -> Branch -> Rule
boxRule bf@(PrFormula pr0 (Box r1 f2)) af@(AccFormula r2 pr1 pr2) _
 | (pr0 == pr1) && (r1 == r2) = BoxRule [(BM_AddFormulas [(prefix pr2 f2)]),
                (BM_AddBoxRuleCheck (bf,af))]

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

semBr :: PrFormula -> Branch -> Rule
semBr df _ = SemBrRule (sbModList df disjointed [])
              where disjointed = (breakDisj df)

sbModList :: PrFormula -> [PrFormula] -> [PrFormula] -> [[BranchModification]]
sbModList df (hd_disj:tl_disj) negated =  [(BM_RemFormula df),
                                           (BM_AddFormulas [hd_disj]),
                                           (BM_AddFormulas negated)]:(sbModList df tl_disj ((negPr hd_disj):negated))  -- la partie neg est a corriger

                                          where negPr (PrFormula pr f) = PrFormula pr (neg f)
sbModList _ [] _ = []


{-
        Monad-related stuff
-}

applyToMonad :: Rule -> BranchMonad ()
applyToMonad r =
 modify (\bd -> case (branch_info bd) of
                 (BranchOK br) -> bd{branch_info=(applyMods2 (head (mods r)) br)}
                 _             -> bd )
