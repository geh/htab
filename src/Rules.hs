module Rules where

import Formula
import Structures

-- a "rule" is basically a list of modifications of the structures

data StructModification =    SM_AddFormulas   [PrFormula]
                           | SM_AddAccFormula AccFormula
                           | SM_AddBoxRuleCheck (PrFormula,AccFormula)
                           | SM_RemFormula PrFormula
                           | SM_IncLastPr

-- type Rule =   [StructModification]
class Rule a where
 mods :: a -> [[StructModification]]
 txt :: a -> String

-- problem : maybe the coupling beetween the txt functions and the internals
--           of ConjRule, DiaRule ... should and could be avoided
data ConjRule = ConjRule [StructModification]
instance Rule ConjRule where
   mods (ConjRule setOfMods) = [setOfMods]
   txt (ConjRule ((SM_RemFormula f):_)) = "conjunction : " ++ (show f)
   txt _ = error $ "txt ConjRule"

data DiaRule = DiaRule [StructModification]
instance Rule DiaRule where
   mods (DiaRule setOfMods) = [setOfMods]
   txt (DiaRule ((SM_RemFormula f):_)) = "diamond : " ++ (show f)
   txt _ = error $ "txt DiaRule"

data BoxRule = BoxRule [StructModification]
instance Rule BoxRule where
   mods (BoxRule setOfMods) = [setOfMods]
   txt (BoxRule _) = "box"

data DisjRule = DisjRule [[StructModification]]
instance Rule DisjRule where
   mods (DisjRule setOfSetOfMods) = setOfSetOfMods
   txt (DisjRule (((SM_RemFormula f):_):_)) = "disjunction : " ++ (show f)
   txt _ = error $ "txt DisjRule"



-- to create heterogenous lists of Rules
-- idea taken here :
-- http://en.wikibooks.org/wiki/Haskell/Existentially_quantified_types

data RuleL = forall r. Rule r => RL r
instance Rule RuleL where
   mods (RL r) = mods r
   txt (RL r)  = txt r
instance Show RuleL where
   show (RL r) = txt r



-- is it a good idea to generate all the modifications done by each application of rule ??
-- of is it better to just say : rule that there, rule that there .. yes!

applicableRules :: SetOfStructures -> [RuleL]
applicableRules sos =    (applicableConjRules sos)
                      ++ (applicableDiaRules sos)
                      ++ (applicableBoxRules sos)
                      ++ (applicableDisjRules sos)


applicableConjRules :: SetOfStructures -> [RuleL]
applicableConjRules sos = [RL (conjRule f sos) | f <- (conjStr sos)]

applicableDiaRules :: SetOfStructures -> [RuleL]
applicableDiaRules sos = [RL (diaRule f sos) | f <- (diaStr sos)]


applicableBoxRules :: SetOfStructures -> [RuleL]
applicableBoxRules sos
  = [RL (boxRule prF accF sos) | (prF,accF) <- (unCheckedBoxPairs sos)]

applicableDisjRules :: SetOfStructures -> [RuleL]
applicableDisjRules sos = [RL (disjRule f sos) | f <- (disjStr sos)]


unCheckedBoxPairs :: SetOfStructures -> [(PrFormula,AccFormula)]
unCheckedBoxPairs sos
  = [(boxF,accF) | boxF@(PrFormula p1 (Box r1 _)) <- (boxStr sos),
                   accF@(AccFormula r2 p2 _) <- (accStr sos),
                   notElem (boxF,accF) (boxRlCh sos),
                   r1 == r2 , p1 == p2]

--

applyRule :: Rule a => a -> SetOfStructures -> [StructInfo]
applyRule rule sos = applyMods (mods rule) sos


-- the functions names really suck here :
applyMods :: [[StructModification]] -> SetOfStructures -> [StructInfo]
applyMods (hd:tl) sos = (applyMods2 hd sos):(applyMods tl sos)
applyMods [] _ = []


applyMods2 :: [StructModification] -> SetOfStructures -> StructInfo
applyMods2 (hd:tl) sos = case (applyMod hd sos) of
                          StructOK sos2        -> applyMods2 tl sos2
                          si@(StructClash _ _) -> si

applyMods2 [] sos = StructOK sos


applyMod ::StructModification -> SetOfStructures -> StructInfo
applyMod (SM_AddFormulas li) sos = addFormulas sos li
applyMod (SM_AddAccFormula accFor) sos = StructOK (addAccFormula sos accFor)
applyMod (SM_AddBoxRuleCheck li) sos = StructOK (addBoxRuleCheck sos li)
applyMod (SM_IncLastPr) sos = StructOK (incLastPr sos)
applyMod (SM_RemFormula f) sos = StructOK (remFormula sos f)



-- the actual rules and their helper functions

-- conjunction

-- takes 1 argument, the formula to remove
conjRule :: PrFormula -> SetOfStructures -> ConjRule
conjRule f _ = ConjRule [(SM_RemFormula f),
                         (SM_AddFormulas (breakConj f))]

breakConj :: PrFormula -> [PrFormula]
breakConj (PrFormula pr (Con formulaList)) = prefixList pr formulaList
breakConj _ = error $ "breakConj error"


-- dia
diaRule :: PrFormula -> SetOfStructures -> DiaRule
diaRule f@(PrFormula pr (Dia r f2)) sos
  = DiaRule [(SM_RemFormula f),
             (SM_AddAccFormula (AccFormula r pr newPr)),
             (SM_AddFormulas [(prefix newPr f2)]),
                              (SM_IncLastPr)]
            where newPr = getNewPr sos
diaRule _ _ = error $ "diaRule"

getNewPr :: SetOfStructures -> Prefix
getNewPr sos = (lastPr sos)+1

-- box
boxRule :: PrFormula -> AccFormula -> SetOfStructures -> BoxRule
boxRule bf@(PrFormula pr0 (Box r1 f2)) af@(AccFormula r2 pr1 pr2) _
 | (pr0 == pr1) && (r1 == r2) = BoxRule [(SM_AddFormulas [(prefix pr2 f2)]),
                (SM_AddBoxRuleCheck (bf,af))]

boxRule _ _ _ = error $ "boxrule error"

-- disjunction

disjRule :: PrFormula -> SetOfStructures -> DisjRule
disjRule df _ = DisjRule [[(SM_RemFormula df),
                           (SM_AddFormulas [oneDisjointed])]
                          | oneDisjointed <- disjointed]
                where disjointed = (breakDisj df)


breakDisj :: PrFormula -> [PrFormula]
breakDisj (PrFormula pr (Dis formulaList)) = prefixList pr formulaList
breakDisj _ = error $ "breakDisj error"

