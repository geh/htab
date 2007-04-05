----------------------------------------------------
--                                                --
-- Structures.hs:                                 --
-- Structures used in the calculus.               --
--                                                --
----------------------------------------------------


module Structures where

-- Formulas are put in different lists depending on their kind
-- literal formulas, conjunctions, disjunctions, diamond, boxes,
-- and accessibility formulas
-- The highest prefix is also stored.

-- Each formula is prefixed

-- There is always one way of knowing that a rule has been applied:
-- for ^ , <> and v : as soon as a formula is used, it is deleted
-- for [] : we remember if a couple (accessibility formula, box formula) has
--          been treated, by storing it in a special list in the structure

import Formula
import Data.List
import qualified Data.Map as Map

type Clasher = PrFormula
data StructInfo = StructOK SetOfStructures |
                  StructClash SetOfStructures Clasher


-- Lit structure is a Map, because it's easier to detect clashed
-- by looking if there is already something at the (prefix, prop) place
-- and if what is there contradicts what we want to add

data Lit_structure = Lit_structure (Map.Map (Prefix,Atom) Bool)
type Conj_structure = [PrFormula]
type Disj_structure = [PrFormula]
type Dia_structure  = [PrFormula]
type Box_structure  = [PrFormula]
type Acc_structure  = [AccFormula]             -- accessibility relations
type Box_rule_chart = [(PrFormula,AccFormula)]

instance Show Lit_structure where
 show (Lit_structure ls) = "[" ++ (join "," [litStructShowElem pair  | pair <- pairs]) ++ "]"
                           where pairs = Map.assocs ls

litStructShowElem :: ((Prefix,Atom),Bool) -> String
litStructShowElem pair =
    if (snd pair) == True then (show (fst (fst pair))) ++ ":" ++ (show (snd (fst pair)))
                          else (show (fst (fst pair))) ++ ":!" ++ (show (snd (fst pair)))

join :: String -> [String] -> String
join s (hd:tl) = hd ++ s ++ (join s tl)
join _ [] = ""

data SetOfStructures = SetOf {  litStr :: Lit_structure,
                               conjStr :: Conj_structure,
                               disjStr :: Disj_structure,
                                diaStr :: Dia_structure,
                                boxStr :: Box_structure,
                                accStr :: Acc_structure,
                               boxRlCh :: Box_rule_chart,
                                lastPr :: Prefix }

--

emptyStructs :: SetOfStructures
emptyStructs = SetOf
                { litStr= Lit_structure (Map.empty::Map.Map (Prefix,Atom) Bool),
                  conjStr=[],
                  disjStr=[],
                  diaStr=[],
                  boxStr=[],
                  accStr=[],
                  boxRlCh=[],
                  lastPr=0 }

instance Show SetOfStructures where
    show sos = "Literals:"          ++ show (litStr sos)   ++
               "\nConjunctions: "   ++ show (conjStr sos)  ++
               "\nDisjunctions: "   ++ show (disjStr sos)  ++
               "\nDiamonds: "       ++ show (diaStr sos)   ++
               "\nBoxes: "          ++ show (boxStr sos)   ++
               "\nAccesibility: "   ++ show (accStr sos)   ++
               "\nBox rule chart: " ++ show (boxRlCh sos)  ++
               "\nBiggest prefix: " ++ show (lastPr sos)



-- takes a formula, looks what kind it is, put it in the right sub-structure
addFormula :: SetOfStructures -> PrFormula -> StructInfo

addFormula sos f@(PrFormula _ (Con _))
           = StructOK sos{conjStr = (f:(conjStr sos))}

addFormula sos f@(PrFormula _ (Dis _))
           = StructOK sos{disjStr = (f:(disjStr sos))}

addFormula sos f@(PrFormula _ (Box _ _))
           = StructOK sos{boxStr = (f:(boxStr sos))}

addFormula sos f@(PrFormula _ (Dia _ _))
           = StructOK sos{diaStr = (f:(diaStr sos))}

addFormula sos f@(PrFormula pr (PosLit a))
           = case (updateMap (litStr sos) (pr,a) True) of
              Just m  -> StructOK sos{litStr = m}
              Nothing -> StructClash sos f

addFormula sos f@(PrFormula pr (NegLit a))
           = case (updateMap (litStr sos) (pr,a) False) of
              Just m  -> StructOK sos{litStr = m}
              Nothing -> StructClash sos f


addFormula _ _ = error $ "unimplemented formula"



updateMap :: Lit_structure -> (Prefix,Atom) -> Bool -> Maybe Lit_structure
updateMap (Lit_structure m) (pre,Taut) True
    = Just (Lit_structure (Map.insert (pre,Taut) True m))

updateMap (Lit_structure m) (pre,Taut) False
    = Nothing

updateMap (Lit_structure m) (pre,atom) b
    = case (Map.lookup (pre,atom) m) of
       Just b2 -> if b == b2 then Just (Lit_structure m)
                             else Nothing                   -- clash!
       Nothing -> Just (Lit_structure (Map.insert (pre,atom) b m))


--

addFormulas :: SetOfStructures -> [PrFormula] -> StructInfo
addFormulas sos (hd:tl) = case (addFormula sos hd) of
                           StructOK sos2        -> addFormulas sos2 tl
                           si@(StructClash _ _) -> si

addFormulas sos [] = StructOK sos

--

addAccFormula :: SetOfStructures -> AccFormula -> SetOfStructures
addAccFormula sos f = sos{accStr=(f:(accStr sos))}

--

addBoxRuleCheck :: SetOfStructures -> (PrFormula,AccFormula) -> SetOfStructures
addBoxRuleCheck sos c = sos{boxRlCh=(c:(boxRlCh sos))}

--

incLastPr :: SetOfStructures -> SetOfStructures
incLastPr sos = sos{lastPr = ((lastPr sos)+1)}

--

remFormula :: SetOfStructures  -> PrFormula -> SetOfStructures
remFormula sos f@(PrFormula _ (Con _)) = sos{conjStr=(delete f (conjStr sos))}
remFormula sos f@(PrFormula _ (Dia _ _)) = sos{diaStr=(delete f (diaStr sos))}
remFormula sos f@(PrFormula _ (Dis _)) = sos{disjStr=(delete f (disjStr sos))}
remFormula _ _ = error $ "Want to delete a formula that shouldn't"
