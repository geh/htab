----------------------------------------------------
--                                                --
-- Branch.hs:                                     --
-- Branches used in the calculus.                 --
--                                                --
----------------------------------------------------


module Branch where

-- Formulas are put in different lists depending on their kind
-- literal formulas, conjunctions, disjunctions, diamond, boxes,
-- and accessibility formulas
-- The highest prefix is also stored.

-- Each formula is prefixed

-- There is always one way of knowing that a rule has been applied:
-- for ^ , <> and v : as soon as a formula is used, it is deleted
-- for [] : we remember if a couple (accessibility formula, box formula) has
--          been treated, by storing it in a special list in the branch


import Control.Monad.State(StateT, modify,MonadState, get)
import Data.List(delete)
import qualified Data.Map as Map

import Statistics(Statistics)
import CommandLine(CmdLineParams)
import Formula

--

type Clasher = PrFormula
data BranchInfo = BranchOK Branch |
                  BranchClash Branch Clasher

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

data Branch = Branch {  litStr :: Lit_structure,
                       conjStr :: Conj_structure,
                       disjStr :: Disj_structure,
                        diaStr :: Dia_structure,
                        boxStr :: Box_structure,
                        accStr :: Acc_structure,
                       boxRlCh :: Box_rule_chart,
                        lastPr :: Prefix }

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: Branch
emptyBranch = Branch
                { litStr= Lit_structure (Map.empty::Map.Map (Prefix,Atom) Bool),
                  conjStr=[],
                  disjStr=[],
                  diaStr=[],
                  boxStr=[],
                  accStr=[],
                  boxRlCh=[],
                  lastPr=0 }

instance Show Branch where
    show br = "Literals:"          ++ show (litStr br)   ++
              "\nConjunctions: "   ++ show (conjStr br)  ++
              "\nDisjunctions: "   ++ show (disjStr br)  ++
              "\nDiamonds: "       ++ show (diaStr br)   ++
              "\nBoxes: "          ++ show (boxStr br)   ++
              "\nAccesibility: "   ++ show (accStr br)   ++
              "\nBox rule chart: " ++ show (boxRlCh br)  ++
              "\nBiggest prefix: " ++ show (lastPr br)



-- takes a formula, looks what kind it is, put it in the right sub-structure
addFormula :: Branch -> PrFormula -> BranchInfo

addFormula br f@(PrFormula _ (Con _))
           = BranchOK br{conjStr = (f:(conjStr br))}

addFormula br f@(PrFormula _ (Dis _))
           = BranchOK br{disjStr = (f:(disjStr br))}

addFormula br f@(PrFormula _ (Box _ _))
           = BranchOK br{boxStr = (f:(boxStr br))}

addFormula br f@(PrFormula _ (Dia _ _))
           = BranchOK br{diaStr = (f:(diaStr br))}

addFormula br f@(PrFormula pr (PosLit a))
           = case (updateMap (litStr br) (pr,a) True) of
              Just m  -> BranchOK br{litStr = m}
              Nothing -> BranchClash br f

addFormula br f@(PrFormula pr (NegLit a))
           = case (updateMap (litStr br) (pr,a) False) of
              Just m  -> BranchOK br{litStr = m}
              Nothing -> BranchClash br f


addFormula _ _ = error $ "unimplemented formula"



updateMap :: Lit_structure -> (Prefix,Atom) -> Bool -> Maybe Lit_structure
updateMap (Lit_structure m) (pre,Taut) True
    = Just (Lit_structure (Map.insert (pre,Taut) True m))

updateMap (Lit_structure _) (_,Taut) False
    = Nothing

updateMap (Lit_structure m) (pre,atom) b
    = case (Map.lookup (pre,atom) m) of
       Just b2 -> if b == b2 then Just (Lit_structure m)
                             else Nothing                   -- clash!
       Nothing -> Just (Lit_structure (Map.insert (pre,atom) b m))


--

addFormulas :: Branch -> [PrFormula] -> BranchInfo
addFormulas br (hd:tl) = case (addFormula br hd) of
                          BranchOK br2         -> addFormulas br2 tl
                          bi@(BranchClash _ _) -> bi

addFormulas br [] = BranchOK br

--

addAccFormula :: Branch -> AccFormula -> Branch
addAccFormula br f = br{accStr=(f:(accStr br))}

--

addBoxRuleCheck :: Branch -> (PrFormula,AccFormula) -> Branch
addBoxRuleCheck br c = br{boxRlCh=(c:(boxRlCh br))}

--

incLastPr :: Branch -> Branch
incLastPr br = br{lastPr = ((lastPr br)+1)}

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ (Con _)) = br{conjStr=(delete f (conjStr br))}
remFormula br f@(PrFormula _ (Dia _ _)) = br{diaStr=(delete f (diaStr br))}
remFormula br f@(PrFormula _ (Dis _)) = br{disjStr=(delete f (disjStr br))}
remFormula _ _ = error $ "Want to delete a formula that shouldn't"


{-
    Monad related stuff
-}

data BranchData = BranchData { branch_info :: BranchInfo,
                               branch_clp :: CmdLineParams,
                               branch_path :: [Int]}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a

mAddAccFormula :: AccFormula -> BranchMonad ()
mAddAccFormula accf = modifyIfOk ((flip addAccFormula) accf)

mAddBoxRuleCheck :: (PrFormula,AccFormula) -> BranchMonad ()
mAddBoxRuleCheck brc = modifyIfOk ((flip addBoxRuleCheck) brc)

mIncLastPr :: BranchMonad ()
mIncLastPr  = modifyIfOk incLastPr

mRemFormula :: PrFormula -> BranchMonad ()
mRemFormula pf = modifyIfOk ((flip remFormula) pf)

modifyIfOk :: (Branch -> Branch) -> BranchMonad ()
modifyIfOk f = modify (\bd -> case (branch_info bd) of
                               (BranchOK br) -> bd{branch_info=(BranchOK (f br))}
                               _             -> bd)     -- do nothing

mAddFormulas ::  [PrFormula] -> BranchMonad ()
mAddFormulas pfs = modify (\bd -> case (branch_info bd) of
                                   (BranchOK br) -> bd{branch_info=(addFormulas br pfs)}
                                   _             -> bd)

--

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

--

getCLParams :: BranchMonad CmdLineParams
getCLParams = do bd <- get
                 return (branch_clp bd)