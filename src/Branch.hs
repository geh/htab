----------------------------------------------------
--                                                --
-- Branch.hs:                                     --
-- Branches used in the calculus.                 --
--                                                --
----------------------------------------------------


module Branch where

-- Formulas are put in different lists depending on their kind
-- conjunctions, disjunctions, diamond, boxes,
-- and accessibility formulas.
-- there is also a "seen" map to store every formula seen during
-- the calculus, if full clashing is enabled, and at least contains
-- literals even if full clashing is disabled.
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

data Seen_structure = Seen_structure (Map.Map (Prefix,Formula) Bool)
type Conj_structure = [PrFormula]
type Disj_structure = [PrFormula]
type Dia_structure  = [PrFormula]
type Box_structure  = [PrFormula]
type Neg_structure  = [PrFormula]
type Acc_structure  = [AccFormula]             -- accessibility relations
type Box_rule_chart = [(PrFormula,AccFormula)]

instance Show Seen_structure where
 show (Seen_structure ls) = "[" ++ (join "," [seenStructShowElem pair  | pair <- pairs]) ++ "]"
                           where pairs = Map.assocs ls

seenStructShowElem :: ((Prefix,Formula),Bool) -> String
seenStructShowElem pair =
    if (snd pair) == True then (show (fst (fst pair))) ++ ":" ++ (show (snd (fst pair)))
                          else (show (fst (fst pair))) ++ ":!" ++ (show (snd (fst pair)))

join :: String -> [String] -> String
join s (hd:tl) = hd ++ s ++ (join s tl)
join _ [] = ""

data Branch = Branch { seenStr :: Seen_structure,
                       conjStr :: Conj_structure,
                       disjStr :: Disj_structure,
                        diaStr :: Dia_structure,
                        boxStr :: Box_structure,
                        negStr :: Neg_structure,
                        accStr :: Acc_structure,
                       boxRlCh :: Box_rule_chart,
                        lastPr :: Prefix }

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: Branch
emptyBranch = Branch
                { seenStr= Seen_structure (Map.empty::Map.Map (Prefix,Formula) Bool),
                  conjStr=[],
                  disjStr=[],
                  diaStr=[],
                  boxStr=[],
                  negStr=[],
                  accStr=[],
                  boxRlCh=[],
                  lastPr=0 }

instance Show Branch where
    show br = "Seen formulas:"     ++ show (seenStr br)   ++
              "\nConjunctions: "   ++ show (conjStr br)  ++
              "\nDisjunctions: "   ++ show (disjStr br)  ++
              "\nDiamonds: "       ++ show (diaStr br)   ++
              "\nBoxes: "          ++ show (boxStr br)   ++
              "\nNegations: "      ++ show (negStr br)   ++
              "\nAccesibility: "   ++ show (accStr br)   ++
              "\nBox rule chart: " ++ show (boxRlCh br)  ++
              "\nBiggest prefix: " ++ show (lastPr br)



-- takes a formula, looks what kind it is, put it in the right sub-structure
addFormula :: Branch -> PrFormula -> BranchInfo

addFormula br f@(PrFormula pr f2@(Con _))
           = case (addAndUpdateMap br pr f f2 True) of
              BranchOK bok       -> BranchOK bok{conjStr = (f:(conjStr bok))}
              bc@(BranchClash _ _) -> bc

addFormula br f@(PrFormula pr f2@(Dis _))
           = case (addAndUpdateMap br pr f f2 True) of
              BranchOK bok       -> BranchOK bok{disjStr = (f:(disjStr bok))}
              bc@(BranchClash _ _) -> bc

addFormula br f@(PrFormula pr f2@(Box _ _))
           = case (addAndUpdateMap br pr f f2 True) of
              BranchOK bok       -> BranchOK bok{boxStr = (f:(boxStr bok))}
              bc@(BranchClash _ _) -> bc

addFormula br f@(PrFormula pr f2@(Dia _ _))
           = case (addAndUpdateMap br pr f f2 True) of
              BranchOK bok       -> BranchOK bok{diaStr = (f:(diaStr bok))}
              bc@(BranchClash _ _) -> bc

addFormula br f@(PrFormula pr (Neg f2))
           = case (addAndUpdateMap br pr f f2 False) of
              BranchOK bok       -> BranchOK bok{negStr = (f:(negStr bok))}
              bc@(BranchClash _ _) -> bc

addFormula br f@(PrFormula pr (PosLit a))
           = addAndUpdateMap br pr f (PosLit a) True

addFormula br f@(PrFormula pr (NegLit a))
           = addAndUpdateMap br pr f (PosLit a) False


addFormula _ _ = error $ "unimplemented formula"

--

addAndUpdateMap :: Branch -> Prefix -> PrFormula -> Formula -> Bool -> BranchInfo
addAndUpdateMap br pr f noNegF b = case (updateMap (seenStr br) (pr,noNegF) b) of
                                    Just m  -> BranchOK br{seenStr = m}
                                    Nothing -> BranchClash br f

updateMap :: Seen_structure -> (Prefix,Formula) -> Bool -> Maybe Seen_structure
updateMap (Seen_structure m) (pre,PosLit Taut) True
    = Just (Seen_structure (Map.insert (pre,PosLit Taut) True m))

updateMap (Seen_structure _) ( _ ,PosLit Taut) False
    = Nothing

updateMap (Seen_structure m) (pre,PosLit a) b
    = case (Map.lookup (pre,PosLit a) m) of
       Just b2 -> if b == b2 then Just (Seen_structure m)
                             else Nothing                   -- clash!
       Nothing -> Just (Seen_structure (Map.insert (pre,PosLit a) b m))

updateMap _ (_,NegLit _) _
    = error $ "shouldn't happen"

updateMap (Seen_structure m) (pre,f) b           -- Conj, Disj , Box, Dia, At
    = case (Map.lookup (pre,f) m) of
       Just b2 -> if b == b2 then Just (Seen_structure m)
                             else Nothing                   -- clash!
       Nothing -> Just (Seen_structure (Map.insert (pre,f) b m))

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
remFormula br f@(PrFormula _ (Con _))   = br{conjStr=(delete f (conjStr br))}
remFormula br f@(PrFormula _ (Dia _ _)) = br{diaStr=(delete f (diaStr br))}
remFormula br f@(PrFormula _ (Dis _))   = br{disjStr=(delete f (disjStr br))}
remFormula br f@(PrFormula _ (Neg _)  ) = br{negStr=(delete f (negStr br))}
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