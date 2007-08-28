----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module Formula where

import LatexOutputHelper
import qualified Data.Set as Set
import Data.List(elemIndex)

type Prop = Int
type Rel  = Int
type Level = Int
type Nominal = Int
type Prefix = Int

data Atom = Taut
          | N Nominal
          | P Prop
  deriving(Eq, Ord)
instance Show Atom where
 show (Taut) = "T"
 show (N n) = "N"++(show n)
 show (P p) = "P"++(show p)

instance ShowLatex Atom where
 showLatex (Taut) = "T"
 showLatex (N n) = "N_{" ++(show n) ++ "}"
 showLatex (P p) = "P_{" ++(show p) ++ "}"


data Formula
     = PosLit Atom
     | NegLit Atom
     | Con   [Formula]
     | Dis   [Formula]
     | At     Nominal Formula
     | Box    Rel     Formula
     | Dia    Rel     Formula
     | Neg Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (PosLit a) = show a
 show (NegLit a) = "!(" ++ show a ++ ")"
 show (Con fs)   = "^" ++ (show fs)
 show (Dis fs)   = "v" ++ (show fs)
 show (At n f)   = "@" ++ (show n)  ++ (show f)
 show (Box r f)  = "[R" ++ (show r)  ++ "]" ++ (show f)
 show (Dia r f)  = "<R" ++ (show r)  ++ ">" ++ (show f)
 show (Neg f)    = "!" ++ show f


instance ShowLatex Formula where
   showLatex (PosLit a) = showLatex a
   showLatex (NegLit a) = "\\neg(" ++ showLatex a ++ ")"
   showLatex (Con fs)   = "(" ++ (separate "\\wedge " fs) ++ ")"
   showLatex (Dis fs)   = "(" ++ (separate "\\vee " fs) ++ ")"
   showLatex (At n f)   = "@_{" ++ (show n) ++ "}"  ++ (showLatex f)
   showLatex (Box r f)  = "\\square_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Dia r f)  = "\\lozenge_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Neg f)    = "\\neg" ++ showLatex f


data PrFormula = PrFormula Prefix Formula
 deriving (Eq, Ord)

instance Show PrFormula where
 show (PrFormula pr f) = (show pr)++":"++(show f)

instance ShowLatex PrFormula where
 showLatex (PrFormula pr f) = (show pr)++"{:}"++(showLatex f)

prefix :: Prefix -> Formula -> PrFormula
prefix p f = PrFormula p f

prefixList :: Prefix -> [Formula] -> [PrFormula]
prefixList p fl = [(PrFormula p formula)|formula <-fl]

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
prop :: Prop -> Formula
nom  :: Nominal -> Formula

taut   = PosLit Taut
prop p = PosLit (P p)
nom  n = PosLit (N n)

{- Modalities -}
box, diamond :: Rel -> Formula -> Formula

box        = Box
diamond    = Dia


{- Hybrid operators -}
at             :: Nominal -> Formula -> Formula

at  _  f@(At _ _)    = f
at  n  f             = At n f


{- Conjunction and disjunction -}

conj, disj :: Formula -> Formula -> Formula

{- conjunctions and disjunctions are sorted to obtain a normal representation -}
conj    (Con xs) (Con ys) = Con (mergeAndNub xs ys)
conj     f     c@(Con  _) = conj c f
conj c@(Con xs)   f
    | isTrue f            = c
    | isFalse f           = neg taut
    | otherwise           = Con (insertAndNub f xs)
conj     f        f'
    | isTrue f            = f'
    | isFalse f           = neg taut
    | isTrue f'           = f
    | isFalse f'          = neg taut
    | otherwise           = skipSingleton Con (sortAndNub2 f f')

disj   (Dis xs)   (Dis ys) = Dis (mergeAndNub xs ys)
disj    f       c@(Dis  _) = disj c f
disj c@(Dis xs)    f
    | isTrue f             = taut
    | isFalse f            = c
    | otherwise            = Dis (insertAndNub f xs)
disj    f          f'
    | isTrue f             = taut
    | isFalse f            = f'
    | isTrue f'            = taut
    | isFalse f'           = f
    | otherwise            = skipSingleton Dis (sortAndNub2 f f')


skipSingleton :: ([Formula] -> Formula) -> [Formula] -> Formula
skipSingleton _ [x] = x
skipSingleton c xs  = c xs

mergeAndNub :: [Formula] -> [Formula] -> [Formula]
mergeAndNub xs         []         = xs
mergeAndNub []         ys         = ys
mergeAndNub xs@(x:xs') ys@(y:ys') = case compare x y of
                                      LT -> x:mergeAndNub xs' ys
                                      EQ -> x:mergeAndNub xs' ys'
                                      GT -> y:mergeAndNub xs  ys'

insertAndNub :: Formula -> [Formula] -> [Formula]
insertAndNub x []         = [x]
insertAndNub x ys@(y:ys') = case compare x y of
                              LT -> x:ys
                              EQ -> ys
                              GT -> y:insertAndNub x ys'

sortAndNub2 :: Formula -> Formula -> [Formula]
sortAndNub2 x y = case compare x y of
                    LT -> [x,y]
                    EQ -> [x]
                    GT -> [y,x]


{- Negation -}

neg :: Formula -> Formula
-- zero-step negation

neg (PosLit a)   = (NegLit a)
neg (NegLit a)   = (PosLit a)
neg (Neg f)      = f             -- avoids Neg Neg f
neg f            = Neg f

--

{- Prefixes for externalised calculus -}


{- Accessibility Formulas -}
-- of the kind i<>j with i and j prefixes
data AccFormula = AccFormula Rel Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula r p1 p2) = (show p1)++"<R"++(show r)++">"++(show p2)


instance ShowLatex AccFormula where
 showLatex (AccFormula r p1 p2) = (show p1)++"\\lozenge_{"++(show r)++"}"++(show p2)


{- isTrue: Given

  - a formula f

  returns True iff f is Taut, or is of the form @_n n or @_n Taut
-}
isTrue :: Formula -> Bool
isTrue (At n (PosLit (N m))) = (n==m)
isTrue (At _ (PosLit Taut))  = True
isTrue (PosLit Taut)         = True
isTrue  _                    = False


{- isFalse: Given

  - a formula f

  returns True iff f is -Taut, or is of the form @_n -n or @_n -Taut
-}
isFalse :: Formula -> Bool
isFalse (At n (NegLit (N m))) = (n==m)
isFalse (At _ (NegLit Taut))  = True
isFalse (NegLit Taut)         = True
isFalse  _                    = False


{-
 Put a formula into negative normal form
-}
-- negative normal form negation

nnf :: Formula -> Formula
nnf (Neg f) = nnf (neg2 f)
nnf (Con l) = Con (map nnf l)
nnf (Dis l) = Dis (map nnf l)
nnf (At n f) = At n (nnf f)
nnf (Box r f) = Box r (nnf f)
nnf (Dia r f) = Dia r (nnf f)
nnf (PosLit a) = PosLit a
nnf (NegLit a) = NegLit a

-- deep negation
-- digs until it finds another negation, or an atom
neg2 :: Formula -> Formula
neg2 (Con l)      = Dis (map neg2 l)
neg2 (Dis l)      = Con (map neg2 l)
neg2 (At n f)     = At n (neg2 f)
neg2 (Box r f)    = Dia r (neg2 f)
neg2 (Dia r f)    = Box r (neg2 f)
neg2 (PosLit a)   = (NegLit a)       --
neg2 (NegLit a)   = (PosLit a)       -- cases where it doesn't go deeper
neg2 (Neg f)      = f                --


type LanguageInfo = Int

-- currently : how many nominals has the formula
-- api may evolve ... (does it have past modalities ?...)
formulaLanguageInfo :: Formula -> LanguageInfo
formulaLanguageInfo = countNominals


countNominals :: Formula -> Int
countNominals f = Set.size $ extractNominals f 

extractNominals :: Formula -> Set.Set Nominal
extractNominals (PosLit (N n)) = Set.singleton n
extractNominals (NegLit (N n)) = Set.singleton n
extractNominals (Con fs) = Set.unions $ map extractNominals fs
extractNominals (Dis fs) = Set.unions $ map extractNominals fs
extractNominals (Dia _ f) = extractNominals f
extractNominals (Box _ f) = extractNominals f
extractNominals (Neg f) = extractNominals f
extractNominals (At n f) = Set.insert n $ extractNominals f
extractNominals _ = Set.empty

--

renameNominals :: Formula -> Formula
renameNominals f = fst $ renameNominals_ f []

-- scans the whole formula, building a list of Nominals in the order of which they
-- have been found, and replace each nominal by its place in the list

renameNominals_ :: Formula -> [Nominal] -> (Formula,[Nominal])
renameNominals_ (PosLit (N n)) l = (PosLit (N newN),newL)
      where (newN,newL) = indexInNominalList n l
renameNominals_ (NegLit (N n)) l = (NegLit (N newN),newL)
      where (newN,newL) = indexInNominalList n l
renameNominals_ (At n f) l = ((At newN newF),newNewL)
      where (newN,newL) = indexInNominalList n l
            (newF,newNewL) = renameNominals_ f newL
renameNominals_ (Dia r f) l = (Dia r newF,newL)
      where (newF,newL) = renameNominals_ f l
renameNominals_ (Box r f) l = (Box r newF,newL)
      where (newF,newL) = renameNominals_ f l
renameNominals_ (Neg f)  l = (Neg newF,newL)
      where (newF,newL) = renameNominals_ f l
renameNominals_ (Con fs) l = (Con newFs,newL)
      where (newFs,newL) =  (renameNominals_formulas fs l)
renameNominals_ (Dis fs) l = (Dis newFs,newL)
      where (newFs,newL) =  (renameNominals_formulas fs l)
renameNominals_ f l = (f,l)

indexInNominalList :: Nominal -> [Nominal] -> (Nominal,[Nominal])
indexInNominalList n l =  case (elemIndex n l) of
                           Just i  -> (i,l)
                           Nothing -> (length l, l++[n])

renameNominals_formulas :: [Formula] -> [Nominal] -> ([Formula],[Nominal])
renameNominals_formulas (hd:tl) l = ((newHd:newTl),newDeepL)
      where (newHd,newL) = (renameNominals_ hd l)
            (newTl,newDeepL) =  renameNominals_formulas tl newL

renameNominals_formulas [] l = ([],l)

