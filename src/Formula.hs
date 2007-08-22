----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module Formula where

import LatexOutputHelper

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


instance ShowLatex (PrFormula, AccFormula) where
 showLatex (pr,acc) = "(" ++ (math $ showLatex pr) ++ "," ++ (math $ showLatex acc) ++ ")"


{- showInfixOp: Given

   - a string for an infix operator
   - a list of formulas corresponding to n succesive
     applications of the infix operator

  returns a string for that formula
-}

showInfixOp :: String -> [Formula] -> String

showInfixOp _ []            = ""
showInfixOp op (h1:(h2:tl)) = (show h1) ++ op ++ (showInfixOp op (h2:tl))
showInfixOp _ [h]           = show h

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




-- the following functions are taken from hylores but with the sorting stuff
-- removed -->
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

-- <--


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


{- isComplementaryLiteralOf: Given

  - a @-formula f
  - a @-formula g

  returns True iff f is of the form @_n -a and g is of the form @_n a or
  viceversa. The name of this function makes more sense when used as an
  infix operator :)
-}
isComplementaryLiteralOf :: Formula -> Formula -> Bool
isComplementaryLiteralOf (At n (NegLit a)) (At n' (PosLit a')) = (n == n') && (a == a')
isComplementaryLiteralOf (At n (PosLit a)) (At n' (NegLit a')) = (n == n') && (a == a')
isComplementaryLiteralOf  _                 _                  = False


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
