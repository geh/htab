----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------


-- different from Formula.hs because we don't handle down-arrows
-- plan:
-- 0) Nothing works
-- 1) ML                  <- current stage
-- 2) HL(@)
-- 3) HL(@,A)
-- 4) HL(@,A,<>¯)

-- no multimodality support is planned


module Formula where

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

{- Only formulas in negated normal form can be built with these constructors -}
data Formula
     = PosLit Atom
     | NegLit Atom
     | Con   [Formula]
     | Dis   [Formula]
     | At     Nominal Formula
     | Box    Rel     Formula
     | Dia    Rel     Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (PosLit a) = show a
 show (NegLit a) = "!" ++ show a
 show (Con fs)   = "^" ++ (show fs)
 show (Dis fs)   = "v" ++ (show fs)
 show (At n f)   = "@" ++ (show n)  ++ (show f)
 show (Box r f)  = "[R" ++ (show r)  ++ "]" ++ (show f)
 show (Dia r f)  = "<R" ++ (show r)  ++ ">" ++ (show f)

--   show (Con tl)     = "(" ++ (showInfixOp " & " tl) ++ ")"
--   show (Dis tl)     = "(" ++ (showInfixOp " | " tl) ++ ")"



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

neg (PosLit a)   = (NegLit a)
neg (NegLit a)   = (PosLit a)
neg (Con l)      = Dis (map neg l)
neg (Dis l)      = Con (map neg l)
neg (At n f)     = at n (neg f)
neg (Box r f)    = Dia r (neg f)
neg (Dia r f)    = Box r (neg f)


{- Prefixes for externalised calculus -}


{- Accessibility Formulas -}
-- of the kind i<>j with i and j prefixes
data AccFormula = AccFormula Rel Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula r p1 p2) = "@"++(show p1)++"[R"++(show r)++"]"++(show p2)



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

