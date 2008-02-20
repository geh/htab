----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module HTab.Formula

(PropSymbol(..), NomSymbol(..), StateVar,
RelSymbol(..), Rel, Prefix,
Formula(..), Atom(..),
BranchingPrefix, BranchingPrefixes,
bps_union, bps_unions, bps_insert, bps_member,
bps_empty, deps_min, bps_show,
PrFormula(..), AccFormula(..),
LanguageInfo(..),
nnf, neg, isTrue, isFalse,
box, diamond, at, conj, disj, univMod, existMod,
dUnivMod, dExistMod,
taut, dimp, imp,
prop, nom, formulaLanguageInfo, prefixList ,
firstPrefixedFormula
)


 where

import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

import HyLo.Signature.Simple( PropSymbol(..),
                              NomSymbol(..),
                              RelSymbol(..),
                              StateVar)

import HTab.LatexOutputHelper

type Prefix = Int
type Rel = Int
data Atom = Taut
          | N NomSymbol
          | P PropSymbol
  deriving(Eq, Ord)

instance Show Atom where
 show (Taut) = "T"
 show (N n) = show n
 show (P p) = show p

instance ShowLatex Atom where
 showLatex (Taut) = "T"
 showLatex (N n) = show n
 showLatex (P p) = show p

data Formula
     = PosLit Atom
     | NegLit Atom
     | Con   [Formula]
     | Dis   [Formula]
     | At     NomSymbol Formula
     | Box    RelSymbol     Formula
     | Dia    RelSymbol     Formula
     | A      Formula
     | E      Formula
     | D      Formula
     | B      Formula
     | Neg Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (PosLit a) = show a
 show (NegLit a) = "!(" ++ show a ++ ")"
 show (Con fs)   = "^" ++ (show fs)
 show (Dis fs)   = "v" ++ (show fs)
 show (At n f)   = "@" ++ (show n)  ++ (show f)
 show (Box r f)  = "[" ++ (show r)  ++ "]" ++ (show f)
 show (Dia r f)  = "<" ++ (show r)  ++ ">" ++ (show f)
 show (Neg f)    = "!" ++ show f
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (D f)      = "D" ++ show f
 show (B f)      = "B" ++ show f

instance ShowLatex Formula where
   showLatex (PosLit a) = showLatex a
   showLatex (NegLit a) = "\\neg(" ++ showLatex a ++ ")"
   showLatex (Con fs)   = "(" ++ (lseparate "\\wedge " fs) ++ ")"
   showLatex (Dis fs)   = "(" ++ (lseparate "\\vee " fs) ++ ")"
   showLatex (At n f)   = "@_{" ++ (show n) ++ "}"  ++ (showLatex f)
   showLatex (Box r f)  = "\\square_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Dia r f)  = "\\lozenge_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Neg f)    = "\\neg" ++ showLatex f
   showLatex (A f)      = "A" ++ showLatex f
   showLatex (E f)      = "E" ++ showLatex f
   showLatex (D f)      = "D" ++ showLatex f
   showLatex (B f)      = "B" ++ showLatex f

--
-- Required structures to implement backjumping
--

type BranchingPrefix = Int
type BranchingPrefixes = IntSet.IntSet

bps_union :: BranchingPrefixes -> BranchingPrefixes -> BranchingPrefixes
bps_union  = IntSet.union

bps_unions :: [BranchingPrefixes] -> BranchingPrefixes
bps_unions = IntSet.unions

bps_insert :: BranchingPrefix -> BranchingPrefixes -> BranchingPrefixes
bps_insert = IntSet.insert

bps_member :: BranchingPrefix -> BranchingPrefixes -> Bool
bps_member = IntSet.member

bps_empty :: BranchingPrefixes
bps_empty  = IntSet.empty

deps_min :: BranchingPrefixes -> Int
deps_min deps
  =  case IntSet.toAscList deps of
       []    -> 0
       (hd:_)-> hd

bps_show :: BranchingPrefixes -> String
bps_show = show . IntSet.toList

data PrFormula = PrFormula Prefix BranchingPrefixes Formula
 deriving Eq

instance Ord PrFormula where
 compare (PrFormula pr1 deps1 f1) (PrFormula pr2 deps2 f2) =
  case (compare (deps_min deps1) (deps_min deps2)) of
   LT -> LT
   GT -> GT
   EQ -> compare (pr1,f1) (pr2,f2)

instance Show PrFormula where
 show (PrFormula pr bprs f) = (show pr)++":"++(show $ IntSet.toList bprs)++":"++(show f)

instance ShowLatex PrFormula where
 showLatex (PrFormula pr bprs f) = (show pr)++"{:}"++(show $ IntSet.toList bprs)++"{:}"++(showLatex f)

prefixList :: Prefix -> BranchingPrefixes -> [Formula] -> [PrFormula]
prefixList p bps fl = [(PrFormula p bps formula)|formula <-fl]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 bps_empty

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
prop :: PropSymbol -> Formula
nom  :: NomSymbol -> Formula

taut   = PosLit Taut
prop p = PosLit (P p)
nom  n = PosLit (N n)

{- Modalities -}
box, diamond :: RelSymbol -> Formula -> Formula
univMod, existMod, dUnivMod, dExistMod :: Formula -> Formula
box        = Box
diamond    = Dia
univMod    = A
existMod   = E
dUnivMod   = B
dExistMod  = D

{- Hybrid operators -}
at             :: NomSymbol -> Formula -> Formula
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

dimp :: Formula -> Formula -> Formula
dimp f1 f2 = conj (disj (neg f1) f2) (disj (neg f2) f1)

imp :: Formula -> Formula -> Formula
imp f1 f2 = disj (neg f1) f2

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

{- Accessibility Formulas -}
-- of the kind i<>j with i and j prefixes
data AccFormula = AccFormula BranchingPrefixes RelSymbol Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula bprs r p1 p2) = (showLatex bprs) ++ ":" ++ (show p1)++"<"++(show r)++">"++(show p2)


instance ShowLatex AccFormula where
 showLatex (AccFormula bprs r p1 p2) = (showLatex bprs) ++ ":" ++ (show p1)++"\\lozenge_{"++(show r)++"}"++(show p2)


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
nnf (A f) = A (nnf f)
nnf (E f) = E (nnf f)
nnf (D f) = D (nnf f)
nnf (B f) = B (nnf f)
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
neg2 (A f)        = E (neg2 f)
neg2 (E f)        = A (neg2 f)
neg2 (D f)        = B (neg2 f)
neg2 (B f)        = D (neg2 f)
neg2 (PosLit a)   = (NegLit a)       --
neg2 (NegLit a)   = (PosLit a)       -- cases where it doesn't go deeper
neg2 (Neg f)      = f                --

data LanguageInfo = LanguageInfo {   languageNoms :: [NomSymbol], -- ascending list
                                    languageProps :: [PropSymbol], -- ascending list 
                                     languageUniv :: Bool }
 deriving (Show)

formulaLanguageInfo :: Formula -> LanguageInfo
formulaLanguageInfo f
 = LanguageInfo {   languageNoms = noms,
                   languageProps = props,
                    languageUniv = hasUnivModality f }
    where noms = Set.toAscList $ extractNominals f
          props = Set.toAscList $ extractProps f

extractNominals :: Formula -> Set.Set NomSymbol
extractNominals (PosLit (N n)) = Set.singleton n
extractNominals (NegLit (N n)) = Set.singleton n
extractNominals (Con fs) = Set.unions $ map extractNominals fs
extractNominals (Dis fs) = Set.unions $ map extractNominals fs
extractNominals (Dia _ f) = extractNominals f
extractNominals (Box _ f) = extractNominals f
extractNominals (A f) = extractNominals f
extractNominals (E f) = extractNominals f
extractNominals (D f) = extractNominals f
extractNominals (B f) = extractNominals f
extractNominals (Neg f) = extractNominals f
extractNominals (At n f) = Set.insert n $ extractNominals f
extractNominals _ = Set.empty

extractProps :: Formula -> Set.Set PropSymbol
extractProps (PosLit (P p)) = Set.singleton p
extractProps (NegLit (P p)) = Set.singleton p
extractProps (Con fs) = Set.unions $ map extractProps fs
extractProps (Dis fs) = Set.unions $ map extractProps fs
extractProps (Dia _ f) = extractProps f
extractProps (Box _ f) = extractProps f
extractProps (A f) = extractProps f
extractProps (E f) = extractProps f
extractProps (D f) = extractProps f
extractProps (B f) = extractProps f
extractProps (Neg f) = extractProps f
extractProps (At _ f) = extractProps f
extractProps _ = Set.empty

hasUnivModality :: Formula -> Bool
hasUnivModality (Con fs)  = or $ map hasUnivModality fs
hasUnivModality (Dis fs)  = or $ map hasUnivModality fs
hasUnivModality (Dia _ f) = hasUnivModality f
hasUnivModality (Box _ f) = hasUnivModality f
hasUnivModality (Neg f)   = hasUnivModality f
hasUnivModality (At _ f)  = hasUnivModality f
hasUnivModality (A _)     = True
hasUnivModality (E _)     = True  -- will be ' hasUnivModality f ' when formulas are nnf
hasUnivModality (D _)     = True  -- |
hasUnivModality (B _)     = True  -- | TODO: really?
hasUnivModality _         = False -- PosLit , NegLit

