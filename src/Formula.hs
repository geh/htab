----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module Formula

(PropSymbol(..), NomSymbol(..), StateVar,
RelSymbol(..), Rel, Prefix,
Formula(..), Atom(..),
BranchingPrefix, BranchingPrefixes,
bps_union, bps_unions, bps_insert, bps_member,
bps_empty, deps_min, PrFormula(..), AccFormula(..),
LanguageInfo(..),
nnf, neg, isTrue, isFalse,
NewToOldNomsMap, renameNominals,
box, diamond, at, conj, disj, taut,
dimp, imp,
prop, nom, formulaLanguageInfo, prefixList ,
firstPrefixedFormula
)


 where

import LatexOutputHelper
import qualified Data.Set as Set
import Data.List(elemIndex)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map

import HyLo.Signature.Simple( PropSymbol(..),
                              NomSymbol(..),
                              RelSymbol(..),
                              StateVar)
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


instance ShowLatex Formula where
   showLatex (PosLit a) = showLatex a
   showLatex (NegLit a) = "\\neg(" ++ showLatex a ++ ")"
   showLatex (Con fs)   = "(" ++ (separate "\\wedge " fs) ++ ")"
   showLatex (Dis fs)   = "(" ++ (separate "\\vee " fs) ++ ")"
   showLatex (At n f)   = "@_{" ++ (show n) ++ "}"  ++ (showLatex f)
   showLatex (Box r f)  = "\\square_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Dia r f)  = "\\lozenge_{" ++ (show r)  ++ "}" ++ (showLatex f)
   showLatex (Neg f)    = "\\neg" ++ showLatex f

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
  =  case IntSet.toList deps of  -- with GHC 6.8.1 , use IntSet.toAscList
       [] -> 0
       l  -> minimum l           -- (hd:_) -> hd

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
box        = Box
diamond    = Dia

{- Hybrid operators -}
at             :: NomSymbol -> Formula -> Formula

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

formulaLanguageInfo :: Formula -> LanguageInfo
formulaLanguageInfo = countNominals

countNominals :: Formula -> Int
countNominals f = Set.size $ extractNominals f 

extractNominals :: Formula -> Set.Set NomSymbol
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

type NewToOldNomsMap = Map.Map NomSymbol NomSymbol


renameNominals :: Formula -> (Formula, NewToOldNomsMap)
renameNominals f = (newFormula, newToOldNomsMap)
                    where rawRenamed      = renameNominals_ f []
                          newFormula      = fst rawRenamed
                          newToOldNomsMap = convertNomListInMap $ snd rawRenamed


convertNomListInMap :: [NomSymbol] -> NewToOldNomsMap
-- the initial name of the nominals are the one of the nominals in the list
-- the new name of the nominals are their place in the list
-- ( the list has unique elements )
convertNomListInMap l = foldr (\(new_nom, old_nom) map_ -> Map.insert  new_nom old_nom map_) Map.empty (zip (map NomSymbol [0..]) l)

-- scans the whole formula, building a list of Nominals in the order of which they
-- have been found, and replace each nominal by its place in the list

renameNominals_ :: Formula -> [NomSymbol] -> (Formula,[NomSymbol])
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

indexInNominalList :: NomSymbol -> [NomSymbol] -> (NomSymbol,[NomSymbol])
indexInNominalList n l =  case (elemIndex n l) of
                           Just i  -> (NomSymbol i,l)
                           Nothing -> (NomSymbol (length l), l++[n])

renameNominals_formulas :: [Formula] -> [NomSymbol] -> ([Formula],[NomSymbol])
renameNominals_formulas (hd:tl) l = ((newHd:newTl),newDeepL)
      where (newHd,newL) = (renameNominals_ hd l)
            (newTl,newDeepL) =  renameNominals_formulas tl newL

renameNominals_formulas [] l = ([],l)

