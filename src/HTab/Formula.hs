----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module HTab.Formula

(PropSymbol(..), NomSymbol(..), StateVar(..),
RelSymbol(..), Rel, Prefix,
Formula(..), Literal(..), Atom(..),
BranchingPrefix, BranchingPrefixes,
bps_union, bps_unions, bps_insert, bps_member,
bps_empty, deps_min, bps_show,
PrFormula(..),showLess, AccFormula(..),
LanguageInfo(..), neg,
box, diamond, at, atv, conj, disj, univMod, existMod,
dUnivMod, dExistMod, taut, dimp, imp,
prop, nom, formulaLanguageInfo, prefixList,
checkIfVariableNegatedOnce, replaceVar,
firstPrefixedFormula,
parse
)


 where

import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

import HyLo.Signature.Simple( PropSymbol(..),
                              NomSymbol(..),
                              RelSymbol(..),
                              StateVar(..))

import qualified HyLo.InputFile as InputFile
import qualified HyLo.Formula as F

type Prefix = Int
type Rel = Int
data Atom = Taut
          | N NomSymbol
          | P PropSymbol
          | V StateVar
  deriving(Eq, Ord)

data Literal = PosLit Atom | NegLit Atom
  deriving(Eq, Ord)

instance Show Atom where
 show (Taut) = "T"
 show (N n) = show n
 show (P p) = show p
 show (V v) = show v

instance Show Literal where
 show (PosLit a) = show a
 show (NegLit a) =  "!" ++ show a

data Formula
     = Lit Literal
     | Con   [Formula]
     | Dis   [Formula]
     | At     NomSymbol Formula
     | Atv    StateVar  Formula
     | Down   StateVar  Formula
     | Box    RelSymbol     Formula
     | Dia    RelSymbol     Formula
     | A      Formula
     | E      Formula
     | D      Formula
     | B      Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (Lit a)    = show a
 show (Con fs)   = "^" ++ (show fs)
 show (Dis fs)   = "v" ++ (show fs)
 show (At n f)   = "@" ++ (show n)  ++ (show f)
 show (Atv v f)  = "@" ++ (show v)  ++ (show f)
 show (Box r f)  = "[" ++ (show r)  ++ "]" ++ (show f)
 show (Dia r f)  = "<" ++ (show r)  ++ ">" ++ (show f)
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (D f)      = "D" ++ show f
 show (B f)      = "B" ++ show f
 show (Down v f) = "down " ++ show v ++ "." ++ show f

parse :: String -> Formula
parse = convert . InputFile.parse

convert :: [F.Formula NomSymbol PropSymbol RelSymbol StateVar] -> Formula
convert fs = conv_ $ foldr (\f1 f2 -> f1 F.:&: f2) F.Top fs

conv_ :: F.Formula NomSymbol PropSymbol RelSymbol StateVar -> Formula
conv_ F.Top = taut
conv_ F.Bot = neg taut
conv_ (F.Prop p) = prop p
conv_ (F.Nom n) = nom n
conv_ (F.SVar v) = svar v
conv_ (F.Neg f) = neg $ conv_ f
conv_ (f1 F.:&: f2) = conj (conv_ f1) (conv_ f2)
conv_ (f1 F.:|: f2) = disj (conv_ f1) (conv_ f2)
conv_ (f1 F.:-->: f2) = imp (conv_ f1) (conv_ f2)
conv_ (f1 F.:<-->: f2) = dimp (conv_ f1) (conv_ f2)
conv_ (F.Diam r f) = diamond r (conv_ f)
conv_ (F.Box r f) = box r (conv_ f)
conv_ (F.At n f) = at n (conv_ f)
conv_ (F.Atv v f) = atv v (conv_ f)
conv_ (F.Down v f) = downArrow v (conv_ f)
conv_ (F.A f) = univMod (conv_ f)
conv_ (F.E f) = existMod (conv_ f)
conv_ (F.D f) = dExistMod (conv_ f)
conv_ (F.B f) = dUnivMod (conv_ f)

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

showLess :: PrFormula -> String
showLess (PrFormula pr _ f) = (show pr)++":"++(show f)

prefixList :: Prefix -> BranchingPrefixes -> [Formula] -> [PrFormula]
prefixList p bps fl = [(PrFormula p bps formula)|formula <-fl]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 bps_empty

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
prop :: PropSymbol -> Formula
nom  :: NomSymbol -> Formula
svar :: StateVar -> Formula

taut   = Lit $ PosLit Taut
prop p = Lit $ PosLit $ P p
nom  n = Lit $ PosLit $ N n
svar v = Lit $ PosLit $ V v

{- Modalities -}
box, diamond :: RelSymbol -> Formula -> Formula
univMod, existMod, dUnivMod, dExistMod :: Formula -> Formula
box        = Box
diamond    = Dia
univMod    = A
existMod   = E
dUnivMod   = B
dExistMod  = D

{- binder -}
downArrow :: StateVar -> Formula -> Formula
downArrow v f = Down v f

{- Hybrid operators -}
at :: NomSymbol -> Formula -> Formula
at  n  f    = At  n f
atv :: StateVar -> Formula -> Formula
atv v  f    = Atv v f

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
dimp f1 f2 = disj (conj f1 f2) (conj (neg f1) (neg f2))

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


{- Accessibility Formulas -}
-- of the kind i<>j with i and j prefixes
data AccFormula = AccFormula BranchingPrefixes RelSymbol Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula bprs r p1 p2) = (show bprs) ++ ":" ++ (show p1)++"<"++(show r)++">"++(show p2)

{- recognize trivial formulas to trim conjunctions and disjunctions -}
isTrue, isFalse :: Formula -> Bool
isTrue (Lit (PosLit Taut))  = True
isTrue  _                   = False
isFalse (Lit (NegLit Taut)) = True
isFalse  _                  = False


-- deep negation
-- digs until it finds another negation, or an atom
neg :: Formula -> Formula
neg (Con l)      = Dis (map neg l)
neg (Dis l)      = Con (map neg l)
neg (At n f)     = At   n (neg f)
neg (Atv v f)    = Atv  v (neg f)
neg (Down v f)   = Down v (neg f)
neg (Box r f)    = Dia  r (neg f)
neg (Dia r f)    = Box  r (neg f)
neg (A f)        = E (neg f)
neg (E f)        = A (neg f)
neg (D f)        = B (neg f)
neg (B f)        = D (neg f)
neg (Lit (PosLit a)) = Lit $ NegLit a --
neg (Lit (NegLit a)) = Lit $ PosLit a -- cases where it doesn't go deeper

data LanguageInfo = LanguageInfo {   languageNoms :: [NomSymbol], -- ascending list
                                     relevantNoms :: [NomSymbol],
                                    languageProps :: [PropSymbol], -- ascending list
                                     languageUniv :: Bool,
                                     languageDiff :: Bool,
                                     languageDown :: Bool }
 deriving (Show)

formulaLanguageInfo :: Formula -> LanguageInfo
formulaLanguageInfo f
 = LanguageInfo {   languageNoms = noms,
                    relevantNoms = relNoms,
                   languageProps = props,
                    languageUniv = hasUnivModality f,
                    languageDiff = hasDiffModality f,
                    languageDown = hasDownArrow f }

    where (allNoms_,relNoms_) = extractNominals f
          noms = Set.toAscList $ allNoms_
          relNoms = Set.toAscList relNoms_
          props = Set.toAscList $ extractProps f

-- composeXX functions follow the idea from
-- "A pattern for almost compositional functions", Bringert and Ranta.
composeFold :: b
            -> (b -> b -> b)
            -> (Formula -> b)
            -> (Formula -> b)
composeFold zero combine g = \e -> case e of
    Con fs     -> foldr1 combine $ map g fs
    Dis fs     -> foldr1 combine $ map g fs
    Dia _ f    -> g f
    Box _ f    -> g f
    At  _ f    -> g f
    Atv _ f    -> g f
    Down _ f   -> g f
    A f        -> g f
    E f        -> g f
    D f        -> g f
    B f        -> g f
    _          -> zero

composeMap :: (Formula -> Formula)
           -> (Formula -> Formula)
           -> (Formula -> Formula)
composeMap baseCase g = \e -> case e of
    Con fs     -> Con $ map g fs
    Dis fs     -> Dis $ map g fs
    Dia r f    -> Dia r (g f)
    Box r f    -> Box r (g f)
    At   i f   -> At  i (g f)
    Atv  x f   -> Atv x (g f)
    A f        -> A (g f)
    E f        -> E (g f)
    D f        -> D (g f)
    B f        -> B (g f)
    Down x f   -> Down x (g f)
    f          -> baseCase f

type AllNominals     = Set.Set NomSymbol
type NegatedNominals = Set.Set NomSymbol

extractNominals :: Formula -> (AllNominals, NegatedNominals)
extractNominals (Lit (PosLit (N n))) = (Set.singleton n, Set.empty)
extractNominals (Lit (NegLit (N n))) = (Set.singleton n, Set.singleton n)
extractNominals (At n f)             = (Set.insert n noms, negNoms)
                                        where (noms, negNoms) = extractNominals f
extractNominals f                    = composeFold (Set.empty,Set.empty) unionTwoSets extractNominals f
                                        where unionTwoSets (s1,s2) (s3,s4) = (Set.union s1 s3, Set.union s2 s4)

extractProps :: Formula -> Set.Set PropSymbol
extractProps (Lit (PosLit (P p))) = Set.singleton p
extractProps (Lit (NegLit (P p))) = Set.singleton p
extractProps f              = composeFold Set.empty Set.union extractProps f

hasUnivModality :: Formula -> Bool
hasUnivModality (A _)     = True
hasUnivModality f         = composeFold False (||) hasUnivModality f

hasDiffModality :: Formula -> Bool
hasDiffModality (B _)     = True
hasDiffModality f         = composeFold False (||) hasDiffModality f

hasDownArrow :: Formula -> Bool
hasDownArrow (Down _ _ ) = True
hasDownArrow f           = composeFold False (||) hasDownArrow f

replaceVar :: StateVar -> NomSymbol -> Formula -> Formula
replaceVar v n a@(Lit (PosLit (V v2))) = if v == v2 then Lit (PosLit (N n)) else a
replaceVar v n a@(Lit (NegLit (V v2))) = if v == v2 then Lit (NegLit (N n)) else a
replaceVar v n a@(Down v2 f) = if v == v2 then a   -- variable capture
                                          else Down v2 (replaceVar v n f)
replaceVar v n (Atv v2 f)   = if v == v2 then At n (replaceVar v n f) else Atv v2 (replaceVar v n f)
replaceVar v n f = composeMap id (replaceVar v n) f

checkIfVariableNegatedOnce :: Formula -> Bool
checkIfVariableNegatedOnce (Down v_ f_)
 = go v_ f_
   where go :: StateVar -> Formula -> Bool
         go v (Down v2 f)           = if v == v2 then False else go v f -- variable capture
         go v (Lit (NegLit (V v2))) = v == v2
         go v f                     = composeFold False (||) (go v) f

checkIfVariableNegatedOnce _ = error "checkIfVariableNegatedOnce : only down-arrow formulas"

