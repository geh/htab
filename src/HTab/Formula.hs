----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------

module HTab.Formula

(PropSymbol(..), NomSymbol(..), RelSymbol(..),
Rel, Prefix,
Formula(..), Literal(..), Atom(..),
DependencySet, Dependency,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow,
PrFormula(..),showLess, AccFormula(..),
LanguageInfo(..), neg,
box, diamond, at, conj, disj, univMod, existMod,
dUnivMod, dExistMod, taut, dimp, imp,
prop, nom, formulaLanguageInfo, prefixList,
checkIfVariableNegatedOnce, replaceVar,
firstPrefixedFormula,
parse, Theory, RelInfo, Task,
encodeValidityTest, encodeSatTest,
HyLoFormula, RelProperties(..)
)

 where

import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.Function ( on )
import Data.List ( lookup )

import HyLo.Signature.String( PropSymbol(..),
                              NomSymbol(..),
                              RelSymbol(..))

import qualified HyLo.InputFile as InputFile
import qualified HyLo.InputFile.Parser as P
import HyLo.InputFile.Parser ( RelProperties(..) )
import qualified HyLo.Formula as F

type Prefix = Int
type Rel = String
data Atom = Taut
          | N NomSymbol
          | P PropSymbol
  deriving(Eq, Ord)

data Literal = PosLit Atom | NegLit Atom
  deriving(Eq, Ord)

instance Show Atom where
 show (Taut) = "T"
 show (N (NomSymbol n))  = n
 show (P (PropSymbol p)) = p

showNom :: NomSymbol -> String
showNom (NomSymbol n) = n

instance Show Literal where
 show (PosLit a) = show a
 show (NegLit a) =  '!' : show a

data Formula
     = Lit Literal
     | Con   [Formula]
     | Dis   [Formula]
     | At     NomSymbol Formula
     | Down   NomSymbol Formula
     | Box    RelSymbol Formula
     | Dia    RelSymbol Formula
     | A      Formula
     | E      Formula
     | D      Formula
     | B      Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (Lit a)    = show a
 show (Con fs)   = "^" ++ show fs
 show (Dis fs)   = "v" ++ show fs
 show (At n f)   = showNom n  ++ ":(" ++ show f ++ ")"
 show (Box r f)  = "[" ++ case r of { RelSymbol rs -> rs ; InvRelSymbol rs -> rs }  ++ "]" ++ show f
 show (Dia r f)  = "<" ++ case r of { RelSymbol rs -> rs ; InvRelSymbol rs -> rs }  ++ ">" ++ show f
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (D f)      = "D" ++ show f
 show (B f)      = "B" ++ show f
 show (Down n f) = "down " ++ showNom n ++ "." ++ show f

-- parsing of the input file

type Theory  = Formula
type Task    = P.InferenceTask
type RelInfo = [P.RelInfo]

parse :: String -> (Theory,RelInfo,[Task])
parse s
  = (theory, relInfo, tasks)
    where parseOutput = InputFile.myparse s
          relInfo     = P.relations parseOutput
          theory      = convert relInfo $ P.theory parseOutput
          tasks       = P.tasks parseOutput

convert :: RelInfo -> [F.Formula NomSymbol PropSymbol RelSymbol] -> Formula
convert relI = conv_ relI . foldr (\f1 f2 -> f1 F.:&: f2) F.Top

conv_ :: RelInfo -> F.Formula NomSymbol PropSymbol RelSymbol -> Formula
conv_  _   F.Top               = taut
conv_  _   F.Bot               = neg taut
conv_  _   (F.Prop p)          = prop p
conv_  _   (F.Nom  n)          = nom n
conv_ relI (F.Neg  f)          = neg $ conv_ relI f
conv_ relI (f1 F.:&:    f2)    = (conv_ relI f1) `conj` (conv_ relI f2)
conv_ relI (f1 F.:|:    f2)    = (conv_ relI f1) `disj` (conv_ relI f2)
conv_ relI (f1 F.:-->:  f2)    = (conv_ relI f1) `imp`  (conv_ relI f2)
conv_ relI (f1 F.:<-->: f2)    = (conv_ relI f1) `dimp` (conv_ relI f2)
conv_ relI (F.Diam r f)        = (specialiseDia r relI) (conv_ relI f)
conv_ relI (F.Box  r f)        = (specialiseBox r relI) (conv_ relI f)
conv_ relI (F.At   n f)        = at        n (conv_ relI f)
conv_ relI (F.Down v f)        = downArrow v (conv_ relI f)
conv_ relI (F.A f)             = univMod     (conv_ relI f)
conv_ relI (F.E f)             = existMod    (conv_ relI f)
conv_ relI (F.D f)             = dExistMod   (conv_ relI f)
conv_ relI (F.B f)             = dUnivMod    (conv_ relI f)

specialiseDia :: RelSymbol -> RelInfo -> (Formula -> Formula)
specialiseDia r relI = case lookup r relI of
                        Nothing          -> diamond r
                        Just properties  -> if P.Difference `elem` properties
                                             then dExistMod
                                             else if P.Universal `elem` properties
                                                   then existMod
                                                   else diamond r

specialiseBox :: RelSymbol -> RelInfo -> (Formula -> Formula)
specialiseBox r relI = case lookup r relI of
                        Nothing          -> box r
                        Just properties  -> if P.Difference `elem` properties
                                             then dUnivMod
                                             else if P.Universal `elem` properties
                                                   then univMod
                                                   else box r
type HyLoFormula = F.Formula NomSymbol PropSymbol RelSymbol

encodeValidityTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeValidityTest relI th fs
 = neg $ conj th (convert relI fs)

encodeSatTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeSatTest relI th fs
 = conj th (convert relI fs)


-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
prop :: PropSymbol -> Formula
nom  :: NomSymbol -> Formula

taut = Lit $ PosLit Taut
prop = Lit . PosLit . P
nom  = Lit . PosLit . N

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
downArrow :: NomSymbol -> Formula -> Formula
downArrow = Down

{- Hybrid operators -}
at :: NomSymbol -> Formula -> Formula
at = At

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
dimp f1 f2 = (f1 `conj` f2) `disj` (neg f1 `conj` neg f2)

imp :: Formula -> Formula -> Formula
imp f1 f2 = neg f1 `disj` f2

skipSingleton :: ([Formula] -> Formula) -> [Formula] -> Formula
skipSingleton _ [x] = x
skipSingleton c xs  = c xs

mergeAndNub :: [Formula] -> [Formula] -> [Formula]
mergeAndNub xs ys = Set.toAscList $ on Set.union Set.fromList xs ys

insertAndNub :: Formula -> [Formula] -> [Formula]
insertAndNub f fs = Set.toAscList $ Set.insert f $ Set.fromList fs

sortAndNub2 :: Formula -> Formula -> [Formula]
sortAndNub2  x y = mergeAndNub [x,y] []

isTrue, isFalse :: Formula -> Bool
isTrue (Lit (PosLit Taut))  = True
isTrue  _                   = False
isFalse (Lit (NegLit Taut)) = True
isFalse  _                  = False

neg :: Formula -> Formula
neg (Con l)          = Dis (map neg l)
neg (Dis l)          = Con (map neg l)
neg (At n f)         = At   n (neg f)
neg (Down v f)       = Down v (neg f)
neg (Box r f)        = Dia  r (neg f)
neg (Dia r f)        = Box  r (neg f)
neg (A f)            = E (neg f)
neg (E f)            = A (neg f)
neg (D f)            = B (neg f)
neg (B f)            = D (neg f)
neg (Lit (PosLit a)) = Lit (NegLit a)
neg (Lit (NegLit a)) = Lit (PosLit a)

-- prefixed formula

data PrFormula = PrFormula Prefix DependencySet Formula
 deriving Eq

instance Show PrFormula where
 show (PrFormula pr bprs f) = show pr ++ ":" ++ (show $ IntSet.toList bprs) ++ ":" ++ show f

showLess :: PrFormula -> String
showLess (PrFormula pr _ f) = show pr ++ ":" ++ show f

prefixList :: Prefix -> DependencySet -> [Formula] -> [PrFormula]
prefixList p bps fl = [PrFormula p bps formula|formula <-fl]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 dsEmpty

-- accessibility Formulas

data AccFormula = AccFormula DependencySet RelSymbol Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula bprs r p1 p2) = show bprs ++ ":" ++ show p1 ++ "<" ++ show r ++ ">" ++ show p2

-- formula language

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
          noms    = Set.toAscList allNoms_
          relNoms = Set.toAscList relNoms_
          props   = Set.toAscList $ extractProps f

-- composeXX functions follow the idea from
-- "A pattern for almost compositional functions", Bringert and Ranta.
composeFold :: b
            -> (b -> b -> b)
            -> (Formula -> b)
            -> (Formula -> b)
composeFold zero combine g e = case e of
    Con fs     -> foldr1 combine $ map g fs
    Dis fs     -> foldr1 combine $ map g fs
    Dia _ f    -> g f
    Box _ f    -> g f
    At  _ f    -> g f
    Down _ f   -> g f
    A f        -> g f
    E f        -> g f
    D f        -> g f
    B f        -> g f
    _          -> zero

composeMap :: (Formula -> Formula)
           -> (Formula -> Formula)
           -> (Formula -> Formula)
composeMap baseCase g e = case e of
    Con fs     -> Con $ map g fs
    Dis fs     -> Dis $ map g fs
    Dia r f    -> Dia r (g f)
    Box r f    -> Box r (g f)
    At   i f   -> At  i (g f)
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

replaceVar :: NomSymbol -> NomSymbol -> Formula -> Formula
replaceVar v n a@(Lit (PosLit (N v2))) = if v == v2 then Lit (PosLit (N n)) else a
replaceVar v n a@(Lit (NegLit (N v2))) = if v == v2 then Lit (NegLit (N n)) else a
replaceVar v n a@(Down v2 f) = if v == v2 then a   -- variable capture
                                          else Down v2 (replaceVar v n f)
replaceVar v n (At v2 f)   = if v == v2 then At n (replaceVar v n f) else At v2 (replaceVar v n f)
replaceVar v n f = composeMap id (replaceVar v n) f

checkIfVariableNegatedOnce :: Formula -> Bool
checkIfVariableNegatedOnce (Down v_ f_)
 = go v_ f_
   where go :: NomSymbol -> Formula -> Bool
         go v (Down v2 f)           = if v == v2 then False else go v f -- variable capture
         go v (Lit (NegLit (N v2))) = v == v2
         go v f                     = composeFold False (||) (go v) f

checkIfVariableNegatedOnce _ = error "checkIfVariableNegatedOnce : only down-arrow formulas"


-- backjumping

type Dependency = Int
type DependencySet = IntSet.IntSet

instance Ord PrFormula where
 compare (PrFormula pr1 deps1 f1) (PrFormula pr2 deps2 f2) =
  case compare (dsMin deps1) (dsMin deps2) of
   LT -> LT
   GT -> GT
   EQ -> compare (pr1,f1) (pr2,f2)

dsUnion :: DependencySet -> DependencySet -> DependencySet
dsUnion  = IntSet.union

dsUnions :: [DependencySet] -> DependencySet
dsUnions = IntSet.unions

dsInsert :: Dependency -> DependencySet -> DependencySet
dsInsert = IntSet.insert

dsMember :: Dependency -> DependencySet -> Bool
dsMember = IntSet.member

dsEmpty :: DependencySet
dsEmpty  = IntSet.empty

dsMin :: DependencySet -> Int
dsMin deps = case IntSet.toAscList deps of { []-> 0 ; (hd:_)-> hd }

dsShow :: DependencySet -> String
dsShow = show . IntSet.toList

