module HTab.Formula

(Atom, Prop, Nom, Literal,
Rel, Prefix, Formula(..),
DependencySet, Dependency, Depth,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow, addDeps,
PrFormula(..),showLess,
LanguageInfo(..), neg,
conj, disj, taut,
prop, nom, formulaLanguageInfo, prefix, negPr,
replaceVar,
firstPrefixedFormula,
parse, simpleParse, Theory, RelInfo, Task,
showRelInfo, showRel, showLit, negLit, isForward, isBackwards,
encodeValidityTest, encodeSatTest, encodeRetrieveTask,
HyLoFormula, RelProperty(..), Encoding(..), maxNom, maxProp,
toPropSymbol, toNomSymbol, toRelSymbol,
isTop, isBottom, isPositiveNom, isPositiveProp, isPositive, isNegative,
isNominal, isProp, atom,
invRel, int
,parseGenerators,Generator,applyGenerators
)

 where

import Data.Bits (complementBit, testBit, clearBit, (.|.) )
import qualified Data.Set as Set
import Data.Set ( Set, unions )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntSet as IntSet
import Data.List ( delete, nub, sort, intercalate, isPrefixOf )

import qualified HyLo.Signature.String as S

import HyLo.Signature( HasSignature(..), relSymbols, nomSymbols, propSymbols )

import qualified HyLo.InputFile as InputFile
import qualified HyLo.InputFile.Parser as P
import qualified HyLo.Formula as F
import HTab.CommandLine ( Params(..) )

type Prefix = Int

type Rel = Int

showRel :: Int -> String
showRel x = sign ++ name
             where sign = if testBit x 0 then "-" else ""
                   name = show $ x `div` 2


isBackwards, isForward :: Int -> Bool
isBackwards x = testBit x 0
isForward = not . isBackwards

data Formula
     = Lit    Atom
     | Con   (Set Formula)
     | Dis   (Set Formula)
     | At     Nom Formula
     | Box    Rel     Formula
     | Dia    Rel     Formula
     | Down   Nom Formula
     | A      Formula
     | E      Formula
  deriving (Eq, Ord)

-- convention : bit0 = OFF -> positive literal, negative otherwise
-- O : top
-- 1 : bottom

-- 2 : p0
-- 3 : !p0
-- 4 : n0
-- 5 : !n0

-- 6 : p1
-- 7 : !p1
-- 8 : n1
-- 9 : !n1
-- ...

type Atom = Int
type Prop = Int
type Nom = Int
type Literal = Int

isTop, isBottom, isPositiveNom, isNominal, isPositiveProp,
 isProp, isNegative, isPositive :: Int -> Bool
isTop            = (==0)
isBottom         = (==1)
isPositiveNom a  = ((a `mod` 4) == 0) && (a > 1)
isNominal a      = ((a `mod` 4) < 2)  && (a > 1)
isPositiveProp a = (a `mod` 4) == 2
isProp a         = (a `mod` 4) >= 2
isNegative a     = testBit a 0
isPositive       = not . isNegative

atom :: Int -> Int
atom x = clearBit x 0

negLit :: Int -> Int
negLit x = complementBit x 0

invRel :: Int -> Int
invRel = negLit

showLit :: Int -> String
showLit n
  | isTop n    = "True"
  | isBottom n = "False"
  | otherwise  = case n `mod` 4 of
                  0 ->  "N" ++ show ((n `div` 4) - 1)
                  1 -> "!N" ++ show ((n `div` 4) - 1)
                  2 ->  "P" ++ show (n `div` 4)
                  3 -> "!P" ++ show (n `div` 4)
                  _ -> error "Impossible"

instance Show Formula where
 show (Lit a)    = showLit a
 show (Con fs)   = "^" ++ show (list fs)
 show (Dis fs)   = "v" ++ show (list fs)
 show (At n f)   = showLit n  ++ ":(" ++ show f ++ ")"
 show (Box r f)    = "[" ++ showRel r ++ "]"   ++ show f
 show (Dia r f)    = "<" ++ showRel r ++ ">"   ++ show f
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (Down n f) = "down " ++ showLit n ++ "." ++ show f

-- parsing of the input file

type Theory  = Formula
type Task    = P.InferenceTask
type PRelInfo = [P.RelInfo]

type RelInfo = Map Rel [RelProperty]
data RelProperty   =   Reflexive
                     | Transitive
                     | Universal
                     --
                     | SubsetOf [Rel]
                     deriving (Eq, Show, Ord)

showRelInfo :: RelInfo -> String
showRelInfo = Map.foldrWithKey (\r v -> (++ " " ++ showRel r ++ " -> " ++ show v )) ""

parse :: Params -> String -> (Theory,RelInfo,Encoding,[Task])
parse p s
  = (theory, relInfo, encoding, tasks)
    where parseOutput = InputFile.myparse s       -- direct parse from hylolib
          encoding    = getEncoding parseOutput
          pRelInfo    = P.relations parseOutput
          relInfo     = forceProperties p encoding $ convertToOurType pRelInfo encoding
          theory      = convert relInfo encoding $ P.theory parseOutput
          tasks       = P.tasks parseOutput


data Encoding = Encoding { nomMap :: Map String Int,
                          propMap :: Map String Int,
                           relMap :: Map String Int }
                  deriving Show

maxNom, maxProp :: Encoding -> Int
maxNom e  = case Map.elems $ nomMap e of
              []  -> 0 -- hackish
              els -> maximum els

maxProp e = case Map.elems $ propMap e of
              []  -> -2 -- hackish
              els -> maximum els

toPropSymbol :: Encoding -> Int -> S.PropSymbol
toPropSymbol e i =
 S.PropSymbol $ case Map.lookup (atom i) (invertMap $ propMap e) of
                  Nothing -> {- new prop symbol -} "new_prop_" ++ show i
                  Just x -> x

toNomSymbol :: Encoding -> Int -> S.NomSymbol
toNomSymbol e i =
 S.NomSymbol $ case Map.lookup (atom i) (invertMap $ nomMap e) of
                 Nothing -> error $ show e ++ " nom symbol " ++ show i
                 Just x -> x

toRelSymbol :: Encoding -> Int -> S.RelSymbol
toRelSymbol e i =
 case Map.lookup (atom i) (invertMap $ relMap e) of
   Nothing -> error $ show e ++ " rel symbol " ++ show i
   Just x -> if isForward i then S.RelSymbol x
              else error "backwards relations not supported"

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap = Map.fromList . map (\(a,b) -> (b,a)) . Map.assocs

getEncoding :: P.ParseOutput -> Encoding
getEncoding parseOutput =
 Encoding {  nomMap = Map.fromList $ zip noms  $ map (\n -> 4 + n*4) [0..],
            propMap = Map.fromList $ zip props $ map (\p -> 2 + p*4) [0..],
             relMap = Map.fromList $ zip rels  $ map (\r ->     r*2) [0..] } 
 where
  theory =  P.theory parseOutput
  noms  =
   map (\(S.NomSymbol n)  -> n) $ list $ unions $ map (nomSymbols . getSignature)  theory
  props =
   map (\(S.PropSymbol p) -> p) $ list $ unions $ map (propSymbols . getSignature) theory
  rels1  = map fst $ P.relations parseOutput
  rels2  =
   map (\(S.RelSymbol r) -> r) $ list $ unions $ map (relSymbols . getSignature) theory
  rels = nub $ rels1 ++ rels2

nomsOfEncoding :: Encoding -> [Nom]
nomsOfEncoding e = Map.elems (nomMap e)

-- add properties specified by the --all-PROP parameters
-- in order to work in case of automatic signature, requires
-- the list of RelSymbol present in the formula

forceProperties :: Params -> Encoding -> RelInfo -> RelInfo
forceProperties p encoding relI
 = foldr addToAll relI rels
   where rels = Map.elems $ relMap encoding
         addToAll r = Map.insertWith (\c1 c2 -> nub $ c1 ++ c2) r conds
         conds = map snd $
                   filter fst   [(allTransitive p, Transitive),
                                 (allReflexive  p, Reflexive )]

convertToOurType :: PRelInfo -> Encoding -> RelInfo
 -- and add for each relation in the formula, the relevant key
convertToOurType prelI e = foldr insertRelProp Map.empty (concatMap convertOne prelI)
 where insertRelProp (rs,pr) = Map.insertWith (++) rs [pr]
       convertOne (r,props)  = concatMap (c r) props
       c r P.Reflexive       = [(int e r,Reflexive    )]
       c _ P.Symmetric       = error "Symmetric not handled"
       c r P.Transitive      = [(int e r,Transitive   )]
       c r P.Universal       = [(int e r,Universal    )]
       c _ (P.InverseOf _)   = error "InverseOf not handled" 
       c r (P.SubsetOf ss)   = [(int e r,SubsetOf [ int e s | s <- ss])]
       c r (P.Equals ss)     = [(int e r,SubsetOf [ int e s | s <- ss])]
                               ++ [(int e s,SubsetOf [int e r]) | s <- ss]
       c _ (P.TClosureOf _)  = error "TClosureOf not handled"
       c _ (P.TRClosureOf _) = error "TRClosureOf not handled"
       c _ P.Functional      = error "Functional not handled"
       c _ P.Injective       = error "Injective not handled"
       c _ P.Difference      = error "Difference not handled"

simpleParse :: Params -> String -> (Theory,RelInfo,Encoding)
simpleParse p s =
 let (t,r,e,_) = parse p $ "signature { automatic } theory { " ++ removeBeginEnd s ++ "}"
 in (t,r,e)
 where removeBeginEnd = unwords . delete "begin" . delete "end" . words

convert :: RelInfo -> Encoding -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol]
             -> Formula
convert relI e = conv_ relI e . foldr (F.:&:) F.Top

conv_ :: RelInfo -> Encoding -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol
           -> Formula
conv_  _   _ F.Top               = taut
conv_  _   _ F.Bot               = neg taut
conv_  _   e (F.Prop p)          = prop e p
conv_  _   e (F.Nom  n)          = nom e n
conv_ relI e (F.Neg  f)          = neg $ conv_ relI e f
conv_ relI e (f1 F.:&:    f2)    = conv_ relI e f1 `conj` conv_ relI e f2
conv_ relI e (f1 F.:|:    f2)    = conv_ relI e f1 `disj` conv_ relI e f2
conv_ relI e (f1 F.:-->:  f2)    = conv_ relI e f1 `imp`  conv_ relI e f2
conv_ relI e (f1 F.:<-->: f2)    = conv_ relI e f1 `dimp` conv_ relI e f2
conv_ relI e (F.Diam r f)        = specialiseDia r relI e (conv_ relI e f)
conv_ relI e (F.Box  r f)        = specialiseBox r relI e (conv_ relI e f)
conv_ relI e (F.At   n f)        = at        e n (conv_ relI e f)
conv_ relI e (F.Down v f)        = downArrow e v (conv_ relI e f)
conv_ relI e (F.A f)             = univMod     (conv_ relI e f)
conv_ relI e (F.E f)             = existMod    (conv_ relI e f)
conv_ _    _ f                   = error (show f ++ "not supported")

type Connector = Formula -> Formula

specialiseDia :: S.RelSymbol -> RelInfo -> Encoding -> Connector
specialiseDia r relI e = specialise r relI (diamond e, existMod) e

specialiseBox :: S.RelSymbol -> RelInfo -> Encoding -> Connector
specialiseBox r relI e = specialise r relI (box e, univMod) e

specialise :: S.RelSymbol -> RelInfo -> (S.RelSymbol -> Connector, Connector)
                -> Encoding -> Connector
specialise (S.RelSymbol r) relI (relational, global) e
 | Universal `elem` props  = global
 | otherwise = relational $ S.RelSymbol r
 where props = Map.findWithDefault [] (int e r) relI

type HyLoFormula = F.Formula S.NomSymbol S.PropSymbol S.RelSymbol

encodeValidityTest :: RelInfo -> Encoding -> Formula -> [HyLoFormula] -> Formula
encodeValidityTest relI e th fs
 = neg $ conj th (convert relI e fs)

encodeSatTest :: RelInfo -> Encoding -> Formula -> [HyLoFormula] -> Formula
encodeSatTest relI e th fs
 = conj th (convert relI e fs)

encodeRetrieveTask :: RelInfo -> Encoding -> LanguageInfo -> Formula -> [HyLoFormula]
                        -> ([Int],[Formula])
encodeRetrieveTask relI e fLang theory fs
 = (noms , map (\n -> conj theory (At n (neg $ convert relI e fs))) noms)
   where noms = languageNoms fLang

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
nom  :: Encoding -> S.NomSymbol -> Formula
prop :: Encoding -> S.PropSymbol -> Formula

taut                    = Lit 0
nom  e (S.NomSymbol n)  = Lit ( nomMap e  Map.! n )
prop e (S.PropSymbol p) = Lit ( propMap e Map.! p )

{- Modalities -}
box, diamond :: Encoding -> S.RelSymbol -> Formula -> Formula
univMod, existMod :: Formula -> Formula
box        e (S.RelSymbol r)    = Box   $ int e r
diamond    e (S.RelSymbol r)    = Dia   $ int e r
univMod    = A
existMod   = E

int :: Encoding -> String -> Int
int e s = relMap e Map.! s

{- binder -}
downArrow :: Encoding -> S.NomSymbol -> Formula -> Formula
downArrow e (S.NomSymbol n) = Down (nomMap e Map.! n)

{- Hybrid operators -}
at :: Encoding -> S.NomSymbol -> Formula -> Formula
at e (S.NomSymbol n) = At (nomMap e Map.! n)

{- Conjunction and disjunction -}

conj, disj :: Formula -> Formula -> Formula

conj    (Con xs) (Con ys) = Con (Set.union xs ys)
conj     f     c@(Con  _) = conj c f
conj c@(Con xs)   f
    | isTrue f            = c
    | isFalse f           = neg taut
    | otherwise           = Con (Set.insert f xs)
conj     f        f'
    | isTrue f            = f'
    | isFalse f           = neg taut
    | isTrue f'           = f
    | isFalse f'          = neg taut
    | otherwise           = skipSingleton Con (set [f,f'])

disj   (Dis xs)   (Dis ys) = Dis (Set.union xs ys)
disj    f       c@(Dis  _) = disj c f
disj c@(Dis xs)    f
    | isTrue f             = taut
    | isFalse f            = c
    | otherwise            = Dis (Set.insert f xs)
disj    f          f'
    | isTrue f             = taut
    | isFalse f            = f'
    | isTrue f'            = taut
    | isFalse f'           = f
    | otherwise            = skipSingleton Dis (set [f,f'])

dimp :: Formula -> Formula -> Formula
dimp f1 f2 = (neg f1 `disj` f2) `conj` (f1 `disj` neg f2)
-- this form is preferred so as to enhance lazy branching

-- TODO
-- ala Spartacus:
-- when there is no literal in the double implication,
-- use the following form:
--dimp f1 f2 = (f1 `conj` f2) `disj` (neg f1 `conj` neg f2)

imp :: Formula -> Formula -> Formula
imp f1 f2 = neg f1 `disj` f2

skipSingleton :: (Set Formula -> Formula) -> Set Formula -> Formula
skipSingleton c xs
 | Set.size xs == 1 = Set.findMin xs
 | otherwise       = c xs

isTrue, isFalse :: Formula -> Bool
isTrue  (Lit 0) = True
isTrue   _      = False
isFalse (Lit 1) = True
isFalse  _      = False

-- invariant : neg is only called on literals during
-- the run of the algorithm
neg :: Formula -> Formula
neg (Con l)          = Dis (Set.map neg l)
neg (Dis l)          = Con (Set.map neg l)
neg (At n f)         = At   n (neg f)
neg (Down v f)       = Down v (neg f)
neg (Box r f)        = Dia  r (neg f)
neg (Dia r f)        = Box  r (neg f)
neg (A f)            = E (neg f)
neg (E f)            = A (neg f)
neg (Lit n)          = Lit $ negLit n


-- prefixed formula

type Depth = Int -- modal depth of current formula wrt input formula

data PrFormula = PrFormula Prefix DependencySet Depth Formula
 deriving Eq

instance Show PrFormula where
 show (PrFormula pr ds md f) = intercalate ":" [show pr, show ds, show md, show f]

showLess :: PrFormula -> String
showLess (PrFormula pr _ _ f) = show pr ++ ":" ++ show f

prefix :: Prefix -> DependencySet -> Depth -> Set Formula -> [PrFormula]
prefix p bps md fs = [PrFormula p bps md formula|formula <- list fs]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 dsEmpty 0

negPr :: PrFormula -> PrFormula
negPr (PrFormula p ds md f) = PrFormula p ds md (neg f)

-- formula language

data LanguageInfo = LanguageInfo { languageNoms :: [Int] } -- ascending

instance Show LanguageInfo where
 show li =         "Input Language:"
           ++ "\n|" ++ yesnol "Noms" ( languageNoms li )
  where yesnol s l | null l = "no " ++ s
        yesnol s l = s ++ concatMap (\l_ -> ", " ++ showLit l_)  l

formulaLanguageInfo :: Encoding -> LanguageInfo
formulaLanguageInfo e
 = LanguageInfo { languageNoms = noms }
    where noms = sort $ nomsOfEncoding e

-- composeXX functions follow the idea from
-- "A pattern for almost compositional functions", Bringert and Ranta.
composeMap :: (Formula -> Formula)
           -> (Formula -> Formula)
           -> (Formula -> Formula)
composeMap baseCase g e = case e of
    Con fs     -> Con $ Set.map g fs
    Dis fs     -> Dis $ Set.map g fs
    Dia r f  -> Dia r (g f)
    Box r f    -> Box r (g f)
    At   i f   -> At  i (g f)
    A f        -> A (g f)
    E f        -> E (g f)
    Down x f   -> Down x (g f)
    f          -> baseCase f

replaceVar :: Int -> Int -> Formula -> Formula
replaceVar v n a@(Lit v2)
   | isNominal v2 = if atom v /= atom v2 then a
                                         else Lit $ atom n .|. sign v2
                      where sign x = if isNegative x then 1 else 0

replaceVar v n a@(Down v2 f) = if v == v2 then a   -- variable capture
                                          else Down v2 (replaceVar v n f)
replaceVar v n (At v2 f)     = if v == v2 then At n (replaceVar v n f)
                                          else At v2 (replaceVar v n f)
replaceVar v n f = composeMap id (replaceVar v n) f

-- backjumping

type Dependency = Int
type DependencySet = IntSet.IntSet

instance Ord PrFormula where
 compare (PrFormula pr1 ds1 _ f1) (PrFormula pr2 ds2 _ f2) =
  case dsMin ds1 `compare` dsMin ds2 of
   LT -> LT
   GT -> GT
   EQ -> compare (pr1,f1) (pr2,f2)

dsUnion :: DependencySet -> DependencySet -> DependencySet
dsUnion = IntSet.union

dsUnions :: [DependencySet] -> DependencySet
dsUnions = IntSet.unions

dsInsert :: Dependency -> DependencySet -> DependencySet
dsInsert = IntSet.insert

dsMember :: Dependency -> DependencySet -> Bool
dsMember = IntSet.member

dsEmpty :: DependencySet
dsEmpty = IntSet.empty

dsMin :: DependencySet -> Int
dsMin ds = maybe 0 fst $ IntSet.minView ds

dsShow :: DependencySet -> String
dsShow = show . IntSet.toList

addDeps :: DependencySet -> PrFormula -> PrFormula
addDeps ds1 (PrFormula p ds2 md f) = PrFormula p (dsUnion ds1 ds2) md f

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList


-- symmetries
-- substitution of literals inside of formulas

type Generator = [(Depth,Atom,Atom)]

applyGenerators :: [Generator] -> PrFormula -> [PrFormula]
applyGenerators gens f = delete f $ nub $ map (\gen -> subst gen f) gens

subst :: Generator -> PrFormula -> PrFormula
subst gen (PrFormula pr ds md f) = PrFormula pr ds md $ substNorm (normGen gen md) f

normGen :: Generator -> Depth -> Generator
normGen g md = [(md1-md,a1,a2) | (md1,a1,a2) <- g, md1 - md >= 0]

substNorm :: Generator -> Formula -> Formula
-- act as if we were at modal depth 0 and generator has been adjusted
substNorm gen (Lit a)     = Lit $ genOnAtom gen a
substNorm gen (At n f)    = At n $ substNorm (normGen gen 1) f
substNorm gen (Box r f)   = Box r $ substNorm (normGen gen 1) f
substNorm gen (Dia r f)   = Dia r $ substNorm (normGen gen 1) f
substNorm gen (Down n f)  = Down n $ substNorm (normGen gen 1) f
substNorm gen (A f)       = A $ substNorm (normGen gen 1) f
substNorm gen (E f)       = E $ substNorm (normGen gen 1) f
substNorm gen f           = composeMap id (substNorm gen) f

genOnAtom :: Generator -> Atom -> Atom
genOnAtom [] a = a
genOnAtom ((d,x,y):g) a
 | d == 0 && x == a        = y
 | d == 0 && x == negLit a = negLit y
 | otherwise               = genOnAtom g a

parseGenerators :: Encoding -> String -> [Generator]
parseGenerators e genString
 =  [lineToGen e l [] | l <- lines genString,
                        not ("%" `isPrefixOf` l),
                        not (null l)            ]

-- turn such a line into a generator:
-- 4 -2 5, 5 3 5, 0 -6 -3
lineToGen :: Encoding -> String -> Generator -> Generator
lineToGen _ "" g      = g
lineToGen e (',':l) g = lineToGen e l g
lineToGen e l g       = let triple = takeWhile (/= ',') l
                            remainder = dropWhile (/= ',') l
                            [md,l1,l2] = map read $ words triple
                            -- we read X for PX or -Y for -PY,
                            -- now we need to convert it in atom
                            a1 = if l1 < 0
                                  then negLit $ (Map.!) (propMap e) ("P" ++ show (negate l1))
                                  else (Map.!) (propMap e) ("P" ++ show l1)
                            a2 = if l2 < 0
                                  then negLit $ (Map.!) (propMap e) ("P" ++ show (negate l2))
                                  else (Map.!) (propMap e) ("P" ++ show l2)
                        in lineToGen e remainder (g ++ [(md,a1,a2)])
