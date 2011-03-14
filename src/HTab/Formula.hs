----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------


module HTab.Formula

(Atom, Prop, Nom, Literal,
Rel, Prefix, Formula(..),
DependencySet, Dependency,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow, addDeps,
PrFormula(..),showLess, AccFormula(..),
LanguageInfo(..), neg,
conj, disj, taut,
prop, nom, formulaLanguageInfo, prefix,
checkIfVariableNegatedOnce, replaceVar,
firstPrefixedFormula,
parse, simpleParse, Theory, RelInfo, Task,
showRelInfo, showRel, showLit, negLit, isForward, isBackwards,
encodeValidityTest, encodeSatTest, encodeRetrieveTask,
HyLoFormula, RelProperty(..), Encoding(..), maxNom, maxProp, toPropSymbol, toNomSymbol, toRelSymbol,
isTop, isBottom, isPositiveNom, isPositiveProp, isPositive, isNegative, isNominal, isProp, atom,
inv, invRel, int
)

 where

import Data.Bits (complementBit, testBit, clearBit, (.|.) )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntSet as IntSet
import Data.List ( delete, nub, sort )

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
     | BoxX   Rel Formula
     | DiaX   (Maybe Int) Rel Formula
     | A      Formula
     | E      Formula
     | D      Formula
     | B      Formula
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

isTop, isBottom, isPositiveNom, isNegativeNom, isNominal, isPositiveProp, isProp, isNegative, isPositive :: Int -> Bool
isTop            = (==0)
isBottom         = (==1)
isPositiveNom a  = ((a `mod` 4) == 0) && (a > 1)
isNegativeNom a  = ((a `mod` 4) == 1) && (a > 1)
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
 show (BoxX r f)   = "[" ++ showRel r ++ "*]"  ++ show f
 show (DiaX i r f) = "<" ++ showRel r ++ "*>(" ++ show i ++ ")" ++ show f
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (D f)      = "D" ++ show f
 show (B f)      = "B" ++ show f
 show (Down n f) = "down " ++ showLit n ++ "." ++ show f

-- parsing of the input file

type Theory  = Formula
type Task    = P.InferenceTask
type PRelInfo = [P.RelInfo]

type RelInfo = Map Rel [RelProperty]
data RelProperty   =   Reflexive
                     | Symmetric
                     | Transitive
                     | Functional
                     | Injective
                     | Universal
                     | Difference
                     --
                     | InverseOf Rel
                     | TRClosureOf Rel
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
          relInfo     = handleFunInj $ saturate $ forceProperties p encoding $ convertToOurType pRelInfo encoding -- TODO
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
toPropSymbol e i = S.PropSymbol $ case Map.lookup (atom i) (invertMap $ propMap e) of
                                    Nothing -> {- new prop symbol -} "new_prop_" ++ show i
                                    Just x -> x

toNomSymbol :: Encoding -> Int -> S.NomSymbol
toNomSymbol e i = S.NomSymbol $  case Map.lookup (atom i) (invertMap $ nomMap e) of
                                        Nothing -> error $ show e ++ " nom symbol " ++ show i
                                        Just x -> x

toRelSymbol :: Encoding -> Int -> S.RelSymbol
toRelSymbol e i = case Map.lookup (atom i) (invertMap $ relMap e) of
                         Nothing -> error $ show e ++ " rel symbol " ++ show i
                         Just x -> if isForward i then S.RelSymbol x else S.InvRelSymbol x

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap = Map.fromList . map (\(a,b) -> (b,a)) . Map.assocs

getEncoding :: P.ParseOutput -> Encoding
getEncoding parseOutput =
 Encoding {  nomMap = Map.fromList $ zip noms  $ map (\n -> 4 + n*4) [0..],
            propMap = Map.fromList $ zip props $ map (\p -> 2 + p*4) [0..],
             relMap = Map.fromList $ zip rels  $ map (\r ->     r*2) [0..] } 
 where
   theory =  P.theory parseOutput
   noms  = map (\(S.NomSymbol n)  -> n) $ Set.toList $ Set.unions $ map (nomSymbols . getSignature)  theory
   props = map (\(S.PropSymbol p) -> p) $ Set.toList $ Set.unions $ map (propSymbols . getSignature) theory
   rels1  = map fst $ P.relations parseOutput
   rels2  = map (\(S.RelSymbol r) -> r) $ Set.toList $ Set.unions $ map (relSymbols . getSignature) theory
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
                   filter fst $ [(allTransitive p, Transitive),
                                 (allReflexive  p, Reflexive ),
                                 (allSymmetric  p, Symmetric ),
                                 (allFunctional p, Functional),
                                 (allInjective  p, Injective )]

convertToOurType :: PRelInfo -> Encoding -> RelInfo -- and add for each relation in the formula, the relevant key
convertToOurType prelI e = foldr insertRelProp Map.empty (concatMap convertOne prelI)
 where insertRelProp (rs,pr) = Map.insertWith (++) rs [pr]
       convertOne (r,props)  = concatMap (c r) props
       c r P.Reflexive       = [(int e r,Reflexive    )]
       c r P.Symmetric       = [(int e r,Symmetric    )]
       c r P.Transitive      = [(int e r,Transitive   )]
       c r P.Functional      = [(int e r,Functional   )]
       c r P.Universal       = [(int e r,Universal    )]
       c r P.Difference      = [(int e r,Difference   )]
       c r (P.InverseOf s)   = [(int e r,InverseOf   (int e s))]
       c r (P.TRClosureOf s) = [(int e r,TRClosureOf (int e s))]
       c r (P.SubsetOf ss)   = [(int e r,SubsetOf [ int e s | s <- ss])]
       c r (P.Equals ss)     = [(int e r,SubsetOf [ int e s | s <- ss])] ++ [(int e s,SubsetOf [int e r]) | s <- ss]
       c _ (P.TClosureOf _)  = error "TClosureOf not handled"

simpleParse :: Params -> String -> (Theory,RelInfo,Encoding,[Task])
simpleParse p s = parse p $ "signature { automatic } theory { " ++ removeBeginEnd s ++ "}"
 where removeBeginEnd = unwords . delete "begin" . delete "end" . words

convert :: RelInfo -> Encoding -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol] -> Formula
convert relI e = conv_ relI e . foldr (F.:&:) F.Top

conv_ :: RelInfo -> Encoding -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol -> Formula
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
conv_ relI e (F.D f)             = dExistMod   (conv_ relI e f)
conv_ relI e (F.B f)             = dUnivMod    (conv_ relI e f)

type Connector = Formula -> Formula

specialiseDia :: S.RelSymbol -> RelInfo -> Encoding -> Connector
specialiseDia r relI e = specialise r relI (diamond e, diamondX e, dExistMod, existMod) e

specialiseBox :: S.RelSymbol -> RelInfo -> Encoding -> Connector
specialiseBox r relI e = specialise r relI (box e, boxX e, dUnivMod, univMod) e

specialise :: S.RelSymbol -> RelInfo -> (S.RelSymbol -> Connector, S.RelSymbol -> Connector, Connector, Connector) -> Encoding -> Connector
specialise (S.InvRelSymbol r) _ (relational, _ , _ , _) _ -- happens only with simple input
 = relational $ S.InvRelSymbol r

specialise (S.RelSymbol r) relI (relational, rtclosure, difference, global) e
 = case filter interesting props of
    (Difference:_) -> difference
    (Universal:_)  -> global
    []             -> relational $ S.RelSymbol r
    _              -> case specialise2 (int e r) relI of
                         Just_ r2        -> relational $ toRelSymbol e r2
                         Inverse r2      -> relational $ invRS $ toRelSymbol e r2
                         RTClosure r2    -> rtclosure  $ toRelSymbol e r2
                         RTClosureInv r2 -> rtclosure  $ invRS $ toRelSymbol e r2
    where
      interesting Difference      = True
      interesting Universal       = True
      interesting (InverseOf _)   = True
      interesting (TRClosureOf _) = True
      interesting _               = False
      props                       = Map.findWithDefault [] (int e r) relI
      invRS (S.RelSymbol s)       = S.InvRelSymbol s
      invRS (S.InvRelSymbol s)    = S.RelSymbol s

data ModType = Just_ Rel | Inverse Rel | RTClosure Rel | RTClosureInv Rel

specialise2 :: Rel -> RelInfo -> ModType
specialise2 r_ relI
 = go (Just_ r_)
    where
     go j@(Just_ r) =
       case filter interesting (propsOf r) of
        (InverseOf r2:_)   -> go (Inverse r2)
        (TRClosureOf r2:_) -> go (RTClosure r2)
        _                  -> j

     go io@(Inverse r) =
       case filter interesting (propsOf r) of
        (InverseOf r2:_)   -> go (Just_ r2)
        (TRClosureOf r2:_) -> RTClosureInv r2
        _                  -> io

     go rtc@(RTClosure r) =
       case filter interesting (propsOf r) of
        (InverseOf r2:_)   -> RTClosureInv r2
        (TRClosureOf r2:_) -> go (RTClosure r2)
        _                  -> rtc

     go rtci@(RTClosureInv r) =
       case filter interesting (propsOf r) of
        (InverseOf r2:_)   -> RTClosure r2
        _                  -> rtci

     interesting (InverseOf _)   = True
     interesting (TRClosureOf _) = True
     interesting _               = False
     propsOf r__                 = Map.findWithDefault [] r__ relI


inv :: Rel -> RelInfo -> Rel
inv r relI
 = case Map.lookup r relI of
    Nothing         -> r
    Just properties -> if Symmetric `elem` properties then r else invRel r

type HyLoFormula = F.Formula S.NomSymbol S.PropSymbol S.RelSymbol

-- saturate RelInfo with hierarchy information : Reflexive, Symmetric, Transitive, Universal, Difference

saturate :: RelInfo -> RelInfo
saturate relI = Map.mapWithKey saturateOne relI
   where saturateOne r props = let ancestorProps = concatMap (getProperties relI) $ getAncestors r relI
                                   newProps = list $ Set.union (set ancestorProps) (set props)
                               in
                                 newProps

getProperties :: RelInfo -> Rel -> [RelProperty]
getProperties ri r
 = getOnlyProps $ filter isProp_ props
    where props             = Map.findWithDefault [] r ri
          getOnlyProps      = filter isProp_
          isProp_ Reflexive  = True
          isProp_ Symmetric  = True
          isProp_ Transitive = True
          isProp_ Universal  = True
          isProp_ Difference = True
          isProp_ _          = False

getAncestors :: Rel -> RelInfo -> [Rel]
getAncestors r_ relI =
 list $ go (Set.singleton r_) r_
 where
  go seen r =
   let props = Map.findWithDefault [] r relI
       parents = concatMap extractParent props
       extractParent (InverseOf rp)   = [rp]
       extractParent (TRClosureOf rp) = [rp]
       extractParent _                = [  ]
       todo = list ( (set parents) Set.\\ seen )
       newSeen = Set.union seen $ set parents
   in
     case todo of
      [] -> Set.singleton r
      _  -> Set.insert r $ Set.unions $ map (go newSeen) todo

-- ==========================================================================
--
-- saturate relInfo with the properties Functional and Injective
-- rationale : being able to enforce Injectivity even though the
--             input format does not have an Injective label.
--             the solution to do so is:
--             R_injective , Inv_R { inverseof R_injective, Functional }
--
-- ==========================================================================

data FunInj = Not | Fun | Inj | FunInj

handleFunInj :: RelInfo -> RelInfo
handleFunInj relI =
-- explore the hierarchy of relations starting by the leaves and ending at the top
-- taking into account the alternations "inverseof" to enforce functionality and/or injectivity
  Map.foldrWithKey startFromLeaf relI relI
 where startFromLeaf rs props currentRelI = follow rs props currentRelI Not

       follow rs props currentRelI currentStatus
         = case parentsWithInv props status of
            Just (parent,newStatus) -> let parentProps = Map.findWithDefault [] parent currentRelI in
                                       follow parent parentProps currentRelI newStatus
            Nothing
              -> case currentStatus of
                   Not -> currentRelI
                   _   -> Map.insertWith (++) rs (toProps status) currentRelI
           where
                 status = if Functional `elem` props
                           then case currentStatus of
                                 FunInj -> FunInj
                                 Inj    -> FunInj
                                 Fun    -> Fun
                                 Not    -> Fun
                           else currentStatus
                 toProps Not = []
                 toProps FunInj = [Functional, Injective]
                 toProps Fun = [Functional]
                 toProps Inj = [Injective]

       parentsWithInv props status
                   = case concatZip $ map extractParent props of
                         ([],[])      -> Nothing
                         ((par:_),_)  -> Just (par, invert status)
                                         where invert Not    = Not
                                               invert FunInj = FunInj
                                               invert Fun    = Inj
                                               invert Inj    = Fun
                         (_,(par:_))  -> Just (par, status)
                     where extractParent (InverseOf rp)   = ([rp],[])
                           extractParent (TRClosureOf rp) = ([]  ,[rp])
                           extractParent _                = ([]  ,[])


concatZip :: [([a],[b])] -> ([a],[b])
concatZip [] = ([],[])
concatZip ((as,bs):tl) = (as++as2,bs++bs2) where (as2,bs2) = concatZip tl

-- ==========================================================================

encodeValidityTest :: RelInfo -> Encoding -> Formula -> [HyLoFormula] -> Formula
encodeValidityTest relI e th fs
 = neg $ conj th (convert relI e fs)

encodeSatTest :: RelInfo -> Encoding -> Formula -> [HyLoFormula] -> Formula
encodeSatTest relI e th fs
 = conj th (convert relI e fs)

encodeRetrieveTask :: RelInfo -> Encoding -> LanguageInfo -> Formula -> [HyLoFormula] -> ([Int],[Formula])
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
box, diamond, boxX, diamondX :: Encoding -> S.RelSymbol -> Formula -> Formula
univMod, existMod, dUnivMod, dExistMod :: Formula -> Formula
box        e (S.RelSymbol r)    = Box   $ int e r
box        e (S.InvRelSymbol r) = Box   $ invRel $ int e r
diamond    e (S.RelSymbol r)    = Dia   $ int e r
diamond    e (S.InvRelSymbol r) = Dia   $ invRel $ int e r
boxX       e (S.RelSymbol r)    = BoxX  $ int e r
boxX       e (S.InvRelSymbol r) = BoxX  $ invRel $ int e r
diamondX   e (S.RelSymbol r)    = DiaX Nothing $ int e r
diamondX   e (S.InvRelSymbol r) = DiaX Nothing $ invRel $ int e r
univMod    = A
existMod   = E
dUnivMod   = B
dExistMod  = D

int :: Encoding -> String -> Int
int e s = (relMap e) Map.! s

{- binder -}
downArrow :: Encoding -> S.NomSymbol -> Formula -> Formula
downArrow e (S.NomSymbol n) = Down ((nomMap e) Map.! n)

{- Hybrid operators -}
at :: Encoding -> S.NomSymbol -> Formula -> Formula
at e (S.NomSymbol n) = At ((nomMap e) Map.! n)

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
neg (BoxX r f)       = DiaX Nothing r (neg f)
neg (DiaX _ r f)     = BoxX r (neg f)
neg (A f)            = E (neg f)
neg (E f)            = A (neg f)
neg (D f)            = B (neg f)
neg (B f)            = D (neg f)
neg (Lit n)          = Lit $ negLit n


-- prefixed formula

data PrFormula = PrFormula Prefix DependencySet Formula
 deriving Eq

instance Show PrFormula where
 show (PrFormula pr ds f) = show pr ++ ":" ++ (dsShow ds) ++ ":" ++ show f

showLess :: PrFormula -> String
showLess (PrFormula pr _ f) = show pr ++ ":" ++ show f

prefix :: Prefix -> DependencySet -> Set Formula -> [PrFormula]
prefix p bps fs = [PrFormula p bps formula|formula <- Set.toList fs]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 dsEmpty

-- accessibility Formulas

data AccFormula = AccFormula DependencySet Rel Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula bprs r p1 p2) = show bprs ++ ":" ++ show p1 ++ "<" ++ showRel r ++ ">" ++ show p2

-- formula language

data LanguageInfo = LanguageInfo {   languageNoms :: [Int], -- ascending list
                                     relevantNoms :: [Int],
                                     languagePast :: Bool,
                                    languageTrans :: Bool }

instance Show LanguageInfo where
 show li =         "Input Language:"
           ++ "\n|" ++ yesnol "Noms" ( languageNoms li )
           ++ "\n|" ++ yesnol "Relevant Noms" ( relevantNoms li ) ++ "\n"
           ++ yesno "Past, " ( languagePast li )
           ++ yesno "Trans, " ( languageTrans li)
  where yesno :: String -> Bool -> String
        yesno s b = ( if b then "" else "no " ) ++ s
        yesnol s l | null l = "no " ++ s
        yesnol s l = s ++ concatMap (\l_ -> ", " ++ showLit l_)  l

formulaLanguageInfo :: Formula -> Encoding -> LanguageInfo
formulaLanguageInfo f e
 = LanguageInfo {   languageNoms = noms,
                    relevantNoms = relNoms,
                    languagePast = hasPast f,
                   languageTrans = hasTransClosure f}

    where allNoms_ = nomsOfEncoding e
          relNoms_ = extractRelevantNominals f
          noms     = sort allNoms_
          relNoms  = Set.toAscList relNoms_

-- composeXX functions follow the idea from
-- "A pattern for almost compositional functions", Bringert and Ranta.
composeFold :: b
            -> (b -> b -> b)
            -> (Formula -> b)
            -> (Formula -> b)
composeFold zero combine g e = case e of
    Con fs     -> foldr1 combine $ map g $ list fs
    Dis fs     -> foldr1 combine $ map g $ list fs
    Dia _ f    -> g f
    Box _ f    -> g f
    DiaX _ _ f -> g f
    BoxX _ f   -> g f
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
    Con fs     -> Con $ Set.map g fs
    Dis fs     -> Dis $ Set.map g fs
    Dia r f  -> Dia r (g f)
    Box r f    -> Box r (g f)
    DiaX i r f -> DiaX i r (g f)
    BoxX r f   -> BoxX r (g f)
    At   i f   -> At  i (g f)
    A f        -> A (g f)
    E f        -> E (g f)
    D f        -> D (g f)
    B f        -> B (g f)
    Down x f   -> Down x (g f)
    f          -> baseCase f


extractRelevantNominals :: Formula -> Set Nom
extractRelevantNominals (Lit n)| isNegativeNom n = Set.singleton (atom n)
extractRelevantNominals (At _ f)                 = extractRelevantNominals f
extractRelevantNominals f                        = composeFold Set.empty Set.union extractRelevantNominals f

hasPast :: Formula -> Bool
hasPast (Dia r _)    = testBit r 0
hasPast (Box r _)    = testBit r 0
hasPast (BoxX r _) = testBit r 0
hasPast (DiaX _ r _) = testBit r 0
hasPast f            = composeFold False (||) hasPast f

hasTransClosure :: Formula -> Bool
hasTransClosure (BoxX _ _)   = True
hasTransClosure (DiaX _ _ _) = True
hasTransClosure f            = composeFold False (||) hasTransClosure f

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

checkIfVariableNegatedOnce :: Formula -> Bool
checkIfVariableNegatedOnce (Down v_ f_)
 = go v_ f_
   where go :: Int -> Formula -> Bool
         go v (Down v2 f)           = if v == v2 then False {- variable capture -} else go v f
         go v (Lit v2)              = (atom v == atom v2) && isNegative v2
         go v f                     = composeFold False (||) (go v) f

checkIfVariableNegatedOnce _ = error "checkIfVariableNegatedOnce : only down-arrow formulas"


-- backjumping

type Dependency = Int
type DependencySet = IntSet.IntSet

instance Ord PrFormula where
 compare (PrFormula pr1 ds1 f1) (PrFormula pr2 ds2 f2) =
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
addDeps ds1 (PrFormula p ds2 f) = PrFormula p (dsUnion ds1 ds2) f

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList
