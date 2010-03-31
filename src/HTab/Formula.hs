----------------------------------------------------
--                                                --
-- Formula.hs:                                    --
-- Formula data type, normal                      --
-- form and show functions.                       --
--                                                --
----------------------------------------------------


module HTab.Formula

(RelSymbol(..), Atom, Prop, Nom, Literal,
Rel, Prefix, Formula(..),
DependencySet, Dependency,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow,
PrFormula(..),showLess, AccFormula(..),
LanguageInfo(..), neg,
box, diamond, at, conj, disj, univMod, existMod,
downArrow, dUnivMod, dExistMod, taut, dimp, imp,
prop, nom, formulaLanguageInfo, prefix,
checkIfVariableNegatedOnce, replaceVar,
firstPrefixedFormula,
parse, simpleParse, Theory, RelInfo, Task,
showRelInfo, showLit,
encodeValidityTest, encodeSatTest, encodeRetrieveTask,
HyLoFormula, RelProperty(..), Encoding(..), maxNom, maxProp, toPropSymbol, toNomSymbol,
isTop, isBottom, isPositiveNom, isPositive, isNegative, isNominal, isProp, atom,
inv
)

 where

import Data.Bits (complementBit, testBit, clearBit, (.|.) )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntSet as IntSet
import Data.List ( delete, nub )

import qualified HyLo.Signature.String as S

import HyLo.Signature( HasSignature(..), relSymbols, nomSymbols, propSymbols )

import qualified HyLo.InputFile as InputFile
import qualified HyLo.InputFile.Parser as P
import HTab.Base (set, list, invertMap)
import qualified HyLo.Formula as F
import HTab.CommandLine ( CmdLineParams(..) )

type Prefix = Int

type Rel = String
data RelSymbol = RelSymbol String | InvRelSymbol String deriving (Eq, Ord)

instance Show RelSymbol where
 show (RelSymbol r)    = r
 show (InvRelSymbol r) = '-':r

data Formula
     = Lit    Atom
     | Con   (Set Formula)
     | Dis   (Set Formula)
     | At     Nom Formula
     | Box    RelSymbol     Formula
     | Dia    RelSymbol     Formula
     | Down   Nom Formula
     | BoxX   RelSymbol Formula
     | DiaX   (Maybe Int) RelSymbol Formula
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

isTop, isBottom, isPositiveNom, isNominal, isProp, isNegative, isPositive :: Int -> Bool
isTop           = (==0)
isBottom        = (==1)
isPositiveNom a = ((a `mod` 4) == 0) && (a > 1)
isNominal a     = ((a `mod` 4) < 2)  && (a > 1)
isProp a        = ((a `mod` 4) >= 2)
isNegative a    = testBit a 0
isPositive      = not . isNegative

atom :: Int -> Int
atom x = clearBit x 0

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
 show (Box r f)  = "[" ++ show r ++ "]" ++ show f
 show (Dia r f)  = "<" ++ show r ++ ">" ++ show f
 show (BoxX r f) = "[" ++ show r ++ "*]" ++ show f
 show (DiaX i r f) = "<" ++ show r ++ "*>(" ++ show i ++ ")" ++ show f
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
showRelInfo = Map.foldWithKey (\rel v -> (++ " " ++ rel ++ " -> " ++ show v )) ""

parse :: CmdLineParams -> String -> (Theory,RelInfo,Encoding,[Task])
parse clp s
  = (theory, relInfo, e, tasks)
    where parseOutput = InputFile.myparse s
          pRelInfo    = P.relations parseOutput
          rels        = Set.toList $ Set.unions $ map (relSymbols . getSignature) $ P.theory parseOutput
          relInfo     = handleFunInj $ saturate $ forceProperties clp rels $ convertToOurType pRelInfo
          e           = getEncoding $ P.theory parseOutput
          theory      = convert relInfo e $ P.theory parseOutput
          tasks       = P.tasks parseOutput


data Encoding = Encoding { nomMap :: Map String Int,
                          propMap :: Map String Int }
                  deriving Show

maxNom, maxProp :: Encoding -> Int
maxNom e  = case Map.elems $ nomMap e of
              []  -> 0 -- hackish
              els -> maximum els

maxProp e = case Map.elems $ propMap e of
              []  -> -2 -- hackish
              els -> maximum els

toPropSymbol :: Encoding -> Int -> S.PropSymbol
--toPropSymbol e i = S.PropSymbol $ (invertMap $ propMap e) Map.! (atom i)
toPropSymbol e i = S.PropSymbol $ case Map.lookup (atom i) (invertMap $ propMap e) of
                                    Nothing -> {- new prop symbol -} "new_prop_" ++ show i
                                    Just x -> x

toNomSymbol :: Encoding -> Int -> S.NomSymbol
--toNomSymbol e i = S.NomSymbol $ (invertMap $ nomMap e) Map.! (atom i)
toNomSymbol e i = S.NomSymbol $  case Map.lookup (atom i) (invertMap $ nomMap e) of
                                        Nothing -> error $ show e ++ " nom symbol " ++ show i
                                        Just x -> x


getEncoding :: [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol] -> Encoding
getEncoding theory =
 Encoding {  nomMap = Map.fromList $ zip noms  $ map (\n -> 4 + n*4) [0..],
            propMap = Map.fromList $ zip props $ map (\n -> 2 + n*4) [0..]  } 
 where
   noms  = map (\(S.NomSymbol n)  -> n) $ Set.toList $ Set.unions $ map (nomSymbols . getSignature)  theory
   props = map (\(S.PropSymbol p) -> p) $ Set.toList $ Set.unions $ map (propSymbols . getSignature) theory

-- add properties specified by the --all-PROP parameters
-- in order to work in case of automatic signature, requires
-- the list of RelSymbol present in the formula

forceProperties :: CmdLineParams -> [S.RelSymbol] -> RelInfo -> RelInfo
forceProperties clp relsymbols relI
 = foldr addToAll relI rels
   where rels = [ rel | S.RelSymbol rel <- relsymbols]
         addToAll r = Map.insertWith (\c1 c2 -> nub $ c1 ++ c2) r conds
         conds = map snd $
                   filter fst $ [(allTransitive clp, Transitive),
                                 (allReflexive  clp, Reflexive ),
                                 (allSymmetric  clp, Symmetric ),
                                 (allFunctional clp, Functional),
                                 (allInjective  clp, Injective )]

convertToOurType :: PRelInfo -> RelInfo -- and add for each relation in the formula, the relevant key
convertToOurType prelI = foldr insertRelProp (Map.empty) (concatMap convertOne prelI)
 where insertRelProp (rs,pr) = Map.insertWith (++) rs [pr]
       convertOne (r,props)  = concatMap (c r) props
       c r P.Reflexive       = [(r,Reflexive    )]
       c r P.Symmetric       = [(r,Symmetric    )]
       c r P.Transitive      = [(r,Transitive   )]
       c r P.Functional      = [(r,Functional   )]
       c r P.Universal       = [(r,Universal    )]
       c r P.Difference      = [(r,Difference   )]
       c r (P.InverseOf s)   = [(r,InverseOf s  )]
       c r (P.TRClosureOf s) = [(r,TRClosureOf s)]
       c r (P.SubsetOf ss)   = [(r,SubsetOf [ s | s <- ss])]
       c r (P.Equals ss)     = [(r,SubsetOf [ s | s <- ss])] ++ [(s,SubsetOf [r]) | s <- ss]
       c _ (P.TClosureOf _)  = error "TClosureOf not handled"

simpleParse :: CmdLineParams -> String -> (Theory,RelInfo,Encoding,[Task])
simpleParse clp s = parse clp $ "signature { automatic } theory { " ++ removeBeginEnd s ++ "}"
 where removeBeginEnd = unwords . delete "begin" . delete "end" . words

convert :: RelInfo -> Encoding -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol] -> Formula
convert relI e = conv_ relI e . foldr (\f1 f2 -> f1 F.:&: f2) F.Top

conv_ :: RelInfo -> Encoding -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol -> Formula
conv_  _   _ F.Top               = taut
conv_  _   _ F.Bot               = neg taut
conv_  _   e (F.Prop p)          = prop e p
conv_  _   e (F.Nom  n)          = nom e n
conv_ relI e (F.Neg  f)          = neg $ conv_ relI e f
conv_ relI e (f1 F.:&:    f2)    = (conv_ relI e f1) `conj` (conv_ relI e f2)
conv_ relI e (f1 F.:|:    f2)    = (conv_ relI e f1) `disj` (conv_ relI e f2)
conv_ relI e (f1 F.:-->:  f2)    = (conv_ relI e f1) `imp`  (conv_ relI e f2)
conv_ relI e (f1 F.:<-->: f2)    = (conv_ relI e f1) `dimp` (conv_ relI e f2)
conv_ relI e (F.Diam r f)        = (specialiseDia r relI) (conv_ relI e f)
conv_ relI e (F.Box  r f)        = (specialiseBox r relI) (conv_ relI e f)
conv_ relI e (F.At   n f)        = at        e n (conv_ relI e f)
conv_ relI e (F.Down v f)        = downArrow e v (conv_ relI e f)
conv_ relI e (F.A f)             = univMod     (conv_ relI e f)
conv_ relI e (F.E f)             = existMod    (conv_ relI e f)
conv_ relI e (F.D f)             = dExistMod   (conv_ relI e f)
conv_ relI e (F.B f)             = dUnivMod    (conv_ relI e f)

type Connector = Formula -> Formula

specialiseDia :: S.RelSymbol -> RelInfo -> Connector
specialiseDia r relI = specialise r relI (diamond, diamondX, dExistMod, existMod)

specialiseBox :: S.RelSymbol -> RelInfo -> Connector
specialiseBox r relI = specialise r relI (box, boxX, dUnivMod, univMod)

specialise :: S.RelSymbol -> RelInfo -> (S.RelSymbol -> Connector, S.RelSymbol -> Connector, Connector, Connector) -> Connector
specialise (S.InvRelSymbol r) _ (relational, _ , _ , _) -- assume it is the simple input
 = relational $ S.InvRelSymbol r

specialise (S.RelSymbol r) relI (relational, rtclosure, difference, global)
 = case filter interesting (propsOf r) of
    (Difference:_) -> difference
    (Universal:_)  -> global
    []             -> relational $ S.RelSymbol r
    _              -> case specialise2 r relI of
                         Just_ r2        -> relational $ S.RelSymbol r2
                         Inverse r2      -> relational $ inv r2 relI
                         RTClosure r2    -> rtclosure  $ S.RelSymbol r2
                         RTClosureInv r2 -> rtclosure  $ inv r2 relI
    where
      interesting Difference      = True
      interesting Universal       = True
      interesting (InverseOf _)   = True
      interesting (TRClosureOf _) = True
      interesting _               = False
      propsOf r_                  = Map.findWithDefault [] r_ relI

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


class Invertible a where
  inv :: Rel -> RelInfo -> a

instance Invertible S.RelSymbol where
  inv r relI
   = case Map.lookup r relI of
      Nothing         -> S.RelSymbol r
      Just properties -> if Symmetric `elem` properties then S.RelSymbol r else S.InvRelSymbol r

instance Invertible RelSymbol where
  inv r relI
   = case Map.lookup r relI of
      Nothing         -> RelSymbol r
      Just properties -> if Symmetric `elem` properties then RelSymbol r else InvRelSymbol r

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
 list $ go r_ (Set.singleton r_)
 where
  go r seen =
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
      _  -> Set.insert r $ Set.unions $ map (\pa -> go pa newSeen) todo

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
  Map.foldWithKey startFromLeaf relI relI
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
                         ((par:_),_)  -> Just $ (par, invert status)
                                         where invert Not    = Not
                                               invert FunInj = FunInj
                                               invert Fun    = Inj
                                               invert Inj    = Fun
                         (_,(par:_))  -> Just $ (par, status)
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
nom  e (S.NomSymbol n)  = Lit $ ( (nomMap e)  Map.! n )
prop e (S.PropSymbol p) = Lit $ ( (propMap e) Map.! p )

{- Modalities -}
box, diamond, boxX, diamondX :: S.RelSymbol -> Formula -> Formula
univMod, existMod, dUnivMod, dExistMod :: Formula -> Formula
box        (S.RelSymbol r)    = Box   $ RelSymbol    r
box        (S.InvRelSymbol r) = Box   $ InvRelSymbol r
diamond    (S.RelSymbol r)    = Dia   $ RelSymbol    r
diamond    (S.InvRelSymbol r) = Dia   $ InvRelSymbol r
boxX       (S.RelSymbol r)    = BoxX  $ RelSymbol    r
boxX       (S.InvRelSymbol r) = BoxX  $ InvRelSymbol r
diamondX   (S.RelSymbol r)    = DiaX Nothing $ RelSymbol    r
diamondX   (S.InvRelSymbol r) = DiaX Nothing $ InvRelSymbol r
univMod    = A
existMod   = E
dUnivMod   = B
dExistMod  = D

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
dimp f1 f2 = (f1 `conj` f2) `disj` (neg f1 `conj` neg f2)

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
neg (Lit n)          = Lit (complementBit n 0)

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

data AccFormula = AccFormula DependencySet RelSymbol Prefix Prefix
     deriving (Eq, Ord)

instance Show AccFormula where
 show (AccFormula bprs r p1 p2) = show bprs ++ ":" ++ show p1 ++ "<" ++ show r ++ ">" ++ show p2

-- formula language

data LanguageInfo = LanguageInfo {   languageNoms :: [Int], -- ascending list
                                     relevantNoms :: [Int],
                                     languageUniv :: Bool,
                                     languagePast :: Bool,
                                     languageDiff :: Bool,
                                    languageTrans :: Bool,
                                     languageDown :: Bool }

instance Show LanguageInfo where
 show li =         "Input Language:"
           ++ "\n|" ++ yesnol "Noms" ( languageNoms li )
           ++ "\n|" ++ yesnol "Relevant Noms" ( relevantNoms li ) ++ "\n"
           ++ yesno "Univ, " ( languageUniv li )
           ++ yesno "Past, " ( languagePast li )
           ++ yesno "Trans, " ( languageTrans li)
           ++ yesno "Down." ( languageDown li )
  where yesno :: String -> Bool -> String
        yesno s b = ( if b then "" else "no " ) ++ s
        yesnol s l | null l = "no " ++ s
        yesnol s l = s ++ concatMap (\l_ -> ", " ++ showLit l_)  l

formulaLanguageInfo :: Formula -> LanguageInfo
formulaLanguageInfo f
 = LanguageInfo {   languageNoms = noms,
                    relevantNoms = relNoms,
                    languageUniv = hasUnivModality f,
                    languagePast = hasPast f,
                    languageDiff = hasDiffModality f,
                   languageTrans = hasTransClosure f,
                    languageDown = hasDownArrow f }

    where (allNoms_,relNoms_) = extractNominals f
          noms    = Set.toAscList allNoms_
          relNoms = Set.toAscList relNoms_

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

type AllNominals     = Set.Set Nom
type NegatedNominals = Set.Set Nom

extractNominals :: Formula -> (AllNominals, NegatedNominals)
extractNominals (Lit n)
   | isNominal n =  (Set.singleton (atom n), emptyOrSingleton)
                     where emptyOrSingleton = if isNegative n then Set.singleton (atom n) else Set.empty
extractNominals (At n f) = (Set.insert n noms, negNoms)
                            where (noms, negNoms) = extractNominals f
extractNominals f                    = composeFold (Set.empty,Set.empty) unionTwoSets extractNominals f
                                        where unionTwoSets (s1,s2) (s3,s4) = (Set.union s1 s3, Set.union s2 s4)

hasUnivModality :: Formula -> Bool
hasUnivModality (A _)     = True
hasUnivModality f         = composeFold False (||) hasUnivModality f

hasPast :: Formula -> Bool
hasPast (Dia (InvRelSymbol _) _) = True
hasPast f                        = composeFold False (||) hasPast f


hasDiffModality :: Formula -> Bool
hasDiffModality (B _)     = True
hasDiffModality f         = composeFold False (||) hasDiffModality f

hasTransClosure :: Formula -> Bool
hasTransClosure (BoxX _ _)   = True
hasTransClosure (DiaX _ _ _) = True
hasTransClosure f            = composeFold False (||) hasTransClosure f

hasDownArrow :: Formula -> Bool
hasDownArrow (Down _ _ ) = True
hasDownArrow f           = composeFold False (||) hasDownArrow f

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
         go v (Lit v2)              = (atom v == atom v2) && (isNegative v2)
         go v f                     = composeFold False (||) (go v) f

checkIfVariableNegatedOnce _ = error "checkIfVariableNegatedOnce : only down-arrow formulas"


-- backjumping

type Dependency = Int
type DependencySet = (Int,  -- smallest element of the set (or 0 if empty set)
                      IntSet.IntSet)

instance Ord PrFormula where
 compare (PrFormula pr1 ds1 f1) (PrFormula pr2 ds2 f2) =
  case fst ds1 `compare` fst ds2 of
   LT -> LT
   GT -> GT
   EQ -> compare (pr1,f1) (pr2,f2)

dsUnion :: DependencySet -> DependencySet -> DependencySet
dsUnion ds1 ds2 = let u = IntSet.union (snd ds1) (snd ds2)
                      m = if fst ds1 == 0 || fst ds2 == 0
                           then maybe 0 fst $ IntSet.minView u
                           else min (fst ds1) (fst ds2)
                  in (m,u)

dsUnions :: [DependencySet] -> DependencySet
dsUnions dss = let u = IntSet.unions $ map snd dss
                   m = minExceptOneZero (map fst dss)
                                        (maybe 0 fst $ IntSet.minView u )
               in (m,u)
 where
       minExceptOneZero []  _  = error "minExceptOneZero"
       minExceptOneZero [0] d  = d
       minExceptOneZero (x0:xs0) d
        = go x0 xs0
           where
              go m []     = m
              go _ (0:_)  = d
              go m (x:xs) = go (min m x) xs



dsInsert :: Dependency -> DependencySet -> DependencySet
dsInsert d ds = let s = IntSet.insert d (snd ds)
                    m = if fst ds == 0 -- in case that 0 was for an empty dependency set
                         then maybe 0 fst $ IntSet.minView s
                         else min d (fst ds)
                in (m,s)

dsMember :: Dependency -> DependencySet -> Bool
dsMember d ds = IntSet.member d (snd ds)

dsEmpty :: DependencySet
dsEmpty = (0,IntSet.empty)

dsMin :: DependencySet -> Int
dsMin = fst

dsShow :: DependencySet -> String
dsShow = show . IntSet.toList . snd

