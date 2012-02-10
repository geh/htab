module HTab.Formula

(Nom, Prop, Rel, Prefix, Formula(..), Literal(..), Atom(..),
DependencySet, Dependency, Depth,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow, addDeps,
PrFormula(..),showLess,
LanguageInfo(..), neg,
conj, disj, taut,
prop, nom, prefix, negPr,
replaceVar,
firstPrefixedFormula,
parse, simpleParse, Theory, RelInfo, Task,
showRelInfo, negLit,
encodeValidityTest, encodeSatTest, encodeRetrieveTask,
HyLoFormula, RelProperty(..),
isPositiveNom, isPositiveProp, isProp
,parseGenerators,Generator,applyGenerators
)

 where
import Debug.Trace
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntSet as IntSet
import Data.List ( delete, nub, intercalate, isPrefixOf )

import Data.Char ( toUpper )

import qualified HyLo.Signature.String as S

import HyLo.Signature( HasSignature(..), nomSymbols, relSymbols )

import qualified HyLo.InputFile as InputFile
import qualified HyLo.InputFile.Parser as P
import qualified HyLo.Formula as F
import HTab.CommandLine ( Params(..) )

type Prefix  = Int
type Rel     = String
type Nom     = String
type Prop    = String
data Atom    = Taut | N String | P String deriving(Eq, Ord)
data Literal = PosLit Atom | NegLit Atom deriving(Eq, Ord)

negLit :: Literal -> Literal
negLit (PosLit a) = NegLit a
negLit (NegLit a) = PosLit a

isPositiveNom, isPositiveProp, isProp :: Literal -> Bool
isPositiveNom (PosLit (N _))  = True
isPositiveNom _               = False
isPositiveProp (PosLit (P _)) = True
isPositiveProp _              = False
isProp (PosLit (P _))         = True
isProp (NegLit (P _))         = True
isProp _                      = False 

instance Show Atom where
 show (Taut) = "T"
 show (N n)  = n
 show (P p)  = p

instance Show Literal where
 show (PosLit a) = show a
 show (NegLit a) =  '!' : show a

data Formula
     = Lit    Literal
     | Con   (Set Formula)
     | Dis   (Set Formula)
     | At     Nom Formula
     | Down   Nom Formula
     | Box    Rel     Formula
     | Dia    Rel     Formula
     | A      Formula
     | E      Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (Lit a)    = show a
 show (Con fs)   = "^" ++ show (list fs)
 show (Dis fs)   = "v" ++ show (list fs)
 show (At n f)   =  n  ++ ":(" ++ show f ++ ")"
 show (Box r f)  = "[" ++ r ++ "]"   ++ show f
 show (Dia r f)  = "<" ++ r ++ ">"   ++ show f
 show (A f)      = "A" ++ show f
 show (E f)      = "E" ++ show f
 show (Down n f) = "down " ++ n ++ "." ++ show f

-- parsing of the input file

type Theory  = Formula
type Task    = P.InferenceTask
type PRelInfo = [P.RelInfo]

type RelInfo = Map String [RelProperty]
data RelProperty   =   Reflexive
                     | Transitive
                     | Universal
                     --
                     | SubsetOf [Rel]
                     deriving (Eq, Show, Ord)

showRelInfo :: RelInfo -> String
showRelInfo = Map.foldrWithKey (\r v -> (++ " " ++ show r ++ " -> " ++ show v )) ""

parse :: Params -> String -> (Theory,RelInfo,LanguageInfo,[Task])
parse p s
  = (theory, relInfo, fLang, tasks)
    where parseOutput = InputFile.myparse s       -- direct parse from hylolib
          pRelInfo    = P.relations parseOutput
          relInfo     = forceProperties p parseOutput $ convertToOurType pRelInfo
          theory      = convert relInfo $ P.theory parseOutput
          tasks       = P.tasks parseOutput
          fLang       = langInfo parseOutput

-- add properties specified by the --all-PROP parameters
-- in order to work in case of automatic signature

forceProperties :: Params -> P.ParseOutput -> RelInfo -> RelInfo
forceProperties p po relI
 = foldr addToAll relI (list rels)
   where
         rels = Set.map (\(S.RelSymbol r) -> up r) $ Set.unions $ map (relSymbols . getSignature) theory
         addToAll r = Map.insertWith (\c1 c2 -> nub $ c1 ++ c2) r conds
         conds = map snd $
                   filter fst   [(allTransitive p, Transitive),
                                 (allReflexive  p, Reflexive )]
         theory =  P.theory po


convertToOurType :: PRelInfo -> RelInfo
 -- and add for each relation in the formula, the relevant key
convertToOurType prelI = foldr insertRelProp Map.empty (concatMap convertOne prelI)
 where insertRelProp (rs,pr) = Map.insertWith (++) rs [pr]
       convertOne (r,props)  = concatMap (c r) props
       c r P.Reflexive       = [(r,Reflexive    )]
       c _ P.Symmetric       = error "Symmetric not handled"
       c r P.Transitive      = [(r,Transitive   )]
       c r P.Universal       = [(r,Universal    )]
       c _ (P.InverseOf _)   = error "InverseOf not handled" 
       c r (P.SubsetOf ss)   = [(r,SubsetOf [ s | s <- ss])]
       c r (P.Equals ss)     = [(r,SubsetOf [ s | s <- ss])]
                               ++ [(s,SubsetOf [r]) | s <- ss]
       c _ (P.TClosureOf _)  = error "TClosureOf not handled"
       c _ (P.TRClosureOf _) = error "TRClosureOf not handled"
       c _ P.Functional      = error "Functional not handled"
       c _ P.Injective       = error "Injective not handled"
       c _ P.Difference      = error "Difference not handled"

simpleParse :: Params -> String -> (Theory,RelInfo,LanguageInfo)
simpleParse p s =
 let (t,r,i,_) = parse p $ "signature { automatic } theory { " ++ removeBeginEnd s ++ "}"
 in (t,r,i)
 where removeBeginEnd = unwords . delete "begin" . delete "end" . words

convert :: RelInfo -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol]
             -> Formula
convert relI = conv_ relI . foldr (F.:&:) F.Top

conv_ :: RelInfo -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol
           -> Formula
conv_  _   F.Top               = taut
conv_  _   F.Bot               = neg taut
conv_  _   (F.Prop p)          = prop p
conv_  _   (F.Nom  n)          = nom n
conv_ relI (F.Neg  f)          = neg $ conv_ relI f
conv_ relI (f1 F.:&:    f2)    = conv_ relI f1 `conj` conv_ relI f2
conv_ relI (f1 F.:|:    f2)    = conv_ relI f1 `disj` conv_ relI f2
conv_ relI (f1 F.:-->:  f2)    = conv_ relI f1 `imp`  conv_ relI f2
conv_ relI (f1 F.:<-->: f2)    = conv_ relI f1 `dimp` conv_ relI f2
conv_ relI (F.Diam (S.RelSymbol r) f)        = specialiseDia (up r) relI (conv_ relI f)
conv_ relI (F.Box  (S.RelSymbol r) f)        = specialiseBox (up r) relI (conv_ relI f)
conv_ relI (F.At   n f)        = at        n (conv_ relI f)
conv_ relI (F.Down v f)        = downArrow v (conv_ relI f)
conv_ relI (F.A f)             = univMod     (conv_ relI f)
conv_ relI (F.E f)             = existMod    (conv_ relI f)
conv_ _    f                 = error (show f ++ "not supported")

type Connector = Formula -> Formula

specialiseDia :: String -> RelInfo -> Connector
specialiseDia r relI = specialise r relI (diamond, existMod)

specialiseBox :: String -> RelInfo -> Connector
specialiseBox r relI = specialise r relI (box, univMod)

specialise :: String -> RelInfo -> (String -> Connector, Connector)
                -> Connector
specialise r relI (relational, global)
 | Universal `elem` props  = global
 | otherwise = relational r
 where props = Map.findWithDefault [] r relI

type HyLoFormula = F.Formula S.NomSymbol S.PropSymbol S.RelSymbol

encodeValidityTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeValidityTest relI th fs
 = neg $ conj th (convert relI fs)

encodeSatTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeSatTest relI th fs
 = conj th (convert relI fs)

encodeRetrieveTask :: RelInfo -> LanguageInfo -> Formula -> [HyLoFormula]
                        -> ([String],[Formula])
encodeRetrieveTask relI fLang theory fs
 = (noms , map (\n -> conj theory (At n (neg $ convert relI fs))) noms)
   where noms = languageNoms fLang

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
nom  :: S.NomSymbol -> Formula
prop :: S.PropSymbol -> Formula

taut                  = Lit $ PosLit Taut
nom  (S.NomSymbol n)  = Lit $ PosLit $ N $ up n
prop (S.PropSymbol p) = Lit $ PosLit $ P $ up p

{- Modalities -}
box, diamond :: String -> Formula -> Formula
univMod, existMod :: Formula -> Formula
box        r    = Box   r
diamond    r    = Dia   r
univMod    = A
existMod   = E

{- binder -}
downArrow :: S.NomSymbol -> Formula -> Formula
downArrow (S.NomSymbol n) = Down (up n)

{- Hybrid operators -}
at :: S.NomSymbol -> Formula -> Formula
at (S.NomSymbol n) = At (up n)

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
isTrue  (Lit (PosLit Taut)) = True
isTrue   _                  = False
isFalse (Lit (NegLit Taut)) = True
isFalse  _                  = False

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
neg (Lit (PosLit a)) = Lit (NegLit a)
neg (Lit (NegLit a)) = Lit (PosLit a)


-- prefixed formula

type Depth = Int -- modal depth of current formula wrt input formula

data PrFormula = PrFormula Prefix DependencySet Depth Formula
 deriving Eq

instance Show PrFormula where
 show (PrFormula pr ds md f) = intercalate ":" [show pr, show ds, show md, show f]

showLess :: PrFormula -> String
showLess (PrFormula pr _ md f) = show pr ++ ":" ++ show (md,f)

prefix :: Prefix -> DependencySet -> Depth -> Set Formula -> [PrFormula]
prefix p bps md fs = [PrFormula p bps md formula|formula <- list fs]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 dsEmpty 0

negPr :: PrFormula -> PrFormula
negPr (PrFormula p ds md f) = PrFormula p ds md (neg f)

-- formula language

data LanguageInfo = LanguageInfo { languageNoms :: [String] } -- ascending

instance Show LanguageInfo where
 show li = "Input Language:\n|" ++ yesnol "Noms " ( languageNoms li )
  where yesnol s l | null l = "no " ++ s
        yesnol s l = s ++ intercalate ", " l

langInfo :: P.ParseOutput -> LanguageInfo
langInfo po
 = LanguageInfo { languageNoms = noms }
    where noms = nub $ map (\(S.NomSymbol n) -> up n) $ concatMap (list . nomSymbols . getSignature) theory
          theory =  P.theory po

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

replaceVar :: String -> String -> Formula -> Formula
replaceVar v n a@(Lit (PosLit (N v2))) = if v == v2 then Lit (PosLit (N n)) else a
replaceVar v n a@(Lit (NegLit (N v2))) = if v == v2 then Lit (NegLit (N n)) else a
replaceVar v n a@(Down v2 f) = if v == v2 then a   -- variable capture
                                          else Down v2 (replaceVar v n f)
replaceVar v n (At v2 f)   = if v == v2 then At n (replaceVar v n f)
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

type Generator = [(Depth,Literal,Literal)]

applyGenerators :: [Generator] -> PrFormula -> [PrFormula]
applyGenerators gens f
 = if null res
    then res
    else trace ("SYM on " ++ showLess f ++ ":" ++ intercalate "," (map showLess res))
               res
   where res =  delete f $ nub $ map (\gen -> subst gen f) gens

subst :: Generator -> PrFormula -> PrFormula
subst gen (PrFormula pr ds md f) = PrFormula pr ds md $ substNorm (normGen gen md) f

normGen :: Generator -> Depth -> Generator
normGen g md = [(md1-md,a1,a2) | (md1,a1,a2) <- g, md1 - md >= 0]

substNorm :: Generator -> Formula -> Formula
-- act as if we were at modal depth 0 and generator has been adjusted
substNorm gen (Lit a)     = Lit $ genOnLit gen a
substNorm gen (At n f)    = At n $ substNorm (normGen gen 1) f
substNorm gen (Box r f)   = Box r $ substNorm (normGen gen 1) f
substNorm gen (Dia r f)   = Dia r $ substNorm (normGen gen 1) f
substNorm gen (Down n f)  = Down n $ substNorm (normGen gen 1) f
substNorm gen (A f)       = A $ substNorm (normGen gen 1) f
substNorm gen (E f)       = E $ substNorm (normGen gen 1) f
substNorm gen f           = composeMap id (substNorm gen) f

genOnLit :: Generator -> Literal -> Literal
genOnLit [] l           = l
genOnLit ((d,x,y):g) l
 | d == 0 && x == l        = y
 | d == 0 && x == negLit l = negLit y
 | d == 0 && y == l        = x
 | d == 0 && y == negLit l = negLit y
 | otherwise               = genOnLit g l

parseGenerators :: String -> [Generator]
parseGenerators genString
 =  [lineToGen l [] | l <- lines genString,
                        not ("%" `isPrefixOf` l),
                        not (null l)            ]

-- turn such a line into a generator:
-- 4 -2 5, 5 3 5, 0 -6 -3
lineToGen :: String -> Generator -> Generator
lineToGen "" g    = g
lineToGen (',':l) g = lineToGen l g
lineToGen l g       = let triple = takeWhile (/= ',') l
                          remainder = dropWhile (/= ',') l
                          [md,l1,l2] = map read $ words triple
                          -- we read X for PX or -Y for -PY,
                          -- now we need to convert it in atom
                          a1 = if l1 < 0
                                then NegLit $ P $ "P" ++ show (negate l1)
                                else PosLit $ P $ "P" ++ show l1
                          a2 = if l2 < 0
                                then NegLit $ P $ "P" ++ show (negate l2)
                                else PosLit $ P $ "P" ++ show l2
                      in lineToGen remainder (g ++ [(md,a1,a2)])

up :: String -> String
up = map toUpper
