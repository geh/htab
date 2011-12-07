module HTab.ModelGen (Model, buildModel, toDot )

where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.IntMap as I
import HyLo.Model.Herbrand ( inducedModel )
import HyLo.Model.PrettyPrint ( toDotStr )
import qualified HyLo.Model.Herbrand as H
import qualified HyLo.Model as M

import qualified HyLo.Signature.String as S

import HTab.Formula( PrFormula(..), Formula(..),
                     Prefix, Rel, LanguageInfo(..), Encoding, int,
                     RelInfo, toPropSymbol, toNomSymbol, toRelSymbol, isPositiveProp )
import HTab.Branch( Branch(..), prefixes, getUrfather, BlockingMode(..),
                    patternOf, findByPattern,
                    isInTheModel, relationIsInTheModel, getModelRepresentative,
                    isTransitive, isSymmetric )
import qualified HTab.DisjSet as DS
import HTab.DMap (flatten)
import HTab.Relations ( allRels )

type Model = M.Model S.NomSymbol S.NomSymbol S.PropSymbol S.RelSymbol

buildModel :: Branch -> Model
buildModel br =
  completeModel e (relInfo br) $ inducedModel $ H.herbrand es ps rs
 where
  e = encoding br
  bias = if null $ languageNoms $ inputLanguage br
          then 0
          else 1 + length ( languageNoms $ inputLanguage br )
  es = Set.fromList $
        [(S.NomSymbol $ show (getUrfather br (DS.Nominal n) + bias), toNomSymbol e n)
         | n <- languageNoms $ inputLanguage br]
        ++ [(S.NomSymbol $ show (p + bias), S.NomSymbol $ show (p + bias))
            | p <- prefixes br, isInTheModel br p]
  ps = Set.fromList
        [(S.NomSymbol $ show (pre + bias), pro) | (pre,pro) <- prefixAndProps br]
  pbBlocked =
     if blockMode br `elem` [PatternBlocking,AnywhereBlocking]
        then
         [ (pr, r, pr2) |
             pr <- prefixes br,
             isInTheModel br pr,
             blockedDia@(PrFormula _ _ (Dia r _)) <- get [] pr (blockedDias br),
             let pat = patternOf br blockedDia,
             let pr2 = findByPattern br pat ]
        else []
  rels = (filter (relationIsInTheModel br) $ allRels $ accStr br) ++ pbBlocked
  inModel = flip getModelRepresentative
  rs = Set.fromList
        $ map (toSimpSig e)
        $ map (\(p1,r,p2) -> ((p1 `inModel` br) + bias , r,(p2 `inModel` br) + bias))
          rels

toSimpSig :: Encoding -> (Prefix,Rel,Prefix) -> (S.NomSymbol,S.RelSymbol,S.NomSymbol)
toSimpSig e (p1,r,p2) = (S.NomSymbol (show p1), toRelSymbol e r, S.NomSymbol (show p2))

prefixAndProps :: Branch -> [(Prefix,S.PropSymbol)]
prefixAndProps br =
  [(pr, toPropSymbol e p_) | (pr , p_) <- prPosLitProp ++ prefWitPositive]
 where
  litsRelevant = I.filterWithKey (\k _ -> isInTheModel br k) (literals br)
  prPosLitProp = filter (isPositiveProp . snd) $ map fst $ flatten $ litsRelevant
  --
  witMap = brWitnesses br
  witMapRelevant = I.filterWithKey (\k _ -> isInTheModel br k) witMap
  prefWitPositive = filter (isPositiveProp . snd) $ map fst $ flatten $ witMapRelevant
  --
  e = encoding br

completeModel :: Encoding -> RelInfo -> Model -> Model
completeModel e relI m = completeTrans e relI $ completeSym e relI m

completeTrans :: Encoding -> RelInfo -> Model -> Model
completeTrans e relI m
 = m{M.succs = \rs@(S.RelSymbol r) w
                 -> if isTransitive relI (int e r)
                     then getTransClos (M.succs m) rs w
                     else M.succs m rs w}

completeSym :: Encoding -> RelInfo -> Model -> Model
completeSym e relI m
 = m{M.succs = \rs@(S.RelSymbol r) w
                 -> if isSymmetric relI (int e r)
                     then getSymClos (M.worlds m) (M.succs m) rs w
                     else M.succs m rs w}

getTransClos :: (Ord w) => (r -> w -> Set w) -> r -> w -> Set w
getTransClos succs_ r_ w_
 = go Set.empty Set.empty succs_ r_ w_
 where
  go seen todo succs r w
   = case Set.minView todo1 of
      Nothing                -> seen
      Just (nextWorld,todo2) -> go (Set.insert nextWorld seen) todo2 succs r nextWorld
     where todo1  = (succs r w `Set.union` todo) `Set.difference` seen

getSymClos :: (Ord w) => Set w -> (r -> w -> Set w) -> r -> w -> Set w
getSymClos worlds succs_ r_ w_
 = succs_ r_ w_ `Set.union` syms
    where syms = Set.filter (hasAsSuccessor r_ w_) worlds
          hasAsSuccessor rel world2 world1 = Set.member world2 $ succs_ rel world1

toDot :: Model -> String
toDot = toDotStr

get :: a -> Int -> I.IntMap a -> a
get = I.findWithDefault
