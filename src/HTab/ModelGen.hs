module HTab.ModelGen (Model, buildModel, toDot )

where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.IntMap as IntMap
import HyLo.Model.Herbrand ( inducedModel )
import HyLo.Model.PrettyPrint ( toDotStr )
import qualified HyLo.Model.Herbrand as H
import qualified HyLo.Model as M

import qualified HyLo.Signature.String as S

import HTab.Formula( Prefix, Rel, LanguageInfo(..), Encoding, int,
                     RelInfo, toPropSymbol, toNomSymbol, toRelSymbol, isPositiveProp )
import HTab.Branch( Branch(..), prefixes, getUrfather,
                    isInTheModel, relationIsInTheModel, getModelRepresentative,
                    isTransitive, isSymmetric )
import qualified HTab.DisjSet as DS
import HTab.DMap (flatten, DMap(..), toMap )
import HTab.Relations ( allRels )

type Model = M.Model S.NomSymbol S.NomSymbol S.PropSymbol S.RelSymbol

buildModel :: Branch -> Model
buildModel branch =
  completeModel e (relInfo branch) $ inducedModel $ H.herbrand es ps rs
 where
       e = encoding branch
       bias = if null $ languageNoms $ inputLanguage branch
               then 0
               else 1 + length ( languageNoms $ inputLanguage branch )
       es = Set.union
             (Set.fromList
               [(S.NomSymbol $ show (getUrfather branch (DS.Nominal n) + bias), toNomSymbol e n)
               | n <- languageNoms $ inputLanguage branch]
             )
             (Set.fromList
               [(S.NomSymbol $ show (p + bias), S.NomSymbol $ show (p + bias))
               | p <- prefixes branch, isInTheModel branch p]
             )
       ps = Set.fromList
             [(S.NomSymbol $ show (pre + bias), pro)
             | (pre,pro) <- prefixAndProps branch]
       rs = Set.fromList $ map (toSimpSig e)
              $ map (\(p1,r,p2) -> (getModelRepresentative branch p1 + bias, r, getModelRepresentative branch p2 + bias))
                    $ filter (relationIsInTheModel branch) $ allRels $ accStr branch

toSimpSig :: Encoding -> (Prefix,Rel,Prefix) -> (S.NomSymbol,S.RelSymbol,S.NomSymbol)
toSimpSig e (p1,r,p2) = (S.NomSymbol (show p1), toRelSymbol e r, S.NomSymbol (show p2))

prefixAndProps :: Branch -> [(Prefix,S.PropSymbol)]
prefixAndProps br =
  [(pr, toPropSymbol e p_) | (pr , p_) <- prPosLitProp ++ prefWitPositive]
 where clashable             = toMap $ clashStr br
       clashableRelevant     = IntMap.filterWithKey (\k _ -> isInTheModel br k) clashable
       prPosLitProp          = filter (isPositiveProp . snd) $ map fst $ flatten $ DMap clashableRelevant
       --
       witMap = toMap $ brWitnesses br
       witMapRelevant = IntMap.filterWithKey (\k _ -> isInTheModel br k) witMap
       prefWitPositive = filter (isPositiveProp . snd) $ map fst $ flatten $ DMap witMapRelevant
       --
       e = encoding br

completeModel :: Encoding -> RelInfo -> Model -> Model
completeModel e relI m = completeTransitivity e relI $ completeSymmetry e relI m

completeTransitivity :: Encoding -> RelInfo -> Model -> Model
completeTransitivity e relI m = m{M.succs = \rs@(S.RelSymbol r) w
                                                 -> if isTransitive relI (int e r)
                                                      then getTransClos (M.succs m) rs w
                                                      else M.succs m rs w}

completeSymmetry :: Encoding -> RelInfo -> Model -> Model
completeSymmetry e relI m = m{M.succs = \rs@(S.RelSymbol r) w
                                             -> if isSymmetric relI (int e r)
                                                  then getSymClos (M.worlds m) (M.succs m) rs w
                                                  else M.succs m rs w}

getTransClos :: (Ord w) => (r -> w -> Set w) -> r -> w -> Set w
getTransClos succs_ r_ w_
 = go Set.empty Set.empty succs_ r_ w_
 where go seen todo succs r w
        = case Set.minView todo1 of
           Nothing                -> seen
           Just (nextWorld,todo2) -> go (Set.insert nextWorld seen) todo2 succs r nextWorld
          where todo1  = ((succs r w) `Set.union` todo) `Set.difference` seen

getSymClos :: (Ord w) => Set w -> (r -> w -> Set w) -> r -> w -> Set w
getSymClos worlds succs_ r_ w_
 = Set.union (succs_ r_ w_) syms
    where syms = Set.filter (hasAsSuccessor r_ w_) worlds
          hasAsSuccessor rel world2 world1 = Set.member world2 $ succs_ rel world1

toDot :: Model -> String
toDot = toDotStr
