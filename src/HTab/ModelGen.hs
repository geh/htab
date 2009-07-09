module HTab.ModelGen (Model, buildModel )

where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H
import qualified HyLo.Model as M

import HTab.Formula( Prefix, Atom (..), Rel, LanguageInfo(..),
                     NomSymbol(..), RelSymbol(..), PropSymbol(..), RelInfo )
import HTab.Branch( Branch(..), prefixes, getUrfather,
                    isInTheModel, relationIsInTheModel, getModelRepresentative,
                    isTransitive, isSymmetric )
import qualified HTab.DisjSet as DS
import HTab.DMap (flattenDMap, DMap(..), toMap )
import HTab.Relations ( getAllRels )

type Model = M.Model NomSymbol NomSymbol PropSymbol RelSymbol

buildModel :: Branch -> Model
buildModel branch =
  completeModel (relInfo branch) $ inducedModel $ H.herbrand es ps rs
 where
       bias = if null $ languageNoms $ inputLanguage branch
               then 0
               else 1 + (length $ languageNoms $ inputLanguage branch)
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [(NomSymbol $ show (getUrfather branch (DS.Nominal nString) + bias), n)
               | n@(NomSymbol nString) <- (languageNoms $ inputLanguage branch)]
             )
             (Set.fromList
               [(NomSymbol $ show (p + bias), NomSymbol $ show (p + bias))
               | p <- (prefixes branch), isInTheModel branch p]
             )
       ps = Set.fromList
             [(NomSymbol $ show (pre + bias), pro)
             | (pre,pro) <- prefixAndPropCouples]
       rs = Set.fromList $ map toSimpSig
              $ map (\(p1,r,p2) -> ((getModelRepresentative branch p1) + bias, r, (getModelRepresentative branch p2) + bias))
                    $ filter (relationIsInTheModel branch) $ getAllRels $ accStr branch

toSimpSig :: (Prefix,Rel,Prefix) -> (NomSymbol,RelSymbol,NomSymbol)
toSimpSig (p1,r,p2) = (NomSymbol (show p1), RelSymbol r, NomSymbol (show p2))

prefixAndProps :: Branch -> [(Prefix,PropSymbol)]
prefixAndProps br =
  [(pr, p_) | (pr , P p_) <- prPosLitProp]
 where clashable             = toMap $ clashStr br
       clashableRelevant     = Map.filterWithKey (\k _ -> isInTheModel br k) clashable
       prPosLitProp          = filter (isPosLitProp . snd) $ map fst $ filter (fst . snd) $ flattenDMap $ DMap clashableRelevant
       isPosLitProp   (P _)  = True
       isPosLitProp     _    = False

completeModel :: RelInfo -> Model -> Model
completeModel relI m = completeTransitivity relI $ completeSymmetry relI m

completeTransitivity :: RelInfo -> Model -> Model
completeTransitivity relI m = m{M.succs = \r w -> if isTransitive relI r
                                                   then getTransClos (M.succs m) r w
                                                   else M.succs m r w}

completeSymmetry :: RelInfo -> Model -> Model
completeSymmetry relI m = m{M.succs = \r w -> if isSymmetric relI r
                                               then getSymClos (M.worlds m) (M.succs m) r w
                                               else M.succs m r w}

getTransClos :: (Ord w) => (r -> w -> Set w) -> r -> w -> Set w
getTransClos succs_ r_ w_
 = go Set.empty Set.empty succs_ r_ w_
 where go seen todo succs r w
        = case Set.minView todo1 of
           Nothing                -> seen
           Just (nextWorld,todo2) -> go (Set.insert nextWorld seen) todo2 succs r nextWorld
          where todo1  = (Set.union (succs r w) todo) `Set.difference` seen

getSymClos :: (Ord w) => (Set w) -> (r -> w -> Set w) -> r -> w -> Set w
getSymClos worlds succs_ r_ w_
 = Set.union (succs_ r_ w_) syms
    where syms = Set.filter (hasAsSuccessor r_ w_) worlds
          hasAsSuccessor rel world2 world1 = Set.member world2 $ succs_ rel world1
