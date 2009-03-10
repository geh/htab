module HTab.ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map
import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H
import qualified HyLo.Formula.NNF as NNF

import HTab.Formula( Prefix, Atom (..), Rel, LanguageInfo(..),
                     NomSymbol(..), RelSymbol(..), PropSymbol(..) )
import HTab.Branch( Branch(..), prefixes, getUrfather,
                    isInTheModel, getModelRepresentative )
import qualified HTab.DisjSet as DS
import HTab.DMap (flattenDMap)

type HerbrandModel = H.HerbrandModel NomSymbol PropSymbol RelSymbol

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
  H.herbrand es ps rs
 where
       bias = if null $ languageNoms $ inputLanguage branch
               then 0
               else 1 + (length $ languageNoms $ inputLanguage branch)
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [NNF.At
                (NomSymbol $ show (getUrfather branch (DS.Nominal nString) + bias))
                (NNF.Nom n) | n@(NomSymbol nString) <- (languageNoms $ inputLanguage branch)]
             )
             (Set.fromList
               [NNF.At
                (NomSymbol $ show (p + bias))
                (NNF.Nom (NomSymbol $ show (p + bias))) | p <- (prefixes branch), isInTheModel branch p]
             )
       ps = Set.fromList
             [NNF.At
               (NomSymbol $ show (pre + bias))
               (NNF.Prop pro) | (pre,pro) <- prefixAndPropCouples]
       rs = Set.fromList $ map accToNNF
              $ concatMap (\((p1,rel),bp_ps) -> map (\(_,p2) -> (p1 + bias, rel, (getModelRepresentative branch p2) + bias))
                                                    bp_ps)
                          (filter (isInTheModel branch . fst . fst) $ flattenDMap $ accStr branch)

accToNNF :: (Prefix,Rel,Prefix) -> NNF.Formula NomSymbol PropSymbol RelSymbol (NNF.At (NNF.Diam NNF.Nom))
accToNNF (p1,r,p2) =
  NNF.At (NomSymbol (show p1)) $ NNF.Diam (RelSymbol r) $ NNF.Nom (NomSymbol (show p2))

prefixAndProps :: Branch -> [(Prefix,PropSymbol)]
prefixAndProps br =
  [(pr, p_) | (pr , P p_) <- prPosLitProp]
 where clashable             = clashStr br
       clashableRelevant     = Map.filterWithKey (\k _ -> isInTheModel br k) clashable
       prPosLitProp          = filter (isPosLitProp . snd) $ map fst $ filter (fst . snd) $ flattenDMap clashableRelevant
       isPosLitProp   (P _)  = True
       isPosLitProp     _    = False

