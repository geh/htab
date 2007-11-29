module ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H

import qualified HyLo.Formula.NNF as NNF

import Formula( Prefix, Formula (..), Atom (..), Rel,
                NomSymbol(..), RelSymbol(..), PropSymbol(..), StateVar)
import Branch( Branch(..) , nominals, prefixes,getUrfather)

type HerbrandModel = H.HerbrandModel NomSymbol PropSymbol RelSymbol

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
   H.herbrand es ps rs
 where
       newToOldNomsMap = newToOldNoms branch
       bias = if Map.null newToOldNomsMap then 0
                                          else 1 + (maximum (map unpackNomSymbol $ Map.elems newToOldNomsMap))
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [NNF.At
                (NomSymbol ((urfatherOrPrefixZero branch n_) + bias))
                (NNF.Nom n) | n_ <- (nominals branch),
                            let n = (Map.!) newToOldNomsMap n_]
             )
             (Set.fromList
               [NNF.At
                (NomSymbol (p + bias))
                (NNF.Nom (NomSymbol (p + bias))) | p <- (prefixes branch)]
             )
       ps = Set.fromList
             [NNF.At
               (NomSymbol (pre+bias))
               (NNF.Prop pro) | (pre,pro) <- prefixAndPropCouples]
       rs = Set.fromList $ map accToNNF
              $ concatMap (\((p1,r),bp_ps) -> map (\(_,p2) -> (p1 + bias, r, (getUrfather branch p2)  + bias))
                                                  bp_ps)
                          (Map.assocs $ accStr branch)

accToNNF :: (Prefix,Rel,Prefix)
             -> NNF.Formula NomSymbol PropSymbol RelSymbol StateVar (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF (p1,r,p2) =
  NNF.At (NomSymbol p1) $ NNF.Diam (RelSymbol r) $ NNF.Nom (NomSymbol p2)

urfatherOrPrefixZero :: Branch -> NomSymbol -> Prefix
urfatherOrPrefixZero br n =
  case (Map.lookup n (nomToPref br)) of
     Just p -> p
     Nothing -> 0

prefixAndProps :: Branch -> [(Prefix,PropSymbol)]
prefixAndProps br =
  [(pr,p_) | (pr , PosLit (P p_)) <- prPosLitProp]
 where seen = seenStr br
       prPosLitProp = filter isPosLitProp $ map fst $ filter (fst . snd) $ Map.toList seen

isPosLitProp :: (Prefix,Formula) -> Bool
isPosLitProp (_, PosLit (P _)) = True
isPosLitProp _ = False


unpackNomSymbol :: NomSymbol -> Int
unpackNomSymbol (NomSymbol n) = n
