module ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H

import qualified HyLo.Formula.NNF as NNF

import Formula(Nominal, Prefix,Rel, Prop, Formula (..), Atom (..))
import Branch( Branch(..) , nominals, prefixes,getUrfather)

import qualified HyLo.Signature.Simple as S -- to have types with distinct "show" representations

type HerbrandModel = H.HerbrandModel S.NomSymbol S.PropSymbol S.RelSymbol

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
   H.herbrand es ps rs
 where
       newToOldNomsMap = newToOldNoms branch
       bias = if Map.null newToOldNomsMap then 0
                                          else 1 + (maximum (Map.elems newToOldNomsMap))
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [NNF.At
                (S.NomSymbol ((urfatherOrPrefixZero branch n_) + bias))
                (NNF.Nom (S.NomSymbol n)) | n_ <- (nominals branch),
                                            let n = (Map.!) newToOldNomsMap n_]
             )
             (Set.fromList
               [NNF.At
                (S.NomSymbol (p + bias))
                (NNF.Nom (S.NomSymbol (p + bias))) | p <- (prefixes branch)]
             )
       ps = Set.fromList
             [NNF.At
               (S.NomSymbol (pr+bias))
               (NNF.Prop (S.PropSymbol p)) | (pr,p) <- prefixAndPropCouples]
       rs = Set.fromList $ map (accToNNF branch bias)
              $ concatMap (\((p1,r),bp_ps) -> map (\(_,p2) -> (p1,r,p2))
                                                  bp_ps)
                          (Map.assocs $ accStr branch)

accToNNF :: Branch -> Int -> (Prefix,Rel,Prefix)
             -> NNF.Formula S.NomSymbol S.PropSymbol S.RelSymbol S.StateVar (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF branch bias (p1,r,p2) =
  NNF.At (S.NomSymbol (p1+bias)) $ NNF.Diam (S.RelSymbol r) $ NNF.Nom (S.NomSymbol (p2_urfather+bias))
   where p2_urfather = getUrfather branch p2


urfatherOrPrefixZero :: Branch -> Nominal -> Prefix
urfatherOrPrefixZero br n =
  case (Map.lookup n (nomToPref br)) of
     Just p -> p
     Nothing -> 0

prefixAndProps :: Branch -> [(Prefix,Prop)]
prefixAndProps br =
  [(pr,p_) | (pr , PosLit (P p_)) <- prPosLitProp]
 where seen = seenStr br
       prPosLitProp = filter isPosLitProp $ map fst $ filter (fst . snd) $ Map.toList seen

isPosLitProp :: (Prefix,Formula) -> Bool
isPosLitProp (_, PosLit (P _)) = True
isPosLitProp _ = False



