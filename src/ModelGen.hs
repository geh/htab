module ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H

import qualified HyLo.Formula.NNF as NNF

import Formula(Nominal, Prefix,Rel, Prop, Formula (..), Atom (..))
import Branch( Branch(..) , nominals)

import qualified HyLo.Signature.Simple as S -- to have types with distinct "show" representations

type HerbrandModel = H.HerbrandModel S.NomSymbol S.PropSymbol S.RelSymbol

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
   H.herbrand es ps rs
 where bias = (inputLanguage branch)
       prefixAndPropCouples = prefixAndProps branch
       es = Set.fromList
             [NNF.At
              (S.NomSymbol ((urfatherOrPrefixZero branch n)+ bias))
              (NNF.Nom (S.NomSymbol n)) | n <- (nominals branch)]
       ps = Set.fromList
             [NNF.At
               (S.NomSymbol (pr+bias))
               (NNF.Prop (S.PropSymbol p)) | (pr,p) <- prefixAndPropCouples]
       rs = Set.fromList $ map (accToNNF bias)
              $ concatMap (\((p1,r),bp_ps) -> map (\(_,p2) -> (p1,r,p2))
                                                  bp_ps)
                          (Map.assocs $ accStr branch)

accToNNF :: Int -> (Prefix,Rel,Prefix)
             -> NNF.Formula S.NomSymbol S.PropSymbol S.RelSymbol S.StateVar (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF bias (p1,r,p2) =
  NNF.At (S.NomSymbol (p1+bias)) $ NNF.Diam (S.RelSymbol r) $ NNF.Nom (S.NomSymbol (p2+bias))

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



