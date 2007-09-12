module ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H

import qualified HyLo.Formula.NNF as NNF

import Formula(AccFormula(..), Nominal, Prefix, Prop, Formula (..), Atom (..),
               PrFormula(..) )
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
       rs = Set.fromList $ map (accToNNF bias) (accStr branch)

accToNNF :: Int -> AccFormula
             -> NNF.Formula S.NomSymbol S.PropSymbol S.RelSymbol S.StateVar (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF bias (AccFormula r p1 p2) =
  NNF.At (S.NomSymbol (p1+bias)) $ NNF.Diam (S.RelSymbol r) $ NNF.Nom (S.NomSymbol (p2+bias))

urfatherOrPrefixZero :: Branch -> Nominal -> Prefix
urfatherOrPrefixZero br n =
  case (Map.lookup n (nomToPref br)) of
     Just p -> p
     Nothing -> 0

prefixAndProps :: Branch -> [(Prefix,Prop)]
prefixAndProps br =
  [(pr,p_) | (PrFormula pr (PosLit (P p_))) <- prPosLitProp]
 where seen = seenStr br
       prPosLitProp = filter isPosLitProp $ map fst $ filter snd $ Map.toList seen

isPosLitProp :: PrFormula -> Bool
isPosLitProp (PrFormula _ (PosLit (P _))) = True
isPosLitProp _ = False



