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

type HerbrandModel = H.HerbrandModel Int Int Int

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
   H.herbrand es ps rs
 where bias = (inputLanguage branch) - 1
       prefixAndPropCouples = prefixAndProps branch
       es = Set.fromList [NNF.At ((urfatherOrPrefixZero branch n)+ bias) (NNF.Nom n) | n <- (nominals branch)]
       ps = Set.fromList [NNF.At (pr+bias) (NNF.Prop p) | (pr,p) <- prefixAndPropCouples]
       rs = Set.fromList $ map (accToNNF bias) (accStr branch)

accToNNF :: Int -> AccFormula -> NNF.Formula Int Int Int Int (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF bias (AccFormula r p1 p2) = NNF.At (p1+bias) $ NNF.Diam r $ NNF.Nom (p2+bias)

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



