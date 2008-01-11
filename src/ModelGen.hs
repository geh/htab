module ModelGen (HerbrandModel, buildHerbrandModel, inducedModel )

where

import qualified Data.Set as Set
import qualified Data.Map as Map

import HyLo.Model.Herbrand ( inducedModel )
import qualified HyLo.Model.Herbrand as H

import qualified HyLo.Formula.NNF as NNF

import Formula( Prefix, Formula (..), Atom (..), Rel,
                NomSymbol(..), RelSymbol(..), PropSymbol(..), StateVar,
                LanguageInfo(..) )
import Branch( Branch(..) , prefixes,getUrfather,
               isInclusionUrfather, getInclusionUrfather,
               BlockingMode(..) )

import qualified DisjSet as DS

type HerbrandModel = H.HerbrandModel NomSymbol PropSymbol RelSymbol

buildHerbrandModel :: Branch -> HerbrandModel
buildHerbrandModel branch =
 case (blockMode branch) of
  NoBlocking        -> H.herbrand es ps rs
  InclusionBlocking -> buildHerbrandModel_univMod branch
 where
       bias = if null $ languageNoms $ inputLanguage branch
               then 0
               else 1 + (maximum $ map unpackNomSymbol $ languageNoms $ inputLanguage branch)
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [NNF.At
                (NomSymbol ((urfatherOrPrefixZero branch n) + bias))
                (NNF.Nom n) | n <- (languageNoms $ inputLanguage branch)]
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
              $ concatMap (\((p1,r),bp_ps) -> map (\(_,p2) -> (p1 + bias, r, (getUrfather branch (DS.Prefix p2)) + bias))
                                                  bp_ps)
                          (flattenDMap $ accStr branch)

buildHerbrandModel_univMod :: Branch -> HerbrandModel
buildHerbrandModel_univMod branch =
  H.herbrand es ps rs
 where
       bias = if null $ languageNoms $ inputLanguage branch
               then 0
               else 1 + (maximum $ map unpackNomSymbol $ languageNoms $ inputLanguage branch)
       prefixAndPropCouples = prefixAndProps branch
       es = Set.union
             (Set.fromList
               [NNF.At
                (NomSymbol ((urfatherOrPrefixZero branch n) + bias))
                (NNF.Nom n) | n <- (languageNoms $ inputLanguage branch)]
             )
             (Set.fromList
               [NNF.At
                (NomSymbol (p + bias))
                (NNF.Nom (NomSymbol (p + bias))) | p <- (prefixes branch),
                                                     isInclusionUrfather branch p]
             )
       ps = Set.fromList
             [NNF.At
               (NomSymbol (pre+bias))
               (NNF.Prop pro) | (pre_,pro) <- prefixAndPropCouples,
                                let pre = getInclusionUrfather branch pre_]
       rs = Set.fromList $ map accToNNF
              $ concatMap (\((p1,rel),bp_ps) -> map (\(_,p2) -> (p1 + bias, rel, (getInclusionUrfather branch p2) + bias))
                                                    bp_ps)
                          (filter (isInclusionUrfather branch . fst . fst) $ flattenDMap $ accStr branch)

flattenDMap :: Map.Map a (Map.Map b c) -> [((a,b),c)]
flattenDMap m
 = let ambcs = Map.assocs m  in --  [(a,Map.Map b c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (Map.assocs innerM_  {- [(b,c)] -} )) ambcs

accToNNF :: (Prefix,Rel,Prefix)
             -> NNF.Formula NomSymbol PropSymbol RelSymbol StateVar (NNF.At NNF.Nom (NNF.Diam NNF.Nom))
accToNNF (p1,r,p2) =
  NNF.At (NomSymbol p1) $ NNF.Diam (RelSymbol r) $ NNF.Nom (NomSymbol p2)

urfatherOrPrefixZero :: Branch -> NomSymbol -> Prefix
urfatherOrPrefixZero br (NomSymbol n) =
  if DS.isRoot (DS.Nominal n) (nomPrefClasses br)
   then 0
   else let (DS.Prefix p,_) = DS.find (DS.Nominal n) (nomPrefClasses br)
         in p

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

