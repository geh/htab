module HTab.Literals (
UpdateResult(..), Literals,
SlotUpdateResult(..), LiteralSlot,
updateMap, lsUnions, lsAddDeps, lsQuery,
positiveNom
) where

import Data.IntMap ( IntMap)
import qualified Data.IntMap as I
import Data.Map ( Map)
import qualified Data.Map as M

import Data.List(minimumBy)
import Data.Ord ( comparing )

import HTab.Formula

type Literals           = IntMap {- Prefix -} (Map Literal DependencySet)

{- functions for literals associated to prefixes -}

data UpdateResult = UpdateSuccess Literals | UpdateFailure DependencySet

-- Insert a literal into a literal slot

updateMap :: Literals -> Prefix -> DependencySet -> Literal -> UpdateResult
updateMap ls  _  _  (PosLit Taut) = UpdateSuccess ls
updateMap _   _  ds (NegLit Taut) = UpdateFailure ds
updateMap ls pre ds l
  = case I.lookup pre ls of
     Nothing   -> UpdateSuccess $ I.insert pre (M.singleton l ds) ls
     Just slot ->
       case lsUpdate slot l ds of
        SlotUpdateSuccess updatedSlot -> UpdateSuccess $ I.insert pre updatedSlot ls
        SlotUpdateFailure failureDeps -> UpdateFailure failureDeps


type LiteralSlot = Map Literal DependencySet
data SlotUpdateResult =   SlotUpdateSuccess LiteralSlot
                        | SlotUpdateFailure DependencySet


-- Union a list of literals slots
lsUnions :: [LiteralSlot] -> SlotUpdateResult
lsUnions []              = SlotUpdateSuccess M.empty
lsUnions [ls]            = SlotUpdateSuccess ls
lsUnions (ls1:ls2:tl)
 = case lsUnion ls1 ls2 of
     failure@(SlotUpdateFailure _) -> failure
     SlotUpdateSuccess newLs       -> lsUnions (newLs:tl)

-- Union two literals slots

-- if there is a clash, the result reports the set of dependencies whose
-- earliest dependency is the earliest among all dep. sets that caused the clash
lsUnion :: LiteralSlot -> LiteralSlot -> SlotUpdateResult
lsUnion ls1 ls2
 = uls_helper ls1 (M.assocs ls2)
    where uls_helper :: LiteralSlot -> [(Literal,DependencySet)]
                           -> SlotUpdateResult
          uls_helper ls l_ds_s =
           let (updateStatus,clashing_ds_s)
                = foldr
                   (\(l,ds) (upResult,clashingBps_s)
                    -> case upResult of
                        SlotUpdateSuccess ls_  -> (lsUpdate ls_ l ds,      clashingBps_s)
                        SlotUpdateFailure ds_s -> (lsUpdate ls  l ds, ds_s:clashingBps_s)
                           -- we reuse the input LiteralSlot
                   )
                   (SlotUpdateSuccess ls,[])   l_ds_s
           in
            case clashing_ds_s of
              []   -> updateStatus      -- is 'success'
              ds_s -> SlotUpdateFailure $ findEarliestSet ds_s
                       where findEarliestSet = minimumBy compareBPSets
                             compareBPSets ds1 ds2 = comparing dsMin ds1 ds2


-- Insert a piece of information in a literal slot

lsUpdate :: LiteralSlot -> Literal -> DependencySet -> SlotUpdateResult
lsUpdate ls (PosLit Taut) _  = SlotUpdateSuccess ls
lsUpdate _  (NegLit Taut) ds = SlotUpdateFailure ds
lsUpdate ls l ds  -- nominals, propositional symbols
 = case M.lookup (negLit l) ls of
    Just ds2 -> SlotUpdateFailure $ dsUnion ds ds2
    Nothing  -> SlotUpdateSuccess $ M.insertWith mergeDeps l ds ls
                 where mergeDeps d1 d2  = if dsMin d1 < dsMin d2 then d1 else d2
                  -- if the same information is caused by an earlier
                  -- branching, only keep the information of the earliest
                  -- set of dependencies

-- Other functions related to literals slots

lsAddDeps :: DependencySet -> SlotUpdateResult -> SlotUpdateResult
lsAddDeps ds res_ls =
 case res_ls of
  SlotUpdateSuccess ls -> SlotUpdateSuccess $ M.map (dsUnion ds) ls
  failure              -> failure

lsQuery :: Literals -> Prefix -> Literal -> Maybe (Bool,DependencySet)
-- Output : Nothing    = nevermind
--          Just True  = already there
--          Just False = contrary there
lsQuery _ _ (PosLit Taut) = Just (True,dsEmpty)
lsQuery _ _ (NegLit Taut) = Just (False,dsEmpty)
lsQuery lits pr l
  = case dlookup pr l lits of
      Just ds    -> Just (True,ds)
      Nothing    -> case dlookup pr (negLit l) lits of
                      Just ds -> Just (False,ds)
                      Nothing -> Nothing

   where dlookup pr_ l_ lits_ = do slot <- I.lookup pr_ lits_
                                   M.lookup l_ slot

positiveNom :: Literals -> Prefix -> Maybe String
positiveNom lits pr = do slot <- I.lookup pr lits
                         case filter isPositiveNom (M.keys slot) of
                           (PosLit (N n):_) -> Just n
                           _                -> Nothing

