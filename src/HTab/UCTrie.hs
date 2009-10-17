module HTab.UCTrie
(UCTrie,
 update, empty, query,testSuite)
where

import Data.List ( intersect )
import Data.Maybe ( isJust )
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import Data.Set ( Set )
import qualified Data.Set as Set

data UCTrie = UCTrie (IntMap (Maybe UCTrie))

instance Show UCTrie where
 show (UCTrie uct) = foldr (\(k,v) acc -> case v of
                                           Nothing -> acc ++ " " ++ show k
                                           Just t2 -> acc ++ " " ++ show k ++ " -> (" ++ show t2 ++")" )
                           "" (IntMap.toList uct)

-- This structure is designed to store UNSAT cache information
-- Its only operations are update (= insert) and query
--
-- query returns True when a set stored in UCTrie is subset
-- if a given set
--
-- insert just inserts sets, but in certain cases, does not insert
-- supersets of sets already present (if the ordered list representing the
-- already present set is the prefix if the ordered list representing the
-- new set). This optimisation works because we know we only look for
-- subset querying


-- UCTrie stores sets as a prefix tree
-- Each branch is a set.
-- Updating (=inserting a set) the tree involves adding a branch, and if that branch
-- is a proper prefix of another, the other branch is shortened, since the leaf of
-- the new branch is on the old branch

type Idx = Int

empty :: UCTrie
empty = UCTrie IntMap.empty

update :: Set Idx -> UCTrie -> UCTrie
update idxs uctrie
 = go uctrie l
 where  l = Set.toList idxs
        go _ [] = error "UCTrie.update"
        go (UCTrie trie) [el]
         = UCTrie $ IntMap.insert el Nothing trie
        go unchanged@(UCTrie trie) (hd:tl)
         = case IntMap.lookup hd trie of
              Nothing  -> UCTrie $ IntMap.insert hd (Just $ go empty tl) trie
              Just mTr2 ->
               case mTr2 of
                Nothing  -> unchanged -- no need to insert a bigger set
                Just tr2 -> UCTrie $ IntMap.insert hd (Just $ go tr2 tl) trie


query :: Set Idx -> UCTrie -> Maybe [Idx]
query idxs_ uctrie
 = go (Just uctrie) (Set.toList idxs_) []
 where go Nothing  _  subset = Just subset -- success
       go _        []  _     = Nothing
       go (Just (UCTrie trie)) idxs subset
        = case ( filter isJust $ map (\el -> go (trie IntMap.! el) (dropWhile (<=el) idxs) (el:subset) )
                                     ( keys `intersect` idxs ) ) of
             (Just sol:_) -> Just sol
             _            -> Nothing
           where keys = IntMap.keys trie

--

testSuite :: Bool
testSuite = let
                toAdd = [ [1,2,6,8] , [3,4,7,9], [1,3,6,8], [1, 10], [5,9,40], [42] ] -- those to insert, and who succeed on query
                notToAdd = [ [1,2,3],  [3,9,10]]-- those who fail on query
                toTry =[[1,2,3,6,8], [1,10,12],  [42,43], [3,42]] -- those who succeed on query
                filledTrie = foldr (\l t -> update (Set.fromList l) t) empty toAdd
                succeeds trie list = isJust $ query (Set.fromList list) trie
            in
                   all (succeeds filledTrie) toAdd
                && all (not . (succeeds filledTrie)) notToAdd
                && all (succeeds filledTrie) toTry

