{-# OPTIONS_GHC -fglasgow-exts #-}
----------------------------------------------------
--                                                --
-- Statistics.hs:                                 --
-- Functions that collect and print out           --
-- statistics                                     --
--                                                --
----------------------------------------------------

{-
Copyright (C) HyLoRes 2002-2006
Carlos Areces     - areces@loria.fr      - http://www.loria.fr/~areces
Daniel Gorin      - dgorin@dc.uba.ar
Juan Heguiabehere - juanh@inf.unibz.it - http://www.inf.unibz.it/~juanh/

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
USA.
-}

module HTab.Statistics
(   Statistics, StatisticsState, StatisticsStateIO,
    recordFiredRule, recordClosedBranch,

    printOutAllMetrics, printOutAllMetrics', printOutInspectionMetrics,

    initialStatisticsStateFor,
    addMetric, addInspectionMetric, setPrintOutInterval,

    Metric,
    ruleApplicationCount, closedBranches,
    updateStep

) where

import Control.Monad.State(MonadState , MonadIO, modify, unless,
                           get, gets, guard, when)

import qualified Control.Monad.State as State(liftIO)

import Data.Map(Map)
import qualified Data.Map as Map(insertWith, toList, empty)

import HTab.Base (separate)
import HTab.RuleMetadata(RuleId(..))


-------------------------------------------
-- Statistics are collections of Metrics
-- which can be printed out (at regular intervals)
-------------------------------------------
data Statistics = Stat{metrics::[Metric],
                       inspectionMetrics::[Metric],
                       count::Int,
                       step::Maybe Int}

type StatisticsState a   = forall m. (MonadState Statistics m) => m a
type StatisticsStateIO a = forall m. (MonadState Statistics m, MonadIO m) => m a

updateMetrics :: (Metric -> Metric) -> Statistics -> Statistics
updateMetrics f stat = stat{metrics           = map (f $!) (metrics stat),
                            inspectionMetrics = map (f $!) (inspectionMetrics stat)}

updateStep :: Statistics -> Statistics
updateStep s@(Stat _ [] _     _)         = s
updateStep s@(Stat _ _  _     Nothing)   = s
updateStep stat                          = stat{count = count stat + 1}

needsToPrintOut :: Statistics -> Bool
needsToPrintOut (Stat _ [] _     _)         = False
needsToPrintOut (Stat _ _  _     Nothing)   = False
needsToPrintOut (Stat _ _  iter (Just toi)) = iter > 0 && iter `mod` toi == 0

noStats :: Statistics -> Bool
noStats (Stat [] [] _ _) = True
noStats  _               = False

emptyStats :: Statistics
emptyStats = Stat{metrics=[],
                  inspectionMetrics=[],
                  count=0,
                  step=Nothing}

--------------------------- Monadic Statistics functions follow ------------------------------


initialStatisticsStateFor :: (MonadState Statistics m) => (m a -> Statistics -> b) -> m a -> b
initialStatisticsStateFor f = flip f emptyStats

{- addMetric: - Adds a metric at the end of the list (thus,
   metrics are printed out in the order in which they were added -}
addMetric :: Metric -> StatisticsState ()
addMetric newMetric  = modify (\stat -> stat{metrics = metrics stat ++[newMetric]})

{- addInspectionMetric: - Adds a metric that will be printed out
   at regular intervals -}
addInspectionMetric :: Metric -> StatisticsState ()
addInspectionMetric newMetric = modify (\stat -> stat{inspectionMetrics = inspectionMetrics stat ++[newMetric]})

setPrintOutInterval :: Int -> StatisticsState ()
setPrintOutInterval i = modify $ \s -> s{step = guard (i > 0) >> return i}

recordFiredRule :: RuleId -> StatisticsState ()
recordFiredRule rule = modify (updateMetrics $ recordFiredRuleM rule)

recordClosedBranch :: StatisticsState ()
recordClosedBranch = modify (updateMetrics recordClosedBranchM)

printOutAllMetrics :: StatisticsStateIO ()
printOutAllMetrics = get >>= (liftIO . printOutAllMetrics')

printOutAllMetrics' :: Statistics -> IO ()
printOutAllMetrics' stats =
        unless (noStats stats) $ do
            liftIO $ putStrLn "(final statistics)"
            liftIO $ printOutList (inspectionMetrics stats ++ metrics stats)

printOutInspectionMetrics :: StatisticsStateIO ()
printOutInspectionMetrics = do  shouldPrint <- gets needsToPrintOut
                                when shouldPrint  $ do
                                    liftIO $ putStr "(partial statistics: iteration "
                                    iter <- gets count
                                    liftIO . putStr . show $ iter
                                    liftIO $ putStrLn ")"
                                    ims <- gets inspectionMetrics
                                    liftIO $ printOutList ims


printOutList :: Show a => [a] -> IO ()
printOutList ms = unless ( null ms ) $ do
                          let separator = "\n----------------------------------\n"
                          putStr "begin"
                          putStr separator
                          putStr (separate separator ms)
                          putStr separator
                          putStr "end\n"

--------------------------------------------
-- Metrics
--------------------------------------------
data Metric = RC  (Map RuleId Int) -- Rule application count
             |CB  !Int             -- Number of closed branched

type MetricModificator = Metric -> Metric

instance Show Metric where
  show (CB  x)   = "Closed branches: " ++ show x
  show (RC  x)   = "Rule applications:" ++ concatMap p (Map.toList x)
      where p (i,c) = "\n  " ++ show i ++ " rule: " ++ show c


recordFiredRuleM :: RuleId -> MetricModificator
recordFiredRuleM rule (RC m) = RC (Map.insertWith (+) rule 1 m)
recordFiredRuleM _    m      = m


recordClosedBranchM :: MetricModificator
recordClosedBranchM (CB x) = CB (x+1)
recordClosedBranchM m      = m

ruleApplicationCount :: Metric
ruleApplicationCount = RC  Map.empty

closedBranches :: Metric
closedBranches = CB 0

--

liftIO :: (MonadIO m) => IO a -> m a
liftIO = State.liftIO
