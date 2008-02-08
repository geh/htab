module HTab.Timeout where

import Control.Exception
import Control.Concurrent
import Data.Dynamic(Typeable, typeOf, TyCon, mkTyCon, mkTyConApp, toDyn)
import Data.Unique
{- Timeout code -}

data TimeOut = TimeOut Unique

timeOutTc :: TyCon
timeOutTc = mkTyCon "TimeOut"

instance Typeable TimeOut where
    typeOf _ = mkTyConApp timeOutTc []


timeout :: Integer -> IO a -> IO a -> IO a
timeout secs action on_timeout =
    let {
     timeout_thread seconds parent i =
     do {
         threadDelay ((fromInteger seconds) * 1000000);
         throwTo parent (DynException (toDyn (TimeOut i)))
        }
    } in
   do {
       parent  <- myThreadId;
       i       <- newUnique;
       block (do
          timeoutThreadId <- forkIO (timeout_thread secs parent i);
          Control.Exception.catchDyn
            ( unblock (
                do {
                   result <- action;
                   killThread timeoutThreadId;
                   return result;
                   }
              )
            )
            ( \exception ->
                case exception of
                    TimeOut u | u == i -> unblock on_timeout
                    _ -> do {
                                killThread timeoutThreadId;
                                throwDyn exception
                                }
            )
         )
       }
