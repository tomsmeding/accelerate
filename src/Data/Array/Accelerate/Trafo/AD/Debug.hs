{-# LANGUAGE CPP #-}
module Data.Array.Accelerate.Trafo.AD.Debug where

#undef DEBUG

#ifdef DEBUG
import qualified Debug.Trace as Trace
#endif


trace :: String -> a -> a
#ifdef DEBUG
trace = Trace.trace
#else
trace _ = id
#endif

traceM :: Monad m => String -> m ()
#ifdef DEBUG
traceM = Trace.traceM
#else
traceM _ = return ()
#endif
