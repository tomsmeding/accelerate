{-# LANGUAGE CPP #-}
module Data.Array.Accelerate.Trafo.AD.Debug where

#undef DEBUG

#ifdef DEBUG
import qualified Debug.Trace as Trace
import Data.Array.Accelerate.Trafo.AD.Config
#endif


trace :: String -> a -> a
#ifdef DEBUG
trace s = if getConfigVar Debug then Trace.trace s else id
#else
trace _ = id
#endif

traceM :: Monad m => String -> m ()
#ifdef DEBUG
traceM = if getConfigVar Debug then Trace.traceM else const (return ())
#else
traceM _ = return ()
#endif
