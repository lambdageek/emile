module Language.Example.MiniCore.Desugar where

import Names (Fresh)
import Language.SIL.Syntax (MapNameMonad, Mod)
import {-# source #-} Language.Example.MiniCore.Syntax


desugar :: (MapNameMonad m MiniSIL, Fresh m) => Mod MiniSIL -> m Expr