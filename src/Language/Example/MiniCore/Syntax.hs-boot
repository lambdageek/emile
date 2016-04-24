{-# language TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
module Language.Example.MiniCore.Syntax where

import Language.CoreLang

data MiniSIL

instance CoreLang MiniSIL

type Expr = CoreExpr MiniSIL
