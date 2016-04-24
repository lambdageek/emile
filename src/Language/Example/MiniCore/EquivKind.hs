module Language.Example.MiniCore.EquivKind where

import Control.Monad.Except

import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Errors

ensureEquivKind :: MonadError CoreErr m => Kind -> Kind -> m ()
ensureEquivKind κ₁ κ₂ | κ₁ == κ₂ = return ()
                      | otherwise = raiseExpectedEqK κ₁ κ₂
