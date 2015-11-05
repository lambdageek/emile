module Language.SIL.Embed where

import Language.CoreLang
import Language.SIL.Syntax

class Monad m => MonadEmbed m where

embedΣ :: MonadEmbed m => Σ lang -> m (CoreType lang)
embedΣ = undefined
