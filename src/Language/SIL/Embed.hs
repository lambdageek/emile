module Language.SIL.Embed where

import Names
import Language.CoreLang
import Language.SIL.Syntax

class (CoreLang lang, Monad m) => MonadEmbed lang m where
  -- atomic module types
  embedValΣ :: CoreType lang -> m (CoreType lang)
  embedTyΣ :: CoreType lang -> CoreKind lang -> m (CoreType lang)
  embedSigΣ :: TyVarBinds lang -> CoreType lang -> m (CoreType lang)
  -- building blocks for composite module types
  embedProduct :: (ModuleContent (CoreType lang)) -> m (CoreType lang)
  embedForalls :: TyVarBinds lang -> CoreType lang -> m (CoreType lang)
  embedArrow :: CoreType lang -> CoreType lang -> m (CoreType lang)
  embedExists :: TyVarBinds lang -> CoreType lang -> m (CoreType lang)

embedΣ :: (Typeable lang, Alpha (CoreType lang),
           Alpha (CoreKind lang),
           Fresh m, MonadEmbed lang m) => Σ lang -> m (CoreType lang)
embedΣ (ValΣ τ) = embedValΣ τ
embedΣ (TyΣ τ κ) = embedTyΣ τ κ
embedΣ (SigΣ ξ) = do
  (ακs, τ) <- embedΞ ξ
  embedSigΣ ακs τ
embedΣ (RecordΣ modContent) = do
  lτs <- traverse (traverse embedΣ) modContent
  embedProduct lτs
embedΣ (FunΣ bnd) = do
  (ακs, (σdom, ξcod)) <- unbind bnd
  τdom <- embedΣ σdom
  (βκs, τcod) <- embedΞ ξcod
  -- ∀ α:κ . τ → ∃ β:κ́ . τ́
  embedForalls ακs =<< embedArrow τdom =<< embedExists βκs τcod

embedΞ :: (Typeable lang, Alpha (CoreType lang),
           Alpha (CoreKind lang),
           Fresh m, MonadEmbed lang m) => Ξ lang -> m (TyVarBinds lang, CoreType lang)
embedΞ (Ξ bnd) = do
  (ακs, σ) <- unbind bnd
  τ <- embedΣ σ
  return (ακs, τ)
