{-# language ViewPatterns #-}
module Language.Example.MiniCore.Equiv where

import Control.Monad.Except
import Control.Monad.Reader

import Names

import Language.Common.Label

import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Errors
import Language.Example.MiniCore.Context
import Language.Example.MiniCore.Whnf
import Language.Example.MiniCore.EquivKind

equivLabeledTypes :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => m () -> (Label, Type) -> (Label, Type) -> m ()
equivLabeledTypes onFail (l, t) (l', t') | l == l' = ensureEquivTy t t' TypeK
                                         | otherwise = onFail

ensureEquivTy :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> Type -> Kind -> m ()
ensureEquivTy τ0 σ0 κ = do
  τN <- whnf τ0 κ
  σN <- whnf σ0 κ
  ensureEquivTyWhnf τN σN κ

ensureEquivTyWhnf :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => TypeWhnf -> TypeWhnf -> Kind -> m ()
ensureEquivTyWhnf τN σN κ = do
  case (τN, σN) of
    (ProdWhnf lτs, ProdWhnf lσs) | length lτs == length lσs -> do
                               let lτs' = canonicalizeLabelOrder lτs
                                   lσs' = canonicalizeLabelOrder lσs
                               zipWithM_ (equivLabeledTypes (raiseExpectedEqTy (lowerWhnf τN) (lowerWhnf σN))) lτs' lσs'
    -- (SumT lτs, SumT lσs) | length lτs == length lσs -> do
    --                          let lτs' = canonicalizeLabelOrder lτs
    --                              lσs' = canonicalizeLabelOrder lσs
    --                          zipWithM_ (equivLabeledTypes (raiseExpectedEqTy τ σ)) lτs' lσs'
    (ForallWhnf bnd₁, ForallWhnf bnd₂) -> do
      Just ((α, unembed -> κ₁), τbody, (_, unembed -> κ₂), σbody) <- unbind2 bnd₁ bnd₂
      ensureEquivKind κ₁ κ₂
      extendTyVarCtx α κ₁ $ ensureEquivTy τbody σbody TypeK
    (ExistWhnf bnd₁, ExistWhnf bnd₂) -> do
      Just ((α, unembed -> κ₁), τbody, (_, unembed -> κ₂), σbody) <- unbind2 bnd₁ bnd₂
      ensureEquivKind κ₁ κ₂
      extendTyVarCtx α κ₁ $ ensureEquivTy τbody σbody TypeK
    (NeutralWhnf τR, NeutralWhnf σR) -> do
      κout <- ensureEquivNeutral τR σR
      ensureEquivKind κ κout
    _ -> error "unimplemented ensureEquivTy"  -- but really, we fail now

ensureEquivNeutral :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => TypeR -> TypeR -> m Kind
ensureEquivNeutral τR σR =
  case (τR, σR) of
    (VarR α, VarR β) | α == β -> lookupTyVar α
    (AppR τR τN, AppR σR σN) -> do
      κ <- ensureEquivNeutral τR σR
      (κdom, κcod) <- case κ of
        ArrK κdom κcod -> return (κdom, κcod)
        TypeK -> raiseExpectedFnKind (lowerNeutral τR)
      ensureEquivTyWhnf τN σN κdom
      return κcod
    _ -> error "not equivalent neutrals"
  
