module Language.Example.MiniCore.Whnf where

import Control.Monad.Except
import Control.Monad.Reader

import Names

import Language.Common.Label
import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Errors
import Language.Example.MiniCore.Context
import Language.Example.MiniCore.EquivKind

-- | Types in Weak Head Normal Form
data TypeWhnf =
  NeutralWhnf TypeR
  | ArrWhnf Type Type
  | ProdWhnf [(Label, Type)]
  | ForallWhnf (Bind (TyVar, Embed Kind) Type)
  | ExistWhnf (Bind (TyVar, Embed Kind) Type)
  deriving (Show, Generic)

-- | Neutral types
data TypeR =
  VarR TyVar
  | AppR TypeR TypeWhnf
  deriving (Show, Generic)

instance Alpha TypeWhnf
instance Alpha TypeR

------------------------------------------------------------------------------
-- Normalized types embed into ordinary types

lowerWhnf :: TypeWhnf -> Type
lowerWhnf τN =
  case τN of
    NeutralWhnf τR -> lowerNeutral τR
    ArrWhnf τ₁ τ₂ -> ArrT τ₁ τ₂
    ProdWhnf lτs -> ProdT lτs
    ForallWhnf bnd -> ForallT bnd
    ExistWhnf bnd -> ExistT bnd

lowerNeutral :: TypeR -> Type
lowerNeutral τR =
  case τR of
    VarR α -> VarT α
    AppR τR τN -> AppT (lowerNeutral τR) (lowerWhnf τN)

------------------------------------------------------------------------------
-- (Weak Head) Normalization

whnf :: (MonadReader CoreCtx m, MonadError CoreErr m) => Type -> Kind -> m TypeWhnf
whnf τ (κ@ArrK {}) = do
  (τR, κ') <- whnfR τ
  ensureEquivKind κ κ'
  return (NeutralWhnf τR)
whnf τ TypeK =
  case τ of
    VarT α -> return (NeutralWhnf $ VarR α) -- TODO: ensure α has kind ⋆
    ArrT τ₁ τ₂ -> return (ArrWhnf τ₁ τ₂)
    ProdT lτs -> return (ProdWhnf lτs)
    ForallT bnd -> return (ForallWhnf bnd)
    ExistT bnd -> return (ExistWhnf bnd)
    AppT {} -> do
      (τR, κ) <- whnfR τ
      ensureEquivKind κ TypeK
      return (NeutralWhnf τR)

whnfR :: (MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m (TypeR, Kind)
whnfR τ =
  case τ of
    VarT α -> do
      κ <- lookupTyVar α
      return (VarR α, κ)
    AppT τ₁ τ₂ -> do
      (τR, κ) <- whnfR τ₁
      (κdom, κcod) <- case κ of
        ArrK κdom κcod -> return (κdom, κcod)
        TypeK -> raiseExpectedFnKind τ₁
      τN <- whnf τ₂ κdom
      return (AppR τR τN, κcod)
    _ -> error "not a neutral type in whnfR"
