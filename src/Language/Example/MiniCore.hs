{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving,
  DataKinds, TypeFamilies, PatternSynonyms, PolyKinds, EmptyDataDecls,
  ViewPatterns
  #-}
module Language.Example.MiniCore where

import Control.Lens.Fold (anyOf)
import Control.Monad (unless, when)
import Data.Traversable
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Data.Foldable (for_)
import qualified Data.List

import Names

import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Whnf
import Language.Example.MiniCore.Errors
import Language.Example.MiniCore.Context
import Language.Example.MiniCore.Equiv
import Language.Example.MiniCore.EquivKind

inferCoreType :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Expr -> m Type
inferCoreType (VarE x) = lookupVar x
inferCoreType (LamE bnd) = do
  ((x, unembed -> τ), e) <- unbind bnd
  τ' <- extendVarCtx x τ $ inferCoreType e
  return $ τ `ArrT` τ'
inferCoreType (AppE e₁ e₂) = do
  τ_ <- inferCoreType e₁
  τN <- whnf τ_ TypeK
  case τN of
    ArrWhnf τparam τres -> do
      τarg <- inferCoreType e₂
      ensureEquivTy τparam τarg TypeK
      return τres
    _ -> raiseExpectedFn e₁
inferCoreType (TupleE elems) = do
  lτs <- for elems $ \(lbl, e) -> do
    τ <- inferCoreType e
    return (lbl, τ)
  return $ ProdT lτs
inferCoreType (ProjE e l) = do
  τ_ <- inferCoreType e
  tN <- whnf τ_ TypeK
  case tN of
    ProdWhnf lτs -> do
      case Data.List.lookup l lτs of
        Just τ -> return τ
        Nothing -> raiseUnknownFieldProj lτs l
    _ -> raiseExpectedProduct e
inferCoreType (TLamE bnd) = do
  ((α, unembed -> κ), e) <- unbind bnd
  extendTyVarCtx α κ $ do
    τ <- inferCoreType e
    return (ForallT $ bind (α, embed κ) τ)
inferCoreType (TAppE e τ) = do
  τ₀ <- inferCoreType e
  τN <- whnf τ₀ TypeK
  case τN of
    ForallWhnf bnd -> do
      ((α, unembed -> κ), τ₁) <- unbind bnd
      ensureCoreKind τ κ
      return (subst α τ τ₁)
    _ -> raiseExpectedForall e
inferCoreType (PackE τ e s_) = do
  ensureTypeK s_
  sN <- whnf s_ TypeK
  case sN of
    ExistWhnf bnd -> do
      ((α, unembed -> κ), τ') <- unbind bnd
      ensureCoreKind τ κ
      let τexp = subst α τ τ'
      τact <- inferCoreType e
      ensureEquivTy τexp τact TypeK
      return s_
    _ -> raiseExpectedSigma e
inferCoreType (LetPackE bnd) = do
  ((α, x, unembed -> e₀), e₁) <- unbind bnd
  τ₀ <- inferCoreType e₀
  τN <- whnf τ₀ TypeK
  (κ, τ₁) <- case τN of
               ExistWhnf bnd -> do
                 ((β, unembed -> κ), τ₁) <- unbind bnd
                 return (κ, subst β (VarT α) τ₁)
               _ -> raiseExpectedSigma e₀
  (extendTyVarCtx α κ . extendVarCtx x τ₁) $ do
    τ₂ <- inferCoreType e₁
    when (anyOf fv (== α) τ₂) $ raiseTyVarOccursInType α τ₂
    return τ₂
inferCoreType (LetE bnd) = do
  ((x, unembed -> e₁), e₂) <- unbind bnd
  τ <- inferCoreType e₁
  extendVarCtx x τ $ inferCoreType e₂

ensureTypeK :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m ()
ensureTypeK = flip ensureCoreKind TypeK

ensureCoreKind :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> Kind -> m ()
ensureCoreKind τ κ₀ = do
  κ' <- inferCoreKind τ
  unless (κ₀ == κ') $ raiseExpectedEqK κ₀ κ'


inferCoreKind :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m Kind
inferCoreKind (VarT α) = lookupTyVar α
inferCoreKind (ArrT τ₁ τ₂) = do
  ensureTypeK τ₁
  ensureTypeK τ₂
  return TypeK
inferCoreKind (ProdT lτs) = do
  for_ lτs $ \(_lbl, τ) -> ensureTypeK τ
  return TypeK
inferCoreKind (AppT τ₁ τ₂) = do
  κ <- inferCoreKind τ₁
  case κ of
    ArrK κ₁ κ₂ -> do
      κ₁' <- inferCoreKind τ₂
      ensureEquivKind κ₁ κ₁'
      return κ₂
    TypeK -> raiseExpectedFnKind τ₁
inferCoreKind (ForallT bnd) = do
  ((α, unembed -> κ), τ) <- unbind bnd
  extendTyVarCtx α κ $ ensureTypeK τ
  return TypeK
inferCoreKind (ExistT bnd) = do
  ((α, unembed -> κ), τ) <- unbind bnd
  extendTyVarCtx α κ $ ensureTypeK τ
  return TypeK

    
