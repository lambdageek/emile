module Language.Example.MiniCore.Desugar where

import Control.Monad (when)

import Names

import Language.Common.Label
import Language.SIL.Syntax (MapNameMonad(..), Mod(..), PackMod(..), IdM,
                            Σ(..), Ξ(..), SubsigCoercion(..),
                            DesugarSIL(..) )

import Language.CoreLang
import {-# source #-} Language.Example.MiniCore.Syntax

desugar :: (MapNameMonad m MiniSIL, Fresh m) => Mod MiniSIL -> m Expr
desugar (VarM v) = VarE <$> lookupIdM v
desugar (ValM e) = pure $ TupleE [(ValueLabel, e)]
desugar (TyM τ κ) = do
  e <- polyReflE τ κ
  return $ TupleE [(TypeLabel, e)]
desugar (SigM ξ) = do
  τ <- desugarXi ξ
  e <- polyReflE τ TypeK
  return $ TupleE [(SignatureLabel, e)]
desugar (RecordM lms) =
  TupleE <$> traverse desugarLabeledMods lms
desugar (ProjM m ls) =
  flip projects ls <$> desugar m
desugar (LamM bnd) =
  desugarLamModExpr bnd
desugar (AppM mf τs mx) =
  AppE <$> (tapps <$> desugar mf <*> pure τs) <*> desugar mx
desugar (CoerM coer m) =
  AppE <$> desugarCoercion coer <*> desugar m
desugar (PackM packmod) = desugarPackMod packmod
desugar (UnpackM bnd) =
  desugarUnpackModExpr bnd

desugarSigma :: (Fresh m) => Σ MiniSIL -> m Type
desugarSigma (ValΣ τ) =
  -- [$val : τ]
  pure $ ProdT [(ValueLabel, τ)]
desugarSigma (TyΣ τ κ) = do
  encodeType <$> polyEqT τ κ
  where
    encodeType t = ProdT [(TypeLabel, t)]
desugarSigma (SigΣ ξ) = do
  τ <- desugarXi ξ
  encodeSig <$> polyEqT τ TypeK
  where
    encodeSig t = ProdT [(SignatureLabel, t)]
desugarSigma (RecordΣ lss) =
  ProdT <$> traverse desugarLabeledSigma lss
  where
    desugarLabeledSigma (label, σ) = (,) <$> pure label <*> desugarSigma σ
desugarSigma (FunΣ bnd) = do
  (tvbs, (σ, ξ)) <- unbind bnd
  -- ∀ αs:κs . ↓σ → ↓ξ
  foralls tvbs <$> (ArrT <$> desugarSigma σ <*> desugarXi ξ)

desugarXi :: (Fresh m) => Ξ MiniSIL -> m Type
desugarXi (Ξ bnd) = do
  (tvbs, σ) <- unbind bnd
  existss tvbs <$> desugarSigma σ

-- polyEqT τ κ = ∀ α:(κ→⋆). α τ → α τ
polyEqT :: Fresh m => Type -> Kind -> m Type
polyEqT τ κ = do
  α <- fresh (s2n "α")
  let t = AppT (VarT α) τ
      k = κ `ArrK` TypeK
  return $ ForallT $ bind (α, embed k) $ t `ArrT` t

-- polyReflE τ κ = Λ α :(κ→⋆). λx:(α τ). x
polyReflE :: Fresh m => Type -> Kind -> m Expr
polyReflE τ κ = do
  α <- fresh (s2n "α")
  x <- fresh (s2n "x")
  let k = κ `ArrK` TypeK
      t = AppT (VarT α) τ
      f = LamE $ bind (x, embed t) $ VarE x
  return $ TLamE $ bind (α, embed k) f

desugarLabeledMods :: (MapNameMonad m lang, DesugarSIL lang, Fresh m) => (Label, Mod lang) -> m (Label, CoreExpr lang)
desugarLabeledMods (label, m) = (,) <$> pure label <*> desugarMod m

desugarCoercion :: Fresh m => SubsigCoercion MiniSIL -> m Expr
desugarCoercion (IdCo σ) = do
  τ <- desugarSigma σ
  x <- fresh (s2n "x")
  -- λ x : τ . x
  return $ LamE $ bind (x, embed τ) $ VarE x

desugarLamModExpr :: (MapNameMonad m MiniSIL, Fresh m)
                    => Bind (Rebind [(TyVar, Embed Kind)] (IdM MiniSIL, Embed (Σ MiniSIL))) (PackMod MiniSIL)
                    -> m Expr
desugarLamModExpr bnd = do
  (rbnd, pack) <- unbind bnd
  let (ακs, (x, Embed σ)) = unrebind rbnd
  τ <- desugarSigma σ
  -- Λ αs:κs . λ x′:σ . pack
  l <- extendIdM x $ \y -> do
    pack' <- desugarPackMod pack
    pure $ LamE $ bind (y, Embed τ) pack'
  return $ tlams ακs l

desugarUnpackModExpr :: (MapNameMonad m MiniSIL, Fresh m)
                       => Bind ([TyVar], IdM MiniSIL, Embed (Mod MiniSIL)) (Mod MiniSIL)
                       -> m Expr
desugarUnpackModExpr bnd = do
  ((αs, x, Embed m1), m2) <- unbind bnd
  e1 <- desugarMod m1
  (y, e2) <- extendIdM x $ \y -> do
    e2 <- desugarMod m2
    return (y, e2)
  letpacks αs y e1 e2

desugarPackMod :: (MapNameMonad m MiniSIL, Fresh m)
                 => PackMod MiniSIL -> m Expr
desugarPackMod (PackMod τs m (Ξ bnd)) = do
  (ακs, σ) <- unbind bnd
  τ₀ <- desugarSigma σ
  e <- desugarMod m
  when (length ακs /= length τs) $ error "internal error - malformed PackMod"
  return $ packs e τ₀ (zip τs ακs) 


