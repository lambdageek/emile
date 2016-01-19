{-# LANGUAGE DeriveDataTypeable, DataKinds, TypeFamilies, PatternSynonyms #-}
module Language.Example.MiniCore where

import Control.Applicative (Applicative(..), (<$>))
import Data.Traversable

import Names

import Language.CoreLang
import Language.SIL.Syntax (CoreSIL(..), Σ(..), Ξ(..), Mod(..), Label(..))

data Mini = MiniSIL
  deriving (Typeable)

instance CoreLang MiniSIL where
  data CoreKind MiniSIL =
    TypeK
    | ArrK Kind Kind -- κ₁ → κ₂
    deriving (Show, Generic)
  data CoreType MiniSIL =
    VarT TyVar
    | ArrT Type Type
    | ProdT [(Label, Type)]
    | AppT Type Type
    | ForallT (Bind (TyVar, Embed Kind) Type)
    | ExistT (Bind (TyVar, Embed Kind) Type)
    deriving (Show, Generic)
  data CoreExpr MiniSIL =
    VarE Var
    | LamE (Bind (Var, Embed Type) Expr)
    | AppE Expr Expr
    | TupleE [(Label, Expr)]
    | ProjE Label Expr
    | TLamE (Bind (TyVar, Embed Kind) Expr)
    | TAppE Expr Type
      -- pack ⟨τ, e⟩ as σ where σ=∃α:κ.σ′
    | PackE Type Expr Type
      -- let pack ⟨α,x⟩ = e₁ in e₂
    | LetPackE (Bind (TyVar, Var, Embed Expr) Expr)
    deriving (Show, Generic)

  injTyVar = VarT

instance CoreSIL MiniSIL where
  injProjModExpr = error "unimplemented injProjModExpr" --  ProjModE
  -- projProjModExpr (ProjModE mod) = Just mod
  projProjModExpr _ = Nothing

injSigma :: (Fresh m, Applicative m) => Σ MiniSIL -> m Type
injSigma (ValΣ τ) =
  -- [$val : τ]
  pure $ ProdT [(ValueLabel, τ)]
injSigma (TyΣ τ κ) = do
  α <- fresh (s2n "α")
  let t = AppT (VarT α) τ
      k = κ `ArrK` TypeK
  -- [$type : ∀ α:(κ→⋆). α τ → α τ]
  return $ ProdT [(TypeLabel, ForallT (bind (α, embed k) $ t `ArrT` t))]
injSigma (SigΣ ξ) = 
  encodeSig <$> injXi ξ
  where
    encodeSig τ = ProdT [(SignatureLabel, τ)]
injSigma (RecordΣ lss) =
  ProdT <$> traverse injLabeledSigma lss
  where
    injLabeledSigma (label, σ) = (,) <$> pure label <*> injSigma σ
injSigma (FunΣ bnd) = do
  (tvbs, (σ, ξ)) <- unbind bnd
  -- ∀ αs:κs . ↓σ → ↓ξ
  foralls tvbs <$> (ArrT <$> injSigma σ <*> injXi ξ)

foralls :: [(TyVar, Embed Kind)] -> Type -> Type
foralls [] = id
foralls (tvb:tvbs) = ForallT . bind tvb . foralls tvbs

existss :: [(TyVar, Embed Kind)] -> Type -> Type
existss [] = id
existss (tvb:tvbs) = ExistT . bind tvb . existss tvbs

injXi :: (Fresh m, Applicative m) => Ξ MiniSIL -> m Type
injXi (Ξ bnd) = do
  (tvbs, σ) <- unbind bnd
  existss tvbs <$> injSigma σ

-- pattern ValueLabel :: Label
pattern ValueLabel = Label "$val"

-- pattern TypeLabel :: Label
pattern TypeLabel = Label "$type"

-- pattern SignatureLabel :: Label
pattern SignatureLabel = Label "$kind"

type Kind = CoreKind MiniSIL

type Type = CoreType MiniSIL
type TyVar = Name Type

type Expr = CoreExpr MiniSIL
type Var = Name Expr

instance Alpha (CoreKind MiniSIL)
instance Alpha (CoreType MiniSIL)
