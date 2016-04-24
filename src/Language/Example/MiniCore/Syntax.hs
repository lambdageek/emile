{-# language DeriveDataTypeable, StandaloneDeriving, EmptyDataDecls,
             TypeFamilies
  #-}
module Language.Example.MiniCore.Syntax where

import Names

import Language.Common.Label
import Language.CoreLang

import {-# source #-} qualified Language.Example.MiniCore.Desugar as Desugar
import Language.SIL.Syntax (DesugarSIL(..))

data MiniSIL
  deriving (Typeable)

instance CoreLang MiniSIL where
  data CoreKind MiniSIL =
    TypeK
    | ArrK Kind Kind -- κ₁ → κ₂
    deriving (Show, Generic, Eq)
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
    | ProjE Expr Label -- e.ℓ
    | TLamE (Bind (TyVar, Embed Kind) Expr)
    | TAppE Expr Type
      -- pack ⟨τ, e⟩ as σ where σ=∃α:κ.σ′
    | PackE Type Expr Type
      -- let pack ⟨α,x⟩ = e₁ in e₂
    | LetPackE (Bind (TyVar, Var, Embed Expr) Expr)
      -- XXX this bit is unmotivated...  I need it for nullary UnpackM
      -- in SIL which seems like it's missing a type annotation which
      -- would let me just desugar to a lambda and an application.
    | LetE (Bind (Var, Embed Expr) Expr)
    deriving (Show, Generic)

  injTyVar = VarT


type Kind = CoreKind MiniSIL

type Type = CoreType MiniSIL
type TyVar = Name Type

type Expr = CoreExpr MiniSIL
type Var = Name Expr

instance Alpha (CoreKind MiniSIL)
instance Alpha (CoreType MiniSIL)
instance Alpha (CoreExpr MiniSIL)

instance Subst (CoreType MiniSIL) (CoreKind MiniSIL)

instance Subst (CoreType MiniSIL) (CoreType MiniSIL) where
  isvar (VarT v) = Just (SubstName v)
  isvar _ = Nothing

instance DesugarSIL MiniSIL where
  desugarMod = Desugar.desugar
  
----------------------------------------------------------------------------
-- convenience constructors

-- letpack ⟨x⟩ = e₁ in e₂       ≙ let x = e₁ in e₂
-- letpack ⟨α,βs, x⟩ = e₁ in e₂ ≙ letpack ⟨α,y⟩ = e₁ in letpack ⟨βs,x⟩ = y in e₂
letpacks :: Fresh m => [TyVar] -> Var -> Expr -> Expr -> m Expr
letpacks [] x e₁ e₂ = return $ LetE $ bind (x, embed e₁) e₂
letpacks (α:βs) x e₁ e₂ = do
  y <- fresh (s2n "y")
  e₂' <- letpacks βs x (VarE y) e₂
  return $ LetPackE $ bind (α, y, embed e₁) e₂'

-- pack ⟨e⟩ as t                 ≙ e
-- pack ⟨τ₁, τs, e⟩ as (∃α,βs.t) ≙ pack ⟨τ₁, pack ⟨τs, e⟩ as ∃βs.t[τ₁/α]⟩ as ∃α.∃βs.t
-- packs E T [(τs, ακs)] = pack ⟨τs, e⟩> as (∃αs. T)
packs :: Expr -> Type -> [(Type, (TyVar, Embed Kind))] -> Expr
packs e _t [] = e
packs e t ((τ, ακ@(α,_κ)):τβκs) =
  let e' = packs e (subst α τ t) τβκs
      βks = map snd τβκs
      t' = existss βks t
  in PackE τ e' (ExistT $ bind ακ t')

foralls :: [(TyVar, Embed Kind)] -> Type -> Type
foralls [] = id
foralls (tvb:tvbs) = ForallT . bind tvb . foralls tvbs

existss :: [(TyVar, Embed Kind)] -> Type -> Type
existss [] = id
existss (tvb:tvbs) = ExistT . bind tvb . existss tvbs

projects :: Expr -> [Label] -> Expr
projects e [] = e
projects e (l:ls) = projects (ProjE e l) ls

tlams :: [(TyVar, Embed Kind)] -> Expr -> Expr
tlams [] = id
tlams (ακ:ακs) = TLamE . bind ακ . tlams ακs

tapps :: Expr -> [Type] -> Expr
tapps e [] = e
tapps e (τ:τs) = tapps (TAppE e τ) τs

