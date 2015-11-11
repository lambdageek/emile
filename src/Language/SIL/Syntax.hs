{-# LANGUAGE PolyKinds, TypeFamilies, GADTs, UndecidableInstances, ConstraintKinds #-}
module Language.SIL.Syntax where

import qualified Data.Coerce

import Names

import Language.CoreLang

-- Core SIL
class CoreLang lang => CoreSIL lang where
  -- data CoreExpr = ... | ProjExpr Mod | ...
  injProjModExpr  :: (Mod lang)    -> CoreExpr lang
  projProjModExpr :: CoreExpr lang -> Maybe (Mod lang)


newtype Label = Label String
              deriving (Show, Eq, Ord, Generic)

data Σ lang =
  ValΣ (CoreType lang)
  | TyΣ (CoreType lang) (CoreKind lang)
  | SigΣ (Ξ lang)
  | RecordΣ [(Label, (Σ lang))]
  | FunΣ (Bind (TyVarBinds lang) (Σ lang, Ξ lang))
    -- no elim form for SigM, we can just read off the sig!
    deriving (Show, Generic)

newtype Ξ lang =
  Ξ (Bind (TyVarBinds lang) (Σ lang))
  deriving (Show, Generic)

type TyVar lang = Name (CoreType lang)

-- pattern
type TyVarBinds lang = [(TyVar lang, Embed (CoreKind lang))]

type IdM lang = Name (Mod lang)

data Mod lang =
  -- X
  VarM (IdM lang)
  -- [e]
  | ValM (CoreExpr lang)
  -- [τ:κ]
  | TyM (CoreType lang) (CoreKind lang)
  -- [Ξ]
  | SigM (Ξ lang)
  -- {⋯, ℓ = M, ⋯}
  | RecordM [(Label, (Mod lang))]
  -- M.ℓ₁.ℓ₂…
  | ProjM (Mod lang) [Label]
    -- ∀ αs:κs . λ X : Σ . pack ⟨τs, M⟩ as ∃βs:κ′s.Σ′
  | LamM (Bind (Rebind (TyVarBinds lang) ((IdM lang), Embed (Σ lang))) (PackMod lang))
  | AppM (Mod lang) [CoreType lang] (Mod lang)
    -- unpack ⟨αs, X⟩ = M in M'
  | UnpackM (Bind ([TyVar lang], IdM lang, Embed (Mod lang)) (Mod lang))
    -- pack ⟨τs, M'⟩ as ∃βs:κ's.Σ'
  | PackM (PackMod lang)
    -- f M
  | CoerM (SubsigCoercion lang) (Mod lang)
  deriving (Show, Generic)

data SubsigCoercion lang =
  -- the identity coercion at Σ
  IdCo (Σ lang)
  -- TODO: more here
  deriving (Show, Generic)

data PackMod lang =
  PackMod [CoreType lang] (Mod lang) (Ξ lang)
  deriving (Show, Generic)


instance Alpha Label
instance (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
          Alpha (CoreKind lang), Alpha (CoreType lang))
         => Alpha (Σ lang)
instance (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
          Alpha (CoreKind lang), Alpha (CoreType lang))
         => Alpha (Ξ lang)

instance (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
          Typeable (Mod lang),
          Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang))
         => Alpha (Mod lang)
instance (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
          Typeable (Mod lang),
          Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang))
         => Alpha (PackMod lang)
instance (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
          Typeable (Mod lang),
          Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang))
         => Alpha (SubsigCoercion lang)


instance (CoreLang lang,
          Alpha (CoreKind lang), Alpha (CoreType lang),
          Subst (CoreType lang) (CoreType lang),
          Subst (CoreType lang) (CoreKind lang),
          Generic (CoreType lang),
          Typeable (CoreKind lang), Typeable (CoreType lang)
         )
         => Subst (CoreType lang) (Ξ lang)

instance (CoreLang lang,
          Alpha (CoreKind lang), Alpha (CoreType lang),
          Subst (CoreType lang) (CoreType lang),
          Subst (CoreType lang) (CoreKind lang),
          Generic (CoreType lang),
          Typeable (CoreKind lang), Typeable (CoreType lang)
         )
         => Subst (CoreType lang) (Σ lang)

instance Subst (CoreType lang) Label

mkΞ :: (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
        Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang))
       => [(TyVar lang, CoreKind lang)]
       -> Σ lang
       -> Ξ lang
mkΞ ακs = Ξ . bind (embedMap ακs)
  where
    embedMap :: [(a, b)] -> [(a, Embed b)]
    embedMap = Data.Coerce.coerce

unΞ :: (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
        Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang),
        Fresh m)
       => Ξ lang
       -> m ([(TyVar lang, CoreKind lang)], Σ lang)
unΞ (Ξ bnd) = do
  (ακs, σ) <- unbind bnd
  return (unembedMap ακs, σ)
  where
    unembedMap :: [(a, Embed b)] -> [(a, b)]
    unembedMap = Data.Coerce.coerce

unpackM :: (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang), Typeable (Mod lang),
            Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang))
           => [(TyVar lang)] -> IdM lang -> Mod lang -> Mod lang -> Mod lang
unpackM αs x m1 = UnpackM . bind (αs, x, embed m1)

packM :: [CoreType lang] -> (Mod lang) -> (Ξ lang) -> Mod lang
packM τs m = PackM . PackMod τs m

