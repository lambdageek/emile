{-# LANGUAGE PolyKinds, TypeFamilies, GADTs, UndecidableInstances, ConstraintKinds #-}
module Language.SIL.Syntax where

import qualified Data.Coerce

import Names

import Language.CoreLang

class (CoreLang lang, Monad m) => MapNameMonad m lang where
  lookupIdM :: IdM lang -> m (Name (CoreExpr lang))
  extendIdM :: IdM lang -> (Name (CoreExpr lang) -> m a) -> m a

-- | Desugar SIL
--
-- The SIL language of abstract signatures and structures is just a
-- convenient syntactic sugar for certain expressions of a language
-- that is at least as powerful as System F (for the generative
-- fragment, or System Fω with applicative functors).  This is the
-- class that witnesses that desugaring.
class CoreLang lang => DesugarSIL lang where
  desugarMod  :: (MapNameMonad m lang, Fresh m) => Mod lang -> m (CoreExpr lang)


newtype Label = Label String
              deriving (Show, Eq, Ord, Generic)

-- | Concrete semantic signatures
--
-- Σ Each SIL module may be ascribed a semantic signature of the form
-- Ξ ≙ ∃αs.Σ where Σ is a concrete semantic signature.
data Σ lang =
  -- | [τ] concrete signature for a module containing a single value expression
  ValΣ (CoreType lang)
  -- | [=τ:κ] concrete signature for a module containing a single type definition.
  -- in the case of sealed modules where an abstract type is hidden this will be
  -- a type variable bound in an outer scope.  For manifest types it will be some type expression.
  | TyΣ (CoreType lang) (CoreKind lang)
  -- | [=Ξ] single manifest signature definition. In SIL, modules may contain signature definitions.
  | SigΣ (Ξ lang)
  -- | {⋯ ℓ : Σ, ⋯} a module containing several named bindings.
  | RecordΣ [(Label, (Σ lang))]
  -- | ∀αs.Σ₁ → Ξ a generative functor signature the functor takes
  -- several types and a module with concrete signature Σ₁ (which may
  -- mention αs) and reutrns a module Ξ=∃βs.Σ₂ where Σ₂ may mention αs
  -- and βs.  Thus each application of the functor produces new
  -- distinct abstract types βs while allowing the result to depend on
  -- the abstract types of the argument Σ₁.
  | FunΣ (Bind (TyVarBinds lang) (Σ lang, Ξ lang))
    deriving (Show, Generic)

newtype Ξ lang =
  Ξ (Bind (TyVarBinds lang) (Σ lang))
  deriving (Show, Generic)

type TyVar lang = Name (CoreType lang)

-- pattern
type TyVarBinds lang = [(TyVar lang, Embed (CoreKind lang))]

-- | bound module identifier
type IdM lang = Name (Mod lang)

-- | Semantic module expressions
data Mod lang =
  -- | X module identifier
  VarM (IdM lang)
  -- | [e] a module containing a single expression
  | ValM (CoreExpr lang)
  -- | [τ:κ] a module containing a single type definition τ
  | TyM (CoreType lang) (CoreKind lang)
  -- | [Ξ] a module containing a single signature definition Ξ
  | SigM (Ξ lang)
  -- | {⋯, ℓ = M, ⋯} a module containing several named bindings
  | RecordM [(Label, (Mod lang))]
  -- | M.ℓ₁.ℓ₂… projection of a named field from a composite module
  | ProjM (Mod lang) [Label]
    -- | Λ αs:κs . λ X : Σ . pack ⟨τs, M⟩ as ∃βs:κ′s.Σ′  generative functor construction
  | LamM (Bind (Rebind (TyVarBinds lang) ((IdM lang), Embed (Σ lang))) (PackMod lang))
    -- | F [τs] M functor application
  | AppM (Mod lang) [CoreType lang] (Mod lang)
    -- | unpack ⟨αs, X⟩ = M in M' abstract module unpacking
  | UnpackM (Bind ([TyVar lang], IdM lang, Embed (Mod lang)) (Mod lang))
    -- | pack ⟨τs, M'⟩ as Ξ sealing at an abstract signature
  | PackM (PackMod lang)
    -- | ¢@M module subsignature coercion - ¢ is a witness for the
    -- subsignature judgment αs ⊢ Σ ≤ Ξ ⇝ ¢ (these could all be
    -- expressed in terms of packing unpacking record construction and
    -- projection etc, but they tend to produce a lot of boring
    -- administrative redices, so it's better to keep them somewhat
    -- abstract and delay desugaring)
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

