{-# LANGUAGE PolyKinds, TypeFamilies, GADTs, UndecidableInstances, ConstraintKinds #-}
module Language.SIL.Syntax where

import Names

import Language.CoreLang

-- Core SIL
class CoreLang lang => CoreSIL lang where
  -- data CoreExpr = ... | ProjExpr Mod | ...
  injProjModExpr  :: (Mod lang)    -> CoreExpr lang
  projProjModExpr :: CoreExpr lang -> Maybe (Mod lang)


newtype Label = Label String
              deriving (Show, Generic)

data Σ lang =
  ValΣ (CoreType lang)
  | TyΣ (CoreType lang) (CoreKind lang)
  | SigΣ (Ξ lang)
  | RecordΣ [(Label, (Σ lang))]
  | FunΣ (Bind (TyVarBinds lang) (Σ lang, Ξ lang))
    -- no elim form for SigM, we can just read off the sig!
    deriving (Show, Generic)

newtype Ξ lang =
  Ξ (Bind [(TyVar lang, Embed (CoreKind lang) )] (Σ lang))
  deriving (Show, Generic)

type TyVar lang = Name (CoreType lang)

-- pattern
type TyVarBinds lang = [(TyVar lang, Embed (CoreKind lang))]

type IdM lang = Name (Mod lang)

data Mod lang =
  VarM (IdM lang)
  | ValM (CoreExpr lang)
  | TyM (CoreType lang) (CoreKind lang)
  | SigM (Ξ lang)
  | RecordM [(Label, (Mod lang))]
  | ProjM (Mod lang) [Label]
    -- ∀ αs:κs . λ X : Σ . pack ⟨τs, M⟩ as ∃βs:κ′s.Σ′
  | LamM (Bind (Rebind (TyVarBinds lang) ((IdM lang), Embed (Σ lang))) (PackMod lang))
  | AppM (Mod lang) [CoreType lang] (Mod lang)
  | LetM (Bind ([TyVar lang], IdM lang, Embed (Mod lang)) (Mod lang))
  deriving (Show, Generic)

data PackMod lang =
  PackMod [CoreType lang] (Mod lang) (Ξ lang)
  deriving (Show, Generic)


type TypeableCore lang = (Typeable lang, Typeable (CoreKind lang), Typeable (CoreType lang))
type AlphaCore lang = (Alpha (CoreKind lang), Alpha (CoreType lang))

instance Alpha Label
instance (CoreLang lang, TypeableCore lang, AlphaCore lang) => Alpha (Σ lang)
instance (CoreLang lang, TypeableCore lang, AlphaCore lang) => Alpha (Ξ lang)

instance (CoreLang lang, TypeableCore lang, AlphaCore lang, Typeable (Mod lang), Alpha (CoreExpr lang)) => Alpha (Mod lang)
instance (CoreLang lang, TypeableCore lang, AlphaCore lang, Typeable (Mod lang), Alpha (CoreExpr lang)) => Alpha (PackMod lang)

