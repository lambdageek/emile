{-# LANGUAGE TypeFamilies, KindSignatures, PolyKinds #-}
module Language.CoreLang where

import Names (Name)

-- | This is the interface between the module languages and the core language.
--
-- This class has three associated data families, but in principle the
-- core language could collapse some of these together.
class CoreLang (lang :: k) where
  -- | Core kinds classify core types
  data CoreKind lang :: *
  -- | Core types classify core expressions, other core type
  -- constructors may also be available.
  data CoreType lang :: *
  -- | Core language expressions
  data CoreExpr lang :: *

  -- | Elaboration needs to be able to inject type variables (used in
  -- elaborating abstract types) into the type fragment.
  injTyVar :: Name (CoreType lang) -> CoreType lang
