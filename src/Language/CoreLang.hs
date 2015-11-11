{-# LANGUAGE TypeFamilies, KindSignatures, PolyKinds #-}
module Language.CoreLang where

import Names (Name)

class CoreLang (lang :: k) where
  data CoreKind lang :: *
  data CoreType lang :: *
  data CoreExpr lang :: *

  injTyVar :: Name (CoreType lang) -> CoreType lang
