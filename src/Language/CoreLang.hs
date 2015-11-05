{-# LANGUAGE TypeFamilies, KindSignatures, PolyKinds #-}
module Language.CoreLang where

class CoreLang (lang :: k) where
  data CoreKind lang :: *
  data CoreType lang :: *
  data CoreExpr lang :: *

