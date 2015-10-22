{-# LANGUAGE DataKinds, TypeFamilies #-}
module Language.Example.MiniCore where

import Names

import Language.SIL.Syntax (CoreLang(..), Mod)

data Mini = MiniSIL

instance CoreLang MiniSIL where
  data CoreKind MiniSIL =
    TypeK
    deriving (Show, Generic)
  data CoreType MiniSIL =
    VarT TyVar
    | ArrT Type Type
    deriving (Show, Generic)
  data CoreExpr MiniSIL =
    VarE Var
    | LamE (Bind (Var, Embed Type) Expr)
    | AppE Expr Expr
    | ProjModE (Mod MiniSIL)
    deriving (Show, Generic)

  injProjModExpr = ProjModE
  projProjModExpr (ProjModE mod) = Just mod
  projProjModExpr _ = Nothing

type Type = CoreType MiniSIL
type TyVar = Name Type

type Expr = CoreExpr MiniSIL
type Var = Name Expr