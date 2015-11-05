{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs, KindSignatures, PolyKinds, StandaloneDeriving, ConstraintKinds #-}
module Language.OIL.Syntax where

import Names
import Language.CoreLang

type MId lang = Name (MExpr lang)

data MExpr (lang :: k) where
  IdME :: MId lang -> MExpr lang
  ProjME :: MExpr lang -> MId lang -> MExpr lang
  FunME :: Bind (MId lang, Embed (MTyp lang)) (MExpr lang) -> MExpr lang
  AppME :: MExpr lang -> MExpr lang -> MExpr lang
  SealME :: MExpr lang -> MTyp lang -> MExpr lang
  LitME :: Embed (MBinds lang) -> MExpr lang

data MTyp (lang :: k) where
  PathMT :: MExpr lang -> MTyp lang
  FunMT :: Bind (MId lang, Embed (MTyp lang)) (MTyp lang) -> MTyp lang
  PatchMT :: MTyp lang -> MWhere lang -> MTyp lang
  LitMT :: Embed (MDecls lang) -> MTyp lang

data MWhere (lang :: k) = MWhere

-- pattern
data MBinds (lang :: k) where
  ValMB :: MId lang -> Embed (CoreExpr lang) -> MBinds lang
  TypeMB :: MId lang -> Embed (CoreType lang) -> MBinds lang
  ModMB :: MId lang -> Embed (MExpr lang) -> MBinds lang
  SigMB :: MId lang -> Embed (MTyp lang) -> MBinds lang
  IncludeMB :: Provide [MId lang] (MExpr lang) -> MBinds lang
  NilMB :: MBinds lang
  SeqMB :: Rebind (MBinds lang) (MBinds lang) -> MBinds lang

-- pattern
data MDecls (lang :: k) where
  ValMD :: MId lang -> Embed (CoreType lang) -> MDecls lang
  TypeMD :: MId lang -> Embed (Either (CoreKind lang) (CoreType lang)) -> MDecls lang
  ModMD :: MId lang -> Embed (MTyp lang) -> MDecls lang
  SigMD :: MId lang -> Embed (MTyp lang) -> MDecls lang
  IncludeMD :: Provide [MId lang] (MTyp lang) -> MDecls lang
  NilMD :: MDecls lang
  SeqMD :: Rebind (MDecls lang) (MDecls lang) -> MDecls lang

data Provide p t = Provide p (Embed t) -- provide the names p

type CoreShow lang = (Show (CoreType lang), Show (CoreExpr lang), Show (CoreKind lang))
type CoreAlpha lang = (Alpha (CoreType lang), Alpha (CoreExpr lang), Alpha (CoreKind lang))


deriving instance CoreShow lang => Show (MExpr lang)
deriving instance CoreShow lang => Show (MTyp lang)
deriving instance CoreShow lang => Show (MBinds lang)
deriving instance CoreShow lang => Show (MDecls lang)
deriving instance Show (MWhere lang)
deriving instance (Show p, Show t) => Show (Provide p t)

deriving instance Generic (MExpr lang)
deriving instance Generic (MTyp lang)
deriving instance Generic (MBinds lang)
deriving instance Generic (MDecls lang)
deriving instance Generic (MWhere lang)
deriving instance Generic (Provide p t)


instance (Alpha p, Alpha t) => Alpha (Provide p t)

instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MExpr lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MBinds lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MTyp lang)
instance Alpha (MWhere lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MDecls lang)

