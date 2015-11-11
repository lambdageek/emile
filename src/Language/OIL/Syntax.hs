{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs, KindSignatures, PolyKinds, StandaloneDeriving, ConstraintKinds #-}
module Language.OIL.Syntax where

import Names
import Language.CoreLang

type MId lang = Name (MExpr lang)
newtype Field = Field { fieldName :: String }
                deriving (Show, Generic)

data MExpr (lang :: k) where
  IdME :: MId lang -> MExpr lang
  ProjME :: MExpr lang -> Field -> MExpr lang
  FunME :: Bind (MId lang, Embed (MTyp lang)) (MExpr lang) -> MExpr lang
  AppME :: MId lang -> MId lang -> MExpr lang
  SealME :: MId lang -> MTyp lang -> MExpr lang
  LitME :: Embed (MBinds lang) -> MExpr lang

data MTyp (lang :: k) where
  PathMT :: MExpr lang -> MTyp lang
  FunMT :: Bind (MId lang, Embed (MTyp lang)) (MTyp lang) -> MTyp lang
  PatchMT :: MTyp lang -> MWhere lang -> MTyp lang
  LitMT :: Embed (MDecls lang) -> MTyp lang

data MWhere (lang :: k) =
  MWhere [Field] (CoreType  lang)
  deriving (Show, Generic)

-- pattern
data MBinds (lang :: k) where
  AtomicMB :: Embed Field -> MId lang -> Embed (AtomicBinding lang) -> MBinds lang
  IncludeMB :: Provide [(Embed Field, MId lang)] (MExpr lang) -> MBinds lang
  NilMB :: MBinds lang
  SeqMB :: Rebind (MBinds lang) (MBinds lang) -> MBinds lang

data AtomicBinding (lang :: k) where
  ValAB :: CoreExpr lang -> AtomicBinding lang
  TypeAB :: CoreType lang -> AtomicBinding lang
  ModAB :: MExpr lang -> AtomicBinding lang
  SigAB :: MTyp lang -> AtomicBinding lang

-- pattern
data MDecls (lang :: k) where
  AtomicMD :: Embed Field -> MId lang -> Embed (AtomicDecl lang) -> MDecls lang
  IncludeMD :: Provide [(Embed Field, MId lang)] (MTyp lang) -> MDecls lang
  NilMD :: MDecls lang
  SeqMD :: Rebind (MDecls lang) (MDecls lang) -> MDecls lang

data AtomicDecl (lang :: k) where
  ValMD :: CoreType lang -> AtomicDecl lang
  TypeMD :: Either (CoreKind lang) (CoreType lang) -> AtomicDecl lang
  ModMD :: MTyp lang -> AtomicDecl lang
  SigMD :: MTyp lang -> AtomicDecl lang

data Provide p t = Provide p (Embed t) -- provide the names p

type CoreShow lang = (Show (CoreType lang), Show (CoreExpr lang), Show (CoreKind lang))
type CoreAlpha lang = (Alpha (CoreType lang), Alpha (CoreExpr lang), Alpha (CoreKind lang))


deriving instance CoreShow lang => Show (MExpr lang)
deriving instance CoreShow lang => Show (MTyp lang)
deriving instance CoreShow lang => Show (MBinds lang)
deriving instance CoreShow lang => Show (AtomicBinding lang)
deriving instance CoreShow lang => Show (MDecls lang)
deriving instance CoreShow lang => Show (AtomicDecl lang)
deriving instance (Show p, Show t) => Show (Provide p t)

deriving instance Generic (MExpr lang)
deriving instance Generic (MTyp lang)
deriving instance Generic (MBinds lang)
deriving instance Generic (AtomicBinding lang)
deriving instance Generic (MDecls lang)
deriving instance Generic (AtomicDecl lang)
deriving instance Generic (Provide p t)


instance (Alpha p, Alpha t) => Alpha (Provide p t)

instance Alpha Field
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MExpr lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MBinds lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (AtomicBinding lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MTyp lang)
instance (Alpha (CoreType lang)) => Alpha (MWhere lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (MDecls lang)
instance (CoreShow lang, CoreAlpha lang, Typeable (MExpr lang)) => Alpha (AtomicDecl lang)
