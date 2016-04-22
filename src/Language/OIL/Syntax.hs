{-# language StandaloneDeriving, UndecidableInstances,
             GADTs, KindSignatures, PolyKinds, StandaloneDeriving, ConstraintKinds
  #-}
module Language.OIL.Syntax where

import Names
import Language.CoreLang

type MId lang = Name (MExpr lang)
newtype Field = Field { fieldName :: String }
                deriving (Show, Generic)

-- module expressions
data MExpr (lang :: k) where
  -- module identifier
  IdME :: MId lang -> MExpr lang
  -- module projection
  ProjME :: MExpr lang -> Field -> MExpr lang
  -- (generative) functor construction
  FunME :: Bind (MId lang, Embed (MTyp lang)) (MExpr lang) -> MExpr lang
  -- (generative) functor application
  AppME :: MId lang -> MId lang -> MExpr lang
  -- sealing
  SealME :: MId lang -> MTyp lang -> MExpr lang
  -- literal module
  LitME :: Bind (MBinds lang) () -> MExpr lang

-- module types (aka signatures)
data MTyp (lang :: k) where
  -- path projection.  All expressions are syntactically valid as
  -- paths, but the path elaboration judgment will rule out non-projectable
  -- ones.
  PathMT :: MExpr lang -> MTyp lang
  -- (generative) functor signatures
  FunMT :: Bind (MId lang, Embed (MTyp lang)) (MTyp lang) -> MTyp lang
  -- signature patching with a "where" clause
  PatchMT :: MTyp lang -> MWhere lang -> MTyp lang
  -- literal module signature
  LitMT :: Bind (MDecls lang) () -> MTyp lang

-- where clauses
data MWhere (lang :: k) =
  MWhere [Field] (CoreType  lang)
  deriving (Generic)

deriving instance (Show (CoreType lang)) => Show (MWhere lang)

-- module bindings
-- (Unbound pattern)
data MBinds (lang :: k) where
  -- atomic binding of a single field.
  AtomicMB :: Provide (Embed Field, MId lang) (AtomicBinding lang) -> MBinds lang
  -- inclusion of another module expression
  IncludeMB :: Provide [(Embed Field, MId lang)] (MExpr lang) -> MBinds lang
  -- the empty module
  NilMB :: MBinds lang
  -- binding sequencing
  SeqMB :: Rebind (MBinds lang) (MBinds lang) -> MBinds lang

-- atomic binding
-- (Unbound term)
data AtomicBinding (lang :: k) where
  ValAB :: CoreExpr lang -> AtomicBinding lang
  -- type X = T
  TypeAB :: CoreType lang -> AtomicBinding lang
  ModAB :: MExpr lang -> AtomicBinding lang
  SigAB :: MTyp lang -> AtomicBinding lang

-- signature declarations
-- (Unbound pattern)
data MDecls (lang :: k) where
  -- atomic delcaration of a single field X
  AtomicMD :: Provide (Embed Field, MId lang) (AtomicDecl lang) -> MDecls lang
  -- signature inclusion
  IncludeMD :: Provide [(Embed Field, MId lang)] (MTyp lang) -> MDecls lang
  -- the empty signature
  NilMD :: MDecls lang
  -- declaration sequencing
  SeqMD :: Rebind (MDecls lang) (MDecls lang) -> MDecls lang

-- | atomic declaration
-- (Unbound term)
data AtomicDecl (lang :: k) where
  -- | val X : T
  ValMD :: CoreType lang -> AtomicDecl lang
  -- | type X : K     or     type X = T
  TypeMD :: Either (CoreKind lang) (CoreType lang) -> AtomicDecl lang
  -- | module X : S
  ModMD :: MTyp lang -> AtomicDecl lang
  -- | signature X = S
  SigMD :: MTyp lang -> AtomicDecl lang

-- convenience wrapper for bindings and declarations 
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
