{-# language PolyKinds, TypeFamilies, PatternGuards,
             UndecidableInstances,
             StandaloneDeriving
  #-}
module Language.OIL.Elaborate where

import Names

import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.Except (MonadError(..))
import Data.Monoid (Monoid(..), (<>))

import qualified Data.Coerce
import qualified Data.Map as M
import qualified Data.List

import Language.CoreLang

import Language.OIL.Syntax

import qualified Language.SIL.Syntax as SIL
import Language.SIL.Syntax (Ξ(..), Σ(..), TyVar)
       
class (MonadError (Err lang) m, MonadReader (Ctx lang) m, Fresh m) => MonadElab m lang where
  -- | infer type for a core language expression (or raise error in the monad)
  inferTy :: CoreExpr lang -> m (CoreType lang)
  inferKind :: CoreType lang -> m (CoreKind lang)

data Err lang =
  NotFound (MId lang)
  | AppNotFunctor (MId lang)
  | NoField SIL.Label
    -- Tried to project something that didn't turn out to be a signature
  | SigProjectionNotASig (MExpr lang)

deriving instance (Show (CoreExpr lang), Show (CoreKind lang), Show (CoreType lang) ) => Show (Err lang)

data Ctx lang = Ctx {
  ctxTyVars :: M.Map (TyVar lang) (CoreKind lang),
  ctxModMap :: M.Map (MId lang) (SIL.IdM lang, Σ lang)
  }
                   
nilElabCtx :: Ctx lang
nilElabCtx = Ctx mempty mempty

elaborateMId :: MonadElab m lang => MId lang -> m (SIL.Mod lang, Σ lang)
elaborateMId x = do
  mv <- asks (M.lookup x . ctxModMap)
  case mv of
    Just (x, σ) -> return (SIL.VarM x, σ)
    Nothing -> throwError (NotFound x)

extendTyVarContext :: MonadElab m lang => SIL.TyVarBinds lang -> m a -> m a
extendTyVarContext ακs = local (updTyVars (M.union m))
  where m = M.fromList (SIL.unembedMap ακs)
        updTyVars f ctx = ctx { ctxTyVars = f (ctxTyVars ctx) }

extendModMapContext :: MonadElab m lang => [(MId lang, (SIL.IdM lang, Σ lang))] -> m a -> m a
extendModMapContext xτs = local (updModMap (M.union m))
  where m = M.fromList xτs
        updModMap f ctx = ctx { ctxModMap = f (ctxModMap ctx) }

translateField :: Field -> SIL.Label
translateField = SIL.Label . fieldName

translateMId :: MId lang -> SIL.IdM lang
translateMId = Data.Coerce.coerce

-- | elaborate a module expression 'm' to a SIL module and its SIL signature σ
elaborateME' :: (Typeable lang, CoreLang lang,
                 Typeable (CoreKind lang), Typeable (CoreType lang),
                 Typeable (SIL.Mod lang),
                 Typeable (MExpr lang),
                 Generic (CoreType lang),
                 Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang),
                 Subst (CoreType lang) (CoreKind lang),
                 Subst (CoreType lang) (CoreType lang),
                 MonadElab m lang)
                => MExpr lang
                -> m (SIL.Mod lang, SIL.TyVarBinds lang, Σ lang)
elaborateME' m = do
  (m', Ξ ξ) <- elaborateME m
  (ακs, σ) <- unbind ξ
  return (m', ακs, σ)

elaborateME :: (Typeable lang, CoreLang lang,
                Typeable (CoreKind lang), Typeable (CoreType lang),
                Typeable (SIL.Mod lang),
                Typeable (MExpr lang),
                Generic (CoreType lang), -- because of instance Generic (CoreType lang) => Subst b (Name (CoreType lang))
                Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang),
                Subst (CoreType lang) (CoreKind lang),
                Subst (CoreType lang) (CoreType lang),
                MonadElab m lang)
               => MExpr lang
               -> m (SIL.Mod lang, Ξ lang)
elaborateME m = case m of
  IdME x -> do
    (e,σ) <- elaborateMId x
    return (e, SIL.mkΞ [] σ)
  ProjME me f -> do
    (me', xi) <- elaborateME me
    let l = translateField f
    repackXi xi me' $ \_αs σ y -> do
      σ' <- getFieldΣ σ l
      return (SIL.ProjM (SIL.VarM y) [l], σ')
  AppME x1 x2 -> do
    (e1, σ₁) <- elaborateMId x1
    (e2, σ₂) <- elaborateMId x2
    case σ₁ of
      FunΣ bnd -> do
        (ακs, (σdom, ξcod)) <- unbind bnd
        (τs, coer) <- signatureMatching σ₂ (ακs, σdom)
        let αs = map fst ακs
            s = zip αs τs
        return (SIL.AppM e1 τs (SIL.CoerM coer e2)
               , substs s ξcod)
      _ -> throwError (AppNotFunctor x1)
  LitME bnd -> do
    (bindings, ()) <- unbind bnd
    (m, ακs, γ, σ) <- elaborateBindings bindings
    -- this needs to either be a term with a γ-shaped hole in it, or an unpack-repack sort of thing.
    return (SIL.RecordM m, SIL.Ξ (bind ακs (SIL.RecordΣ σ)))
    
  FunME {} -> return (error "unimplemented elaborare FunME")
  SealME {} -> return (error "unimplemented elaborare SealME")
                

elaborateBindings :: (Typeable lang
                     , CoreLang lang
                     , Generic (CoreType lang)
                     , Typeable (CoreType lang)
                     , Typeable (CoreKind lang)
                     , Typeable (SIL.Mod lang)
                     , Typeable (MExpr lang)
                     , Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang)
                     , Subst (CoreType lang) (CoreKind lang)
                     , Subst (CoreType lang) (CoreType lang)
                     , MonadElab m lang)
                     => MBinds lang
                     -> m (SIL.ModuleContent (SIL.Mod lang), SIL.TyVarBinds lang, ContextExtension lang, SIL.ModuleContent (Σ lang))
elaborateBindings mbs =
  case mbs of
    AtomicMB (Provide (f_, x) atomicBinding_) -> do
      let f = unembed f_
          atomicBinding = unembed atomicBinding_
          l = translateField f
          y = translateMId x
      (m, ακs, σ) <- elaborateAtomicBinding atomicBinding
      return ([(l, m)], ακs, [(x, (y, σ))], [(l, σ)])
      
    IncludeMB pvdExpr ->
      -- elaborateME'
      return $ error "unimplemented elaborateBindings IncludeMB"
    NilMB -> return mempty
    SeqMB rbnd -> do
      let (_mbs1, _mbs2) = unrebind rbnd
      return $ error "unimplemented elaborate sequence of bindings"

elaborateAtomicBinding :: (Typeable lang
                          , CoreLang lang
                          , Generic (CoreType lang)
                          , Typeable (CoreType lang)
                          , Typeable (CoreKind lang)
                          , Typeable (SIL.Mod lang)
                          , Typeable (MExpr lang)
                          , Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang)
                          , Subst (CoreType lang) (CoreKind lang)
                          , Subst (CoreType lang) (CoreType lang)
                          , MonadElab m lang)
                          => AtomicBinding lang
                          -> m (SIL.Mod lang, SIL.TyVarBinds lang, Σ lang)
elaborateAtomicBinding ab =
  case ab of
    ValAB e -> do
      τ <- inferTy e
      return (SIL.ValM e, [], SIL.ValΣ τ)
    TypeAB τ -> do
      κ <- inferKind τ
      return (SIL.TyM τ κ, [], SIL.TyΣ τ κ)
    ModAB m -> do
      (m', ακs, σ) <- elaborateME' m
      return (m', ακs, σ)
    SigAB sig -> do
      ξ <- elaborateMTyp sig
      return (SIL.SigM ξ, [], SIL.SigΣ ξ)

elaborateMTyp :: (Typeable lang
                 , CoreLang lang
                 , Generic (CoreType lang)
                 , Typeable (CoreType lang)
                 , Typeable (CoreKind lang)
                 , Typeable (SIL.Mod lang)
                 , Typeable (MExpr lang)
                 , Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang)
                 , Subst (CoreType lang) (CoreKind lang)
                 , Subst (CoreType lang) (CoreType lang)
                 , MonadElab m lang)
                 => MTyp lang
                 -> m (SIL.Ξ lang)
elaborateMTyp sig =
  case sig of
    PathMT m -> do
      -- don't care about what module it elaborated to,
      -- I just want the sig
      (_, ξ) <- elaborateME m
      (ακs, σ) <- SIL.unΞ ξ
      case σ of
        SigΣ ξsig -> do
          guardAvoidanceProblem (map fst ακs) ξsig
          return ξsig
        _ -> throwError (SigProjectionNotASig m)
    LitMT bnd -> do
      (decls, ()) <- unbind bnd
      (ακs, _γ, σ) <- declarations decls
      return $ SIL.Ξ (bind ακs $ SIL.RecordΣ σ)
    FunMT {} -> return (error "unimplemented elaborateMTyp FunMT")
    PatchMT {} -> return (error "unimplemented elaborateMTyp PatchMT")

type ContextExtension lang = [(MId lang, (SIL.IdM lang, SIL.Σ lang))]

declarations :: (Typeable lang
                 , CoreLang lang
                 , Generic (CoreType lang)
                 , Typeable (CoreType lang)
                 , Typeable (CoreKind lang)
                 , Typeable (SIL.Mod lang)
                 , Typeable (MExpr lang)
                 , Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang)
                 , Subst (CoreType lang) (CoreKind lang)
                 , Subst (CoreType lang) (CoreType lang)
                 , MonadElab m lang)
                 => MDecls lang
                 -> m (SIL.TyVarBinds lang, ContextExtension lang, SIL.ModuleContent (Σ lang))
declarations d =
  case d of
    AtomicMD pvdOne -> do
      (ακs, x, f, σ) <- (error "unimplemented declarations AtomicMD" ){-atomicDeclaration-} pvdOne
      let x' = translateMId x
      return (ακs, [(x,(x', σ))], [(f, σ)])
    IncludeMD pvdMany -> (error "unimeplemented declarations IncludeMD") {-includeDeclaration-} pvdMany
    NilMD -> return mempty
    SeqMD rbnd -> do
      let (d₁, d₂) = unrebind rbnd
      (ακs₁, γ₁, fs₁) <- declarations d₁
      -- xxx duplicate fields
      (ακs₂, γ₂, fs₂) <- extendTyVarContext ακs₁ $ extendModMapContext γ₁ $ declarations d₂
      return (ακs₁ <> ακs₂, γ₁ <> γ₂, fs₁ <> fs₂)

-- | Given some abstract type variables, make sure that the given
-- semantic signature object doesn't mention any of them.  This is the
  -- key to path projection.
guardAvoidanceProblem :: MonadElab m lang => [TyVar lang] -> SIL.Ξ lang -> m ()
guardAvoidanceProblem _avoid _ξ = return () -- XXX TODO: implement this

provideMany :: Provide [(Embed Field, MId lang)] a -> (a -> r) -> r
provideMany = undefined

signatureMatching :: Monad m
                     => Σ lang
                     -> (SIL.TyVarBinds lang, Σ lang)
                     -> m ([CoreType lang], SIL.SubsigCoercion lang)
signatureMatching _σ _ξ =
  return (error "unimplemented subsignatureMatching")

getFieldΣ :: MonadElab m lang => Σ lang -> SIL.Label -> m (Σ lang)
getFieldΣ σ l = case σ of
  RecordΣ ls | (Just σ') <- Data.List.lookup l ls -> return σ'
  _ -> throwError (NoField l)

repackXi :: (CoreLang lang, Typeable (CoreKind lang), Typeable (CoreType lang),
             Typeable (SIL.Mod lang),
             Alpha (CoreKind lang), Alpha (CoreType lang), Alpha (CoreExpr lang),
             MonadElab m lang)
            => Ξ lang -> SIL.Mod lang
            -> ([(TyVar lang, CoreKind lang)] -> Σ lang -> SIL.IdM lang -> m (SIL.Mod lang, Σ lang))
            -> m (SIL.Mod lang, Ξ lang)
repackXi xi e k = do
  y <- fresh (string2Name "y")
  (ακs, σ) <- SIL.unΞ xi
  (e', σ') <- k ακs σ y
  let αs = map fst ακs
      τs = map injTyVar αs
      xi' = SIL.mkΞ ακs σ'
  return (SIL.unpackM (map fst ακs) y e (SIL.packM τs e' xi'), xi')
