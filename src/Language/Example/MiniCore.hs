{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving,
  DataKinds, TypeFamilies, PatternSynonyms, PolyKinds, EmptyDataDecls,
  ViewPatterns
  #-}
module Language.Example.MiniCore where

import Control.Applicative (Applicative(..), (<$>))
import Control.Monad (when)
import Data.Traversable
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Data.Foldable (for_)
import qualified Data.Map as M

import Names

import Language.CoreLang
import Language.SIL.Syntax (MapNameMonad(..), DesugarSIL(..),
                            Σ(..), Ξ(..),
                            IdM, Mod(..), PackMod(..),
                            SubsigCoercion(..),
                            Label(..))

data MiniSIL
  deriving (Typeable)

instance CoreLang MiniSIL where
  data CoreKind MiniSIL =
    TypeK
    | ArrK Kind Kind -- κ₁ → κ₂
    deriving (Show, Generic, Eq)
  data CoreType MiniSIL =
    VarT TyVar
    | ArrT Type Type
    | ProdT [(Label, Type)]
    | AppT Type Type
    | ForallT (Bind (TyVar, Embed Kind) Type)
    | ExistT (Bind (TyVar, Embed Kind) Type)
    deriving (Show, Generic)
  data CoreExpr MiniSIL =
    VarE Var
    | LamE (Bind (Var, Embed Type) Expr)
    | AppE Expr Expr
    | TupleE [(Label, Expr)]
    | ProjE Expr Label -- e.ℓ
    | TLamE (Bind (TyVar, Embed Kind) Expr)
    | TAppE Expr Type
      -- pack ⟨τ, e⟩ as σ where σ=∃α:κ.σ′
    | PackE Type Expr Type
      -- let pack ⟨α,x⟩ = e₁ in e₂
    | LetPackE (Bind (TyVar, Var, Embed Expr) Expr)
      -- XXX this bit is unmotivated...  I need it for nullary UnpackM
      -- in SIL which seems like it's missing a type annotation which
      -- would let me just desugar to a lambda and an application.
    | LetE (Bind (Var, Embed Expr) Expr)
    deriving (Show, Generic)

  injTyVar = VarT

desugarSigma :: (Fresh m, Applicative m) => Σ MiniSIL -> m Type
desugarSigma (ValΣ τ) =
  -- [$val : τ]
  pure $ ProdT [(ValueLabel, τ)]
desugarSigma (TyΣ τ κ) = do
  encodeType <$> polyEqT τ κ
  where
    encodeType t = ProdT [(TypeLabel, t)]
desugarSigma (SigΣ ξ) = do
  τ <- desugarXi ξ
  encodeSig <$> polyEqT τ TypeK
  where
    encodeSig t = ProdT [(SignatureLabel, t)]
desugarSigma (RecordΣ lss) =
  ProdT <$> traverse desugarLabeledSigma lss
  where
    desugarLabeledSigma (label, σ) = (,) <$> pure label <*> desugarSigma σ
desugarSigma (FunΣ bnd) = do
  (tvbs, (σ, ξ)) <- unbind bnd
  -- ∀ αs:κs . ↓σ → ↓ξ
  foralls tvbs <$> (ArrT <$> desugarSigma σ <*> desugarXi ξ)

-- polyEqT τ κ = ∀ α:(κ→⋆). α τ → α τ
polyEqT :: Fresh m => Type -> Kind -> m Type
polyEqT τ κ = do
  α <- fresh (s2n "α")
  let t = AppT (VarT α) τ
      k = κ `ArrK` TypeK
  return $ ForallT $ bind (α, embed k) $ t `ArrT` t

-- polyReflE τ κ = Λ α :(κ→⋆). λx:(α τ). x
polyReflE :: Fresh m => Type -> Kind -> m Expr
polyReflE τ κ = do
  α <- fresh (s2n "α")
  x <- fresh (s2n "x")
  let k = κ `ArrK` TypeK
      t = AppT (VarT α) τ
      f = LamE $ bind (x, embed t) $ VarE x
  return $ TLamE $ bind (α, embed k) f

instance DesugarSIL MiniSIL where
  desugarMod (VarM v) = VarE <$> lookupIdM v
  desugarMod (ValM e) = pure $ TupleE [(ValueLabel, e)]
  desugarMod (TyM τ κ) = do
    e <- polyReflE τ κ
    return $ TupleE [(TypeLabel, e)]
  desugarMod (SigM ξ) = do
    τ <- desugarXi ξ
    e <- polyReflE τ TypeK
    return $ TupleE [(SignatureLabel, e)]
  desugarMod (RecordM lms) =
    TupleE <$> traverse desugarLabeledMods lms
  desugarMod (ProjM m ls) =
    flip projects ls <$> desugarMod m
  desugarMod (LamM bnd) =
    desugarLamModExpr bnd
  desugarMod (AppM mf τs mx) =
    AppE <$> (tapps <$> desugarMod mf <*> pure τs) <*> desugarMod mx
  desugarMod (CoerM coer m) =
    AppE <$> desugarCoercion coer <*> desugarMod m
  desugarMod (PackM packmod) = desugarPackMod packmod
  desugarMod (UnpackM bnd) =
    desugarUnpackModExpr bnd

desugarLabeledMods :: (MapNameMonad m lang, DesugarSIL lang, Fresh m) => (Label, Mod lang) -> m (Label, CoreExpr lang)
desugarLabeledMods (label, m) = (,) <$> pure label <*> desugarMod m

desugarCoercion :: Fresh m => SubsigCoercion MiniSIL -> m Expr
desugarCoercion (IdCo σ) = do
  τ <- desugarSigma σ
  x <- fresh (s2n "x")
  -- λ x : τ . x
  return $ LamE $ bind (x, embed τ) $ VarE x

desugarLamModExpr :: (MapNameMonad m MiniSIL, Fresh m)
                    => Bind (Rebind [(TyVar, Embed Kind)] (IdM MiniSIL, Embed (Σ MiniSIL))) (PackMod MiniSIL)
                    -> m Expr
desugarLamModExpr bnd = do
  (rbnd, pack) <- unbind bnd
  let (ακs, (x, Embed σ)) = unrebind rbnd
  τ <- desugarSigma σ
  -- Λ αs:κs . λ x′:σ . pack
  l <- extendIdM x $ \y -> do
    pack' <- desugarPackMod pack
    pure $ LamE $ bind (y, Embed τ) pack'
  return $ tlams ακs l

desugarUnpackModExpr :: (MapNameMonad m MiniSIL, Fresh m)
                       => Bind ([TyVar], IdM MiniSIL, Embed (Mod MiniSIL)) (Mod MiniSIL)
                       -> m Expr
desugarUnpackModExpr bnd = do
  ((αs, x, Embed m1), m2) <- unbind bnd
  e1 <- desugarMod m1
  (y, e2) <- extendIdM x $ \y -> do
    e2 <- desugarMod m2
    return (y, e2)
  letpacks αs y e1 e2

desugarPackMod :: (MapNameMonad m MiniSIL, Fresh m)
                 => PackMod MiniSIL -> m Expr
desugarPackMod (PackMod τs m (Ξ bnd)) = do
  (ακs, σ) <- unbind bnd
  τ₀ <- desugarSigma σ
  e <- desugarMod m
  when (length ακs /= length τs) $ error "internal error - malformed PackMod"
  return $ packs e τ₀ (zip τs ακs) 



-- letpack ⟨x⟩ = e₁ in e₂       ≙ let x = e₁ in e₂
-- letpack ⟨α,βs, x⟩ = e₁ in e₂ ≙ letpack ⟨α,y⟩ = e₁ in letpack ⟨βs,x⟩ = y in e₂
letpacks :: Fresh m => [TyVar] -> Var -> Expr -> Expr -> m Expr
letpacks [] x e₁ e₂ = return $ LetE $ bind (x, embed e₁) e₂
letpacks (α:βs) x e₁ e₂ = do
  y <- fresh (s2n "y")
  e₂' <- letpacks βs x (VarE y) e₂
  return $ LetPackE $ bind (α, y, embed e₁) e₂'

-- pack ⟨e⟩ as t                 ≙ e
-- pack ⟨τ₁, τs, e⟩ as (∃α,βs.t) ≙ pack ⟨τ₁, pack ⟨τs, e⟩ as ∃βs.t[τ₁/α]⟩ as ∃α.∃βs.t
-- packs E T [(τs, ακs)] = pack ⟨τs, e⟩> as (∃αs. T)
packs :: Expr -> Type -> [(Type, (TyVar, Embed Kind))] -> Expr
packs e _t [] = e
packs e t ((τ, ακ@(α,_κ)):τβκs) =
  let e' = packs e (subst α τ t) τβκs
      βks = map snd τβκs
      t' = existss βks t
  in PackE τ e' (ExistT $ bind ακ t')

foralls :: [(TyVar, Embed Kind)] -> Type -> Type
foralls [] = id
foralls (tvb:tvbs) = ForallT . bind tvb . foralls tvbs

existss :: [(TyVar, Embed Kind)] -> Type -> Type
existss [] = id
existss (tvb:tvbs) = ExistT . bind tvb . existss tvbs

projects :: Expr -> [Label] -> Expr
projects e [] = e
projects e (l:ls) = projects (ProjE e l) ls

tlams :: [(TyVar, Embed Kind)] -> Expr -> Expr
tlams [] = id
tlams (ακ:ακs) = TLamE . bind ακ . tlams ακs

tapps :: Expr -> [Type] -> Expr
tapps e [] = e
tapps e (τ:τs) = tapps (TAppE e τ) τs

desugarXi :: (Fresh m, Applicative m) => Ξ MiniSIL -> m Type
desugarXi (Ξ bnd) = do
  (tvbs, σ) <- unbind bnd
  existss tvbs <$> desugarSigma σ

-- pattern ValueLabel :: Label
pattern ValueLabel = Label "$val"

-- pattern TypeLabel :: Label
pattern TypeLabel = Label "$type"

-- pattern SignatureLabel :: Label
pattern SignatureLabel = Label "$sig"

type Kind = CoreKind MiniSIL

type Type = CoreType MiniSIL
type TyVar = Name Type

type Expr = CoreExpr MiniSIL
type Var = Name Expr

instance Alpha (CoreKind MiniSIL)
instance Alpha (CoreType MiniSIL)
instance Alpha (CoreExpr MiniSIL)

instance Subst (CoreType MiniSIL) (CoreKind MiniSIL)

instance Subst (CoreType MiniSIL) (CoreType MiniSIL) where
  isvar (VarT v) = Just (SubstName v)
  isvar _ = Nothing

data CoreErr =
  ExpectedFnExpr Expr
  | ExpectedFnType Type
  | ExpectedEquivTypes Type Type
  | ExpectedEquivKinds Kind Kind
  | ExpectedTypeK
  | UnboundVar Var
  | UnboundTyVar TyVar
  deriving Show

data CoreCtx = CoreCtx { coreCtxV :: M.Map Var Type
                       , coreCtxTV :: M.Map TyVar Kind
                       }

raiseExpectedFn :: MonadError CoreErr m => Expr -> m a
raiseExpectedFn = throwError . ExpectedFnExpr

raiseExpectedFnKind :: MonadError CoreErr m => Type -> m a
raiseExpectedFnKind = throwError . ExpectedFnType

raiseExpectedEqTy :: MonadError CoreErr m => Type -> Type -> m a
raiseExpectedEqTy τ = throwError . ExpectedEquivTypes τ

raiseExpectedEqK :: MonadError CoreErr m => Kind -> Kind -> m a
raiseExpectedEqK κ = throwError . ExpectedEquivKinds κ

raiseExpectedTypeK :: MonadError CoreErr m => m a
raiseExpectedTypeK = throwError ExpectedTypeK

raiseUnboundVar :: MonadError CoreErr m => Var -> m a
raiseUnboundVar = throwError . UnboundVar

raiseUnboundTyVar :: MonadError CoreErr m => TyVar -> m a
raiseUnboundTyVar = throwError . UnboundTyVar

lookupVar x = do
  mt <- asks (M.lookup x . coreCtxV)
  case mt of
    Just τ -> return τ
    Nothing -> raiseUnboundVar x

lookupTyVar α = do
  mk <- asks (M.lookup α . coreCtxTV)
  case mk of
    Just κ -> return κ
    Nothing -> raiseUnboundTyVar α

coreNilCtx :: CoreCtx
coreNilCtx = CoreCtx mempty mempty

extendTyVarCtx α κ = local (\ c -> c { coreCtxTV = M.insert α κ (coreCtxTV c) } )
extendVarCtx x τ = local (\ c -> c { coreCtxV = M.insert x τ (coreCtxV c) } )
  

ensureEquivTy τ σ _κ =
  case (τ, σ) of
    (VarT α, VarT β) | α == β -> return ()
                     | otherwise -> raiseExpectedEqTy τ σ
    _ -> error "unimplemented ensureEquivTy"

ensureEquivKind κ₁ κ₂ | κ₁ == κ₂ = return ()
                      | otherwise = raiseExpectedEqK κ₁ κ₂
  
whnfTy :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m Type
whnfTy = return

inferCoreType :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Expr -> m Type
inferCoreType (VarE x) = lookupVar x
inferCoreType (LamE bnd) = do
  ((x, unembed -> τ), e) <- unbind bnd
  τ' <- extendVarCtx x τ $ inferCoreType e
  return $ τ `ArrT` τ'
inferCoreType (AppE e₁ e₂) = do
  τ_ <- inferCoreType e₁
  τ <- whnfTy τ_
  case τ of
    ArrT τparam τres -> do
      τarg <- inferCoreType e₂
      ensureEquivTy τparam τarg TypeK
      return τres
    _ -> raiseExpectedFn e₁
inferCoreType (TupleE elems) = do
  lτs <- for elems $ \(lbl, e) -> do
    τ <- inferCoreType e
    return (lbl, τ)
  return $ ProdT lτs
inferCoreType _ = error "unimplemented inferCoreType"


ensureTypeK :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m ()
ensureTypeK τ = do
  κ <- inferCoreKind τ
  case κ of
    TypeK -> return ()
    _ -> raiseExpectedTypeK


inferCoreKind :: (Fresh m, MonadError CoreErr m, MonadReader CoreCtx m) => Type -> m Kind
inferCoreKind (VarT α) = lookupTyVar α
inferCoreKind (ArrT τ₁ τ₂) = do
  ensureTypeK τ₁
  ensureTypeK τ₂
  return TypeK
inferCoreKind (ExistT bnd) = do
  ((α, unembed -> κ), τ) <- unbind bnd
  extendTyVarCtx α κ $ ensureTypeK τ
  return TypeK
inferCoreKind (AppT τ₁ τ₂) = do
  κ <- inferCoreKind τ₁
  case κ of
    ArrK κ₁ κ₂ -> do
      κ₁' <- inferCoreKind τ₂
      ensureEquivKind κ₁ κ₁'
      return κ₂
    TypeK -> raiseExpectedFnKind τ₁
inferCoreKind (ProdT lτs) = do
  for_ lτs $ \(_lbl, τ) -> ensureTypeK τ
  return TypeK
inferCoreKind _ = error "unimplemented inferCoreKind"
    
