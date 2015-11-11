{-# LANGUAGE PolyKinds, TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
module Language.OIL.Elaborate where

import Names

import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.Except (MonadError(..))

import qualified Data.Map as M
import qualified Data.List

import Language.CoreLang

import Language.OIL.Syntax

import qualified Language.SIL.Syntax as SIL
import Language.SIL.Syntax (Ξ(..), Σ(..), TyVar(..))
       
class (MonadError (Err lang) m, MonadReader (Ctx lang) m, Fresh m) => MonadElab m lang

data Err lang = NotFound (MId lang)
              | NoField SIL.Label

data Ctx lang = Ctx {
  ctxTyVars :: M.Map (TyVar lang) (CoreKind lang),
  ctxModMap :: M.Map (MId lang) (SIL.IdM lang, Σ lang)
  }
                   
elaborateMId :: MonadElab m lang => MId lang -> m (SIL.Mod lang, Σ lang)
elaborateMId x = do
  mv <- asks (M.lookup x . ctxModMap)
  case mv of
    Just (x, ξ) -> return (SIL.VarM x, ξ)
    Nothing -> throwError (NotFound x)

translateField :: Field -> SIL.Label
translateField = SIL.Label . fieldName

elaborateME :: (Typeable lang, CoreLang lang,
                Typeable (CoreKind lang), Typeable (CoreType lang),
                Typeable (SIL.Mod lang),
                Generic (CoreType lang),
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
    repackXi xi me' $ \αs σ y -> do
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
               , substs s ξcod )
                

signatureMatching :: Monad m
                     => Σ lang
                     -> (SIL.TyVarBinds lang, Σ lang)
                     -> m ([CoreType lang], SIL.SubsigCoercion lang)
signatureMatching σ ξ = return (error "unimplemented subsignatureMatching")

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
