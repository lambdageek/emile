-- | Type-checking context
module Language.Example.MiniCore.Context where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M

import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Errors

data CoreCtx = CoreCtx { coreCtxV :: M.Map Var Type
                       , coreCtxTV :: M.Map TyVar Kind
                       }


lookupVar :: (MonadError CoreErr m, MonadReader CoreCtx m) => Var -> m Type
lookupVar x = do
  mt <- asks (M.lookup x . coreCtxV)
  case mt of
    Just τ -> return τ
    Nothing -> raiseUnboundVar x

lookupTyVar :: (MonadError CoreErr m, MonadReader CoreCtx m) => TyVar -> m Kind
lookupTyVar α = do
  mk <- asks (M.lookup α . coreCtxTV)
  case mk of
    Just κ -> return κ
    Nothing -> raiseUnboundTyVar α

coreNilCtx :: CoreCtx
coreNilCtx = CoreCtx mempty mempty

extendTyVarCtx :: (MonadReader CoreCtx m) => TyVar -> Kind -> m a -> m a
extendTyVarCtx α κ = local (\ c -> c { coreCtxTV = M.insert α κ (coreCtxTV c) } )

extendVarCtx :: (MonadReader CoreCtx m) => Var -> Type -> m a -> m a
extendVarCtx x τ = local (\ c -> c { coreCtxV = M.insert x τ (coreCtxV c) } )
  
