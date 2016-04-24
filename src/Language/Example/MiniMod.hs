{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Example.MiniMod (
  module Language.OIL.Syntax
  , module Language.Example.MiniCore
  , module Language.Example.MiniMod
  , s2n
  ) where

import Control.Monad.Trans.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader
import Control.Monad.Error.Class
import Control.Monad.Trans.Except

import Unbound.Generics.LocallyNameless

import qualified Language.SIL.Syntax as SIL

import Language.OIL.Syntax
import Language.OIL.Elaborate

import Language.Example.MiniCore
import Language.Example.MiniCore.Syntax
import Language.Example.MiniCore.Errors
import Language.Example.MiniCore.Context


type MiniM = ExceptT CoreErr (ReaderT CoreCtx FreshM)

newtype M a = M { unM :: ReaderT (Ctx MiniSIL) (ExceptT (Err MiniSIL) MiniM) a }
  deriving (Functor, Monad, Applicative, MonadReader (Ctx MiniSIL), MonadError (Err MiniSIL), Fresh)

instance MonadElab M MiniSIL where
  inferTy = liftMini . inferCoreType
  inferKind = liftMini . inferCoreKind

type BigErr = Either CoreErr (Err MiniSIL)

liftMini :: MiniM a -> M a
liftMini = M . lift . lift
            
runM :: M a -> Either BigErr a
runM (M comp) = reassoc (runFreshM (runReaderT (runExceptT $ runExceptT (runReaderT comp emptyBigCtx)) emptySmallCtx))
  where
    reassoc :: Either a (Either b c) -> Either (Either a b) c
    reassoc (Left a) = Left (Left a)
    reassoc (Right (Left b)) = Left (Right b)
    reassoc (Right (Right b)) = Right b
    emptySmallCtx = coreNilCtx
    emptyBigCtx = nilElabCtx


c :: MExpr MiniSIL -> M (SIL.Mod MiniSIL, SIL.TyVarBinds MiniSIL, SIL.Σ MiniSIL)
c = elaborateME'


m1 :: MExpr MiniSIL
m1 = LitME $ bind bs ()
  where
    bs = NilMB

-- Try:
-- > runM (c m1)

m2 :: MExpr MiniSIL
m2 = LitME $ bind b1 ()
  where
    unit = (embed (Field "unit"), s2n "unit")
    b1 = AtomicMB $ Provide unit (embed $ ValAB $ TupleE [])

m3 :: MExpr MiniSIL
m3 = LitME $ bind b1 ()
  where
    ty = (embed (Field "T"), s2n "T")
    b1 = AtomicMB $ Provide ty (embed $ TypeAB $ ProdT [])
