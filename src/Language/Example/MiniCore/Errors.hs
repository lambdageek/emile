-- | Static semantics errors
module Language.Example.MiniCore.Errors where

import Control.Monad.Except

import Language.Common.Label
import Language.Example.MiniCore.Syntax

data TypeSpine =
  ForallSp
  | FunctionSp
  | ProductSp
  | SigmaSp
  deriving Show

data CoreErr =
  ExpectedTypeExpr TypeSpine Expr
  | ExpectedFnType Type
  | ExpectedEquivTypes Type Type
  | ExpectedEquivKinds Kind Kind
  | UnboundVar Var
  | UnboundTyVar TyVar
  | UnknownFieldProj [(Label, Type)] Label
  | TyVarOccursInType TyVar Type
  deriving Show


raiseExpectedFn :: MonadError CoreErr m => Expr -> m a
raiseExpectedFn = throwError . ExpectedTypeExpr FunctionSp

raiseExpectedForall :: MonadError CoreErr m => Expr -> m a
raiseExpectedForall = throwError . ExpectedTypeExpr ForallSp

raiseExpectedProduct :: MonadError CoreErr m => Expr -> m a
raiseExpectedProduct = throwError . ExpectedTypeExpr ProductSp

raiseExpectedSigma :: MonadError CoreErr m => Expr -> m a
raiseExpectedSigma = throwError . ExpectedTypeExpr SigmaSp

raiseExpectedFnKind :: MonadError CoreErr m => Type -> m a
raiseExpectedFnKind = throwError . ExpectedFnType

raiseExpectedEqTy :: MonadError CoreErr m => Type -> Type -> m a
raiseExpectedEqTy τ = throwError . ExpectedEquivTypes τ

raiseExpectedEqK :: MonadError CoreErr m => Kind -> Kind -> m a
raiseExpectedEqK κ = throwError . ExpectedEquivKinds κ

raiseUnboundVar :: MonadError CoreErr m => Var -> m a
raiseUnboundVar = throwError . UnboundVar

raiseUnboundTyVar :: MonadError CoreErr m => TyVar -> m a
raiseUnboundTyVar = throwError . UnboundTyVar

raiseUnknownFieldProj :: MonadError CoreErr m => [(Label, Type)] -> Label -> m a
raiseUnknownFieldProj lτs = throwError . UnknownFieldProj lτs

raiseTyVarOccursInType :: MonadError CoreErr m => TyVar -> Type -> m a
raiseTyVarOccursInType α = throwError . TyVarOccursInType α
