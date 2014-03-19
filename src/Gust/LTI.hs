{-#
  LANGUAGE
    FlexibleContexts
  #-}
module Gust.LTI (principalSubstitution,
                 TypeInferenceError(..),
                 ConstraintError(..),
                 Subst.SubstitutionError(..),
                 Subst.Substitution(..)) where

import Control.Monad.Error
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Set as Set

import Unbound.LocallyNameless as U

import Gust.Type

import Gust.LTI.GenerateConstraints
import qualified Gust.LTI.Substitution as Subst

data TypeInferenceError =
  ConstraintGenTIE ConstraintError
  | SubstitutionTIE Subst.SubstitutionError
    deriving Show

principalSubstitution :: MonadError TypeInferenceError m
                         => ([TyName], ArrowType)
                         -> [Type]
                         -> m Subst.Substitution
principalSubstitution (tvs, funTy) ss = let
  ts = arrDom funTy
  r = arrCod funTy
  genCnstr = liftM mconcat $ zipWithM generateConstraints ss ts
  env = ConstraintEnv mempty (Set.fromList tvs)
  in case U.runLFreshM $ runErrorT $ runReaderT genCnstr env of
    Left err -> throwError (ConstraintGenTIE err)
    Right constraint ->
      case Subst.principalSubstitution r constraint of
        Left err -> throwError (SubstitutionTIE err)
        Right ok -> return ok
  
                                
