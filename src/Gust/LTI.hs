{-#
  LANGUAGE
    FlexibleContexts
  #-}
module Gust.LTI (principalSubstitution,
                 anySatisfyingSubstitution,
                 TypeInferenceError(..),
                 ConstraintError(..),
                 Subst.SubstitutionError(..),
                 Subst.Substitution(..),
                 Subst.applySubstitution) where

import Control.Monad.Error
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Set as Set

import Unbound.LocallyNameless as U

import Gust.Type

import Gust.LTI.ConstraintMap
import Gust.LTI.GenerateConstraints
import qualified Gust.LTI.Substitution as Subst

data TypeInferenceError =
  ConstraintGenTIE ConstraintError
  | SubstitutionTIE Subst.SubstitutionError
  | FailTIE String
    deriving Show

instance Error TypeInferenceError where
  strMsg = FailTIE

-- | Construct the constraint map corresponding to the
-- subtyping problem:  ⊢αs σs→τ ≤ Ss->T ⇒ C
-- (when the expected result type is available)
-- or the problem: ⊢αs Ss ≤ σs ⇒ C
-- (when it isnt)
makeProblemConstraints :: (U.LFresh m,
                           MonadError ConstraintError m,
                           MonadReader ConstraintEnv m)
                          => ArrowType  -- ^ function params and result
                          -> [Type]     -- ^ function actual args
                          -> Maybe Type -- ^ (optional) expected result type
                          -> m ConstraintMap
makeProblemConstraints funTy args mRes = let
  ts = arrDom funTy
  r = arrCod funTy
  genCnstrDom = liftM mconcat $ zipWithM generateConstraints args ts
  genCnstrCod = case mRes of
    Just res -> generateConstraints r res
    Nothing -> return mempty
  in liftM2 mappend genCnstrDom genCnstrCod

solveConstraints ::
  MonadError TypeInferenceError m
  => ReaderT ConstraintEnv (ErrorT ConstraintError U.LFreshM) ConstraintMap
  -> ConstraintEnv 
  -> (ConstraintMap -> Either Subst.SubstitutionError Subst.Substitution)
  -> m Subst.Substitution
solveConstraints genCnstr env buildSubst =
  case U.runLFreshM $ runErrorT $ runReaderT genCnstr env of
    Left err -> throwError (ConstraintGenTIE err)
    Right constraint ->
      case buildSubst constraint of
        Left err -> throwError (SubstitutionTIE err)
        Right ok -> return ok

principalSubstitution :: MonadError TypeInferenceError m
                         => [TyName]
                         -> ArrowType
                         -> [Type]
                         -> m Subst.Substitution
principalSubstitution tvs funTy args = let
  r = arrCod funTy
  genCnstr = makeProblemConstraints funTy args Nothing
  env = ConstraintEnv mempty (Set.fromList tvs)
  in solveConstraints genCnstr env (Subst.principalSubstitution r)

anySatisfyingSubstitution :: MonadError TypeInferenceError m
                             => [TyName]
                             -> ArrowType
                             -> [Type]
                             -> Type
                             -> m Subst.Substitution
anySatisfyingSubstitution tvs funTy args res = let
  genCnstr = makeProblemConstraints funTy args (Just res)
  env = ConstraintEnv mempty (Set.fromList tvs)
  in solveConstraints genCnstr env Subst.anySatisfyingSubstitution
