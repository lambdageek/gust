{-#
  LANGUAGE
    FlexibleContexts
  #-}
module Gust.LTI.Substitution where

import Control.Applicative
import Control.Lens
import Control.Monad.Error

import qualified Data.Map as Map

import qualified Unbound.LocallyNameless as U

import Gust.Type
import Gust.LTI.Constraint
import Gust.LTI.ConstraintMap
import Gust.LTI.CalculateVariance

newtype Substitution = Substitution { substitutionMap :: Map.Map TyName Type }
                       deriving Show

applySubstitution :: Substitution
                  -> Type
                  -> Type
applySubstitution sigma =
  U.substs (Map.toList $ substitutionMap sigma)

newtype SubstitutionError =
  SubstitutionError {substitutionErrorMsg :: String }
  deriving Show

instance Error SubstitutionError where
  strMsg = SubstitutionError

-- | principalSubstitution R C = σ where σ maps each x with C(x)=(L,U) to
-- either L or U depending on R's variance on x
principalSubstitution :: (Applicative m, MonadError SubstitutionError m)
                         => Type
                         -> ConstraintMap
                         -> m Substitution
principalSubstitution r =
  fmap Substitution . Map.traverseWithKey substitutionType . unConstraintMap
  where
    substitutionType x c = do
      when (unsatisfiable c) $
        unsatisfiableConstraintErr x c
      let
        l = c^.cnstrLower
        u = c^.cnstrUpper
      case varianceOf x r of
        ConstantVariance        -> return l
        Covariant               -> return l
        Contravariant           -> return u
        Invariant | l `U.aeq` u -> return $ c^.cnstrLower
                  | otherwise   -> invariantConstraintErr x r c

-- | anySatisfyingSubstitution C = σ where σ maps each x with C(x)=(L,U) to
-- some type T such that L ≤ T ≤ U
anySatisfyingSubstitution :: (Applicative m, MonadError SubstitutionError m)
                             => ConstraintMap -> m Substitution
anySatisfyingSubstitution =
  fmap Substitution . Map.traverseWithKey substitutionType . unConstraintMap
  where
    substitutionType x c = do
      when (unsatisfiable c) $
        unsatisfiableConstraintErr x c
      return $ c^.cnstrLower -- arbitrarily pick the lower bound
      
invariantConstraintErr :: MonadError SubstitutionError m
                          => TyName
                          -> Type
                          -> Constraint
                          -> m a
invariantConstraintErr x r c =
  throwError
  $ SubstitutionError ("the variable " ++ show x ++ " occurs invariantly in "
                       ++ show r ++ " but it is constrained by "
                       ++ show c
                       ++ " which has identical bounds."
                       ++ " Principal substitution doesn't exist.")

unsatisfiableConstraintErr :: MonadError SubstitutionError m
                              => TyName
                              -> Constraint
                              -> m a
unsatisfiableConstraintErr x c =
  throwError
  $ SubstitutionError ("the variable " ++ show x ++ " has an unsatisfiable constraint "
                       ++ show c)
