{-#
  LANGUAGE
    FlexibleContexts
  , TemplateHaskell
  #-}
module Gust.LTI.GenerateConstraints where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Error

import Data.Monoid
import qualified Data.Set as Set

import qualified Unbound.LocallyNameless as U

import Gust.Kind
import Gust.Type
import Gust.LTI.ConstraintMap
import Gust.LTI.Avoid (avoidUp, avoidDown, (∈), alsoAvoid)

data ConstraintEnv = ConstraintEnv {
  _cenvAvoid     :: Set.Set TyName -- ^ variables that must not occur
                                   -- in the generated constraints
  , _cenvUnknown :: Set.Set TyName -- ^ domain of the generated
                                   -- constraint map
  }

makeLenses ''ConstraintEnv

newtype ConstraintError = ConstraintError {constraintErrorMsg :: String }
                          deriving (Eq, Show)

instance Error ConstraintError where
  strMsg = ConstraintError

constraintErr :: MonadError ConstraintError m
                 => String
                 -> m a
constraintErr = throwError . ConstraintError

cannotSatisfyErr :: MonadError ConstraintError m
                    => Type -> Type -> m a
cannotSatisfyErr s t = constraintErr ("constraint " ++ show s ++ " <= " ++ show t ++ " is unsatisfiable")


-- | V ⊢ₓ S ≤ T ⇒ {x∈X ↦ C}
--
-- Where x∈X free in fv(S) or fv(T) but not both. And on output
-- (V∪X)∩fv(C)=∅
generateConstraints :: (U.LFresh m,
                        MonadError ConstraintError m,
                        MonadReader ConstraintEnv m)
                       => Type -- ^ lower bound
                       -> Type -- ^ upper bound
                       -> m ConstraintMap
generateConstraints s t = do
  xs <- view cenvUnknown
  case (s^.tyRep, t^.tyRep) of
    (BotT, _)                                       -> return mempty
    (_, TopT)                                       -> return mempty
    (VarT v, _) | v ∈ xs                            -> do
      vs <- view cenvAvoid
      liftM (boundedAbove v) (avoidDown vs t)
    (_, VarT v) | v ∈ xs                            -> do
      vs <- view cenvAvoid
      liftM (boundedBelow v) (avoidUp vs s)
    (VarT x, VarT y) | x == y {- && x ∉ xs -}       -> return mempty
    (TupleT ss, TupleT ts) | length ss == length ts ->
      liftM mconcat $ zipWithM generateConstraints ss ts
    (BoxT s1, BoxT t1)                              -> widthConstraint s1 t1
    (FunT bnd1, FunT bnd2)                          -> do
      mC <- U.lunbind2 bnd1 bnd2 (maybe (return Nothing) (liftM Just . generateConstraintArr))
      case mC of
        Just c                                      -> return c
        Nothing                                     -> cannotSatisfyErr s t
    _                                               -> cannotSatisfyErr s t


generateConstraintArr :: (U.LFresh m,
                          MonadError ConstraintError m,
                          MonadReader ConstraintEnv m)
                         => ([(TyName, TyBind)]
                            , ArrowType    
                            , a
                            , ArrowType)
                         -> m ConstraintMap
generateConstraintArr (bvs, arr1, _, arr2) =
  local (cenvAvoid %~ alsoAvoid bvs) $ do
    cnsDom <- liftM (mconcat)
              $ zipWithM generateConstraints (arrDom arr2) (arrDom arr1)
    cnsCod <- generateConstraints (arrCod arr1) (arrCod arr2)
    return $ cnsDom `mappend` cnsCod

widthConstraint :: (MonadError ConstraintError m)
                   => Type
                   -> Type
                   -> m ConstraintMap
widthConstraint s t =
  throwError $ ConstraintError ("unimplemented: width constraint "
                                ++ show s ++ " <=w " ++ show t)
