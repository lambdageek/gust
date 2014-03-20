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
    (VarT v, _) | v ∈ xs && s^.tyKnd == t^.tyKnd    -> do
      vs <- view cenvAvoid
      liftM (boundedAbove v) (avoidDown vs t)
    (_, VarT v) | v ∈ xs && s^.tyKnd == t^.tyKnd    -> do
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


-- | Generate constraint for V⊢ₓ (Ss₁→T₁)≤(Ss₂→T₂) ⇒ Cs∧D
-- where V⊢ₓ Ss₂≤Ss₁ ⇒ Cs   and V⊢ₓ T₁≤T₂ ⇒ D
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

-- | Generate constraints C for the problem V⊢ₓ S ≤w T ⇒ C
--
-- There is a  slightly tricky case here that we punt on.
-- Consider  V⊢ₓ S ≤w Y (and the symmetric case with an upper bound)
-- where Y∈X is one of the unknowns that we're trying
-- to solve for.  In that case we want to kick out a constraint:
--   {S ≤w Y ≤w ⊤wk}
-- (where ⊤wk is the top for width subtyping for the kind k of Y)
-- but we dont' have width constraints.  So instead we kick out the constraint
--   {S ≤ Y ≤ S}
-- which is wrong, but maybe the additional expressive power isn't useful?
widthConstraint :: (U.LFresh m,
                    MonadError ConstraintError m,
                    MonadReader ConstraintEnv m)
                   => Type
                   -> Type
                   -> m ConstraintMap
widthConstraint s t = do
  -- xs <- view cenvUnknown
  case (s^.tyRep, t^.tyRep) of
    (TupleT ts1, TupleT ts2) ->
      if length ts1 >= length ts2
      then liftM mconcat $ zipWithM depthEquivConstraint ts1 ts2
      else depthEquivConstraint s t
    -- (VarT v, TupleT ts2) | v ∈ xs -> omitted, falling through. see comment
    -- (TupleT ts1, VarT v) | v ∈ xs -> omitted, falling through. see comment
    (_, _) -> depthEquivConstraint s t

-- | Generate equivalence constraint:  V⊢ₓ S≡T ⇒ C∧D
--  where V⊢ₓ S≤T ⇒ C  and V⊢ₓ T≤S ⇒ D
depthEquivConstraint :: (U.LFresh m,
                         MonadError ConstraintError m,
                         MonadReader ConstraintEnv m)
                        => Type
                        -> Type
                        -> m ConstraintMap
depthEquivConstraint s t =
  liftM2 mappend (generateConstraints s t) (generateConstraints t s)
