module Gust.LTI.CalculateVariance (
  Variance(..)
  , varianceOf
  , test_variance1
  ) where

import Control.Lens
import Control.Monad

import qualified Unbound.LocallyNameless as U

import Gust.Kind
import Gust.Type

import Data.Order


data Variance =
  ConstantVariance
  | Covariant
  | Contravariant
  | Invariant
    deriving (Show, Eq)
             
instance Preorder Variance where
  Invariant     <=: _                 = True
  _             <=: ConstantVariance  = True
  Covariant     <=: Covariant         = True
  Contravariant <=: Contravariant     = True
  _             <=: _                 = False

  var1 /\? var2 = Just (var1 /\ var2)
  var1 \/? var2 = Just (var1 \/ var2)

instance Lattice Variance where
  ConstantVariance /\ a                = a
  a                /\ ConstantVariance = a
  Invariant        /\ _                = Invariant
  _                /\ Invariant        = Invariant
  Covariant        /\ Covariant        = Covariant
  Covariant        /\ Contravariant    = Invariant
  Contravariant    /\ Covariant        = Invariant
  Contravariant    /\ Contravariant    = Contravariant
  
  Invariant        \/ a                = a
  a                \/ Invariant        = a
  ConstantVariance \/ _                = ConstantVariance
  _                \/ ConstantVariance = ConstantVariance
  Covariant        \/ Covariant        = Covariant
  Covariant        \/ Contravariant    = ConstantVariance
  Contravariant    \/ Covariant        = ConstantVariance
  Contravariant    \/ Contravariant    = Contravariant

varianceOf :: TyName -> Type -> Variance
varianceOf v = U.runLFreshM . calcVarianceOf v

-- | Calculate whether a type T is constant-, co-, contra-, or
-- invariant in a variable X.
calcVarianceOf :: U.LFresh m => TyName -> Type -> m Variance
calcVarianceOf v = let
  posVariance = varianceOf' Covariant posVariance negVariance v
  negVariance = varianceOf' Contravariant negVariance posVariance v
  in
   posVariance

varianceOf' :: U.LFresh m
               => Variance -- ^ variance for variable occurence
               -> (Type -> m Variance) -- ^ recurse on positive position
               -> (Type -> m Variance) -- ^ recurse on negative position
               -> TyName
               -> Type
               -> m Variance
varianceOf' varVariance posVarianceOf negVarianceOf v t =
  case t^.tyRep of
  VarT v' | v == v'   -> return varVariance
          | otherwise -> return ConstantVariance
  TopT                -> return ConstantVariance
  BotT                -> return ConstantVariance
  TupleT ts           ->
    -- tuples are covariant
    liftM (foldl (/\) ConstantVariance) $ mapM posVarianceOf ts
  BoxT _              -> return Invariant
  FunT bnd            -> U.lunbind bnd $ \(_, arr) -> do
    vardom <- liftM (foldl (/\) ConstantVariance)
              $ mapM negVarianceOf $ arrDom arr
    varcod <- posVarianceOf $ arrCod arr
    return $ vardom /\ varcod
  
test_variance1 :: [Variance]
test_variance1 = let
  x = varT "x" KTy
  y = varT "y" KTy

  t ~~> t' = funT [] [t] t'

  ty1 = x ~~> botT
  ty2 = botT ~~> x
  ty3 = x ~~> x
  ty4 = y ~~> y
  in
   map (\t -> varianceOf (U.s2n "x") t) [ty1, ty2, ty3, ty4]
