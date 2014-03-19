module Gust.LTI.ConstraintMap where

import Control.Lens
import Data.Monoid
import qualified Data.Map as Map

import Data.Order

import Gust.Type

import Gust.LTI.Constraint

-- | pointwise constraint map: { x ↦ C } (semantically, if C=(L,U)
-- then L ≤ x ≤ U)
newtype ConstraintMap =
  ConstraintMap { unConstraintMap :: Map.Map TyName Constraint }

instance Monoid ConstraintMap where
  mempty = ConstraintMap mempty
  mappend c1 c2 =
    ConstraintMap
    $ Map.unionWith (/\) (unConstraintMap c1) (unConstraintMap c2)
  mconcat cs = ConstraintMap $ Map.unionsWith (/\) $ map unConstraintMap cs

boundedBelow :: TyName -> Type -> ConstraintMap
boundedBelow v l =
  ConstraintMap $ Map.singleton v (Constraint l (topT $ l^.tyKnd))

boundedAbove :: TyName -> Type -> ConstraintMap
boundedAbove v u = ConstraintMap $ Map.singleton v (Constraint botT u)
