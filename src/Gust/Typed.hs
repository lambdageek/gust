{-#
  LANGUAGE
    DeriveFunctor
  , DeriveDataTypeable
  , DeriveTraversable
  , DeriveFoldable
  #-}
module Gust.Typed where

import Control.Lens

import Data.Foldable (Foldable)

import Gust.Type
import Gust.AST (Meta(..), mMeta)

-- | A value paired with a type.
data Typed a = !a :-: !Type
  deriving (Eq, Show, Functor, Foldable, Traversable)

infix 2 :-:

class HasTy t where
  ty :: Lens' t Type

instance HasTy Type where
  ty = id
  
instance HasTy (Typed c) where
  ty = lens (\(_ :-: t) -> t) (\(a :-: _) t -> a :-: t)

instance HasTy c => HasTy (Meta t c) where
  ty = mMeta . ty

instance HasTy c => HasTy (a, c) where
  ty = _2 . ty
  
