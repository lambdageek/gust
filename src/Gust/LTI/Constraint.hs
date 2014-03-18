{-#
  LANGUAGE
    TemplateHaskell
  #-}
module Gust.LTI.Constraint where

import Control.Lens
import Control.Applicative

import Data.Order

import Gust.Type

data Constraint =
  Constraint {
    _cnstrLower :: !Type
    , _cnstrUpper :: !Type
    }
  deriving (Show)

makeLenses ''Constraint

instance Preorder Constraint where
  c1 <=: c2 =
    c2^.cnstrLower <=: c1^.cnstrLower
    && c1^.cnstrUpper <=: c2^.cnstrUpper

  c1 /\? c2 =
    Constraint
    <$> (c1^.cnstrLower \/? c2^.cnstrLower)
    <*> (c1^.cnstrUpper /\? c2^.cnstrUpper)

  c1 \/? c2 =
    Constraint
    <$> (c1^.cnstrLower /\? c2^.cnstrLower)
    <*> (c1^.cnstrUpper \/? c2^.cnstrUpper)
