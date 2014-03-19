{-#
  LANGUAGE
    TemplateHaskell
  #-}
module Gust.LTI.Constraint where

import Control.Lens
import Control.Applicative

import Data.Maybe (fromMaybe)

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

unsatisfiable :: Constraint -> Bool
unsatisfiable c = not (c^.cnstrLower <=: c^.cnstrUpper)

instance Lattice Constraint where
  c1 /\ c2 = 
    let t = topT (c1^.cnstrUpper^.tyKnd)
    in fromMaybe (Constraint t botT) $ c1 /\? c2
  c1 \/ c2 =
    let t = topT (c1^.cnstrUpper^.tyKnd)
    in fromMaybe (Constraint t botT) $ c1 \/? c2
