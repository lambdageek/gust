{-#
  LANGUAGE
    DeriveDataTypeable
  , DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  #-}
module Gust.Located where

import Data.Data (Data)
import Data.Foldable (Foldable)
import Data.Function (on)
import Data.Traversable (Traversable)
import Data.Typeable (Typeable)

class HasLocation a where
  extractLocation :: a -> Location

data Location = Location !FilePath !Int !Int !Int !Int
              deriving (Eq, Ord, Data, Typeable)

instance Show Location where
  showsPrec _ (Location p l1 c1 l2 c2) =
    showString p . showString ":" . shows l1
    . if l2 == l1
      then showString ":"
           . shows c1 . showString "-" . shows c2
      else showString "-" . shows l2

instance HasLocation Location where
  extractLocation = id

data Located a =
  Located {
    locatedAt :: !Location
    , locatedVal :: !a
  }
  deriving (Show, Functor, Foldable, Traversable, Data, Typeable)

instance Eq a => Eq (Located a) where
  (==) = (==) `on` locatedVal

instance (Ord a) => Ord (Located a) where
  compare = compare `on` locatedVal

instance HasLocation (Located a) where
  extractLocation = locatedAt
