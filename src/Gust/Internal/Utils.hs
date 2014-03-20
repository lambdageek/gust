module Gust.Internal.Utils where

import qualified Data.Set as Set

(∈) :: Ord a => a -> Set.Set a -> Bool
(∈) = Set.member

