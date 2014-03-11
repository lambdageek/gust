{-# LANGUAGE PatternGuards #-}
module Data.Order where

import Control.Applicative
import Control.Monad
import Data.Monoid

-- | A direction gives the intended subtyping ordering direction:
--   LT means a subtype is expected (or compute a meet), GT means a
--   supertype is expected (or compute a join), and EQ means that
--   equivalent types are expected (or compute a unification)
type Direction = Ordering

-- | Flip the direction
invertDirection :: Direction -> Direction
invertDirection LT = GT
invertDirection EQ = EQ
invertDirection GT = LT

-- | A class for preorders:
class Preorder a where
  -- | less than or equivalent to
  (<=:) :: a -> a -> Bool
  -- | equivalent to
  (~:)  :: a -> a -> Bool
  -- | strictly less than (lte but not equivalent)
  (<:)  :: a -> a -> Bool
  -- | meet
  (/\?) :: a -> a -> Maybe a
  -- | join
  (\/?) :: a -> a -> Maybe a
  -- | "unify" (choose a canonical element when two elements are
  --   equivalent)
  (~~?) :: a -> a -> Maybe a
  --
  a <: b   = a <=: b && not (b <=: a)
  a ~: b   = a <=: b && b <=: a
  a ~~? b
    | Just mt <- a /\? b
    , Just jn <- a \/? b
    , mt ~: jn                  = Just jn
    | otherwise                 = Nothing
  --
  -- | Compare two preorder elements in the given direction
  preorderCompare :: Direction -> a -> a -> Bool
  preorderCompare LT = (<=:)
  preorderCompare GT = (>=:)
  preorderCompare EQ = (~:)
  --
  -- | Combine (meet, join, or unify) two preorder elements in the
  --   given direction
  preorderCombine :: Direction -> a -> a -> Maybe a
  preorderCombine LT = (/\?)
  preorderCombine GT = (\/?)
  preorderCombine EQ = (~~?)

(>=:), (>:) :: Preorder a => a -> a -> Bool
(>=:) = flip (<=:)
(>:)  = flip (<:)

-- | Helper for defining (~~:) when the preorder is a partial order
unifyEqual :: Eq a => a -> a -> Maybe a
unifyEqual a b
  | a == b      = Just a
  | otherwise   = Nothing

infix 4 <=:, ~:, <:, >=:, >:
infixl 5 ~~?
infixl 6 \/?
infixl 7 /\?


instance Preorder a => Preorder (Dual a) where
  a \/? b = Dual <$> getDual a /\? getDual b
  a /\? b = Dual <$> getDual a \/? getDual b
  a ~~? b = Dual <$> getDual a ~~? getDual b
  a <=: b = getDual b <=: getDual a
  a  ~: b = getDual b  ~: getDual a
  a  <: b = getDual b  <: getDual a

instance (Preorder a, Preorder b) => Preorder (a, b) where
  (a,b) \/?  (a',b') = (,) <$> a\/?a' <*> b\/?b'
  (a,b) /\?  (a',b') = (,) <$> a/\?a' <*> b/\?b'
  (a,b) ~~?  (a',b') = (,) <$> a~~?a' <*> b~~?b'
  (a,b) <=:  (a',b') = a <=:  a' && b <=:  b'
  (a,b) ~:   (a',b') = a ~:   a' && b ~:   b'
  (a,b) <:   (a',b') = a <:   a' && b <:   b'

instance (Preorder a, Preorder b, Preorder c) => Preorder (a, b, c) where
  (a,b,c) \/?  (a',b',c') = (,,) <$> a\/?a' <*> b\/?b' <*> c\/?c'
  (a,b,c) /\?  (a',b',c') = (,,) <$> a/\?a' <*> b/\?b' <*> c/\?c'
  (a,b,c) ~~?  (a',b',c') = (,,) <$> a~~?a' <*> b~~?b' <*> c/\?c'
  (a,b,c) <=:  (a',b',c') = a <=:  a' && b <=:  b' && c <=:  c'
  (a,b,c) ~:   (a',b',c') = a ~:   a' && b ~:   b' && c ~:   c'
  (a,b,c) <:   (a',b',c') = a <:   a' && b <:   b' && c <:   c'

instance (Preorder a, Preorder b, Preorder c, Preorder d) =>
         Preorder (a, b, c, d) where
  (a,b,c,d) \/?  (a',b',c',d')
      = (,,,) <$> a\/?a' <*> b\/?b' <*> c\/?c' <*> d\/?d'
  (a,b,c,d) /\?  (a',b',c',d')
      = (,,,) <$> a/\?a' <*> b/\?b' <*> c/\?c' <*> d/\?d'
  (a,b,c,d) ~~?  (a',b',c',d')
      = (,,,) <$> a~~?a' <*> b~~?b' <*> c~~?c' <*> d~~?d'
  (a,b,c,d) <=:  (a',b',c',d') = (a,b) <=:  (a',b') && (c,d) <=:  (c',d')
  (a,b,c,d) ~:   (a',b',c',d') = (a,b) ~:   (a',b') && (c,d) ~:   (c',d')
  (a,b,c,d) <:   (a',b',c',d') = (a,b) <:   (a',b') && (c,d) <:   (c',d')

instance (Preorder a, Preorder b, Preorder c, Preorder d, Preorder e) =>
         Preorder (a, b, c, d, e) where
  (a,b,c,d,e) \/?  (a',b',c',d',e')
      = (,,,,) <$> a\/?a' <*> b\/?b' <*> c\/?c' <*> d\/?d' <*> e \/? e'
  (a,b,c,d,e) /\?  (a',b',c',d',e')
      = (,,,,) <$> a/\?a' <*> b/\?b' <*> c/\?c' <*> d/\?d' <*> e /\? e'
  (a,b,c,d,e) ~~?  (a',b',c',d',e')
      = (,,,,) <$> a~~?a' <*> b~~?b' <*> c~~?c' <*> d~~?d' <*> e ~~? e'
  (a,b,c,d,e) <=:  (a',b',c',d',e')
      = (a,b) <=:  (a',b') && (c,d,e) <=:  (c',d',e')
  (a,b,c,d,e) ~:   (a',b',c',d',e')
      = (a,b) ~:   (a',b') && (c,d,e) ~:   (c',d',e')
  (a,b,c,d,e) <:   (a',b',c',d',e')
      = (a,b) <:   (a',b') && (c,d,e) <:   (c',d',e')

instance (Preorder a, Preorder b) => Preorder (Either a b) where
  Left a  \/?  Left a'   = Left  <$> a \/? a'
  Right b \/?  Right b'  = Right <$> b \/? b'
  _       \/?  _         = mzero
  Left a  /\?  Left a'   = Left  <$> a /\? a'
  Right b /\?  Right b'  = Right <$> b /\? b'
  _       /\?  _         = mzero
  Left a  ~~?  Left a'   = Left  <$> a ~~? a'
  Right b ~~?  Right b'  = Right <$> b ~~? b'
  _       ~~?  _         = mzero
  Left a  <=:  Left a'   = a <=: a'
  Right b <=:  Right b'  = b <=: b'
  _       <=:  _         = False
  Left a  ~:   Left a'   = a ~: a'
  Right b ~:   Right b'  = b ~: b'
  _       ~:   _         = False
  Left a  <:   Left a'   = a <: a'
  Right b <:   Right b'  = b <: b'
  _       <:   _         = False
