{-#
  LANGUAGE
    DeriveDataTypeable
  , FlexibleInstances
  , FlexibleContexts
  , MultiParamTypeClasses
  , TemplateHaskell
  , UndecidableInstances
  #-}
module Gust.Kind where

import Data.Data (Data)
import Data.Typeable (Typeable)

import Generics.RepLib.R
import Generics.RepLib.Derive
import qualified Unbound.LocallyNameless as U

import Data.Order

type Nat = Int

-- | KTy n is the classifier of types of size n
data Kind = KTy !Nat
          deriving (Eq, Ord, Show, Data, Typeable)

-- | AbsTB ks k is an abstract type constructor binding of arity |ks|
data TyConBind = AbsTB ![Kind] !Kind
            deriving (Show, Data, Typeable)

derive [''Kind]

derive [''TyConBind]

instance U.Alpha Kind
instance U.Alpha TyConBind

instance Preorder Kind where
  KTy n <=: KTy m        = n == m
  KTy n /\? KTy m | n == m    = Just (KTy n)
                  | otherwise = Nothing
  
  KTy n \/? KTy m | n == m    = Just (KTy n)
                  | otherwise = Nothing


kSize :: Kind -> Nat
kSize (KTy n) = n
