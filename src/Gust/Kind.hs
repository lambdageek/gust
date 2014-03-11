{-#
  LANGUAGE
    DeriveDataTypeable
  , FlexibleInstances
  , FlexibleContexts
  , MultiParamTypeClasses
  , TemplateHaskell
  #-}
module Gust.Kind where

import Data.Data (Data)
import Data.Typeable (Typeable)

import Generics.RepLib.R
import Generics.RepLib.Derive
import qualified Unbound.LocallyNameless as U

import Data.Order

data Kind = KTy
          deriving (Eq, Ord, Show, Data, Typeable)

derive [''Kind]

instance U.Alpha Kind

instance Preorder Kind where
  KTy <=: _       = True
  KTy /\? _       = Just KTy
  KTy \/? _       = Just KTy
