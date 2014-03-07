{-#
  LANGUAGE
    FlexibleInstances
  , FlexibleContexts
  , TemplateHaskell
  , MultiParamTypeClasses
  , UndecidableInstances
  #-}
module Gust.Type where

import Generics.RepLib.R
import qualified Unbound.LocallyNameless as U

import Gust.Kind

type TyName = U.Name Type

data Type =
  VarT TyName
  | TopT Kind
  | BotT
  | TupleT ![Type]
  | FunT (U.Bind [(TyName, Kind)] ArrowType)
    deriving (Show)

data ArrowType =
  ArrowType {
    arrDom :: [Type]
    , arrCod :: Type
    }
  deriving (Show)
           
-- derive the RepLib representations
U.derive [''Type, ''ArrowType]

instance U.Alpha Type

instance U.Alpha ArrowType

instance U.Subst Type Type where
  isvar (VarT nm) = Just $ U.SubstName nm
  isvar _ = Nothing

-- there are no variable occurrences directly in ArrowType or in Kinds
instance U.Subst Type ArrowType

instance U.Subst Type Kind
