{-#
  LANGUAGE
    DeriveFunctor
  , DeriveDataTypeable
  , DeriveFoldable
  , DeriveTraversable
  , FlexibleContexts
  , ScopedTypeVariables
  , StandaloneDeriving
  , TemplateHaskell
  #-}
module Gust.AST where

import Control.Lens
import Data.Data (Data)
import Data.Foldable (Foldable)
import Data.Typeable (Typeable, Typeable1)
import qualified Data.Typeable as T

import Gust.Kind

data Meta f a =
  (:@:) {
    _mValue :: !(f a)
    , _mMeta :: !a
    }
  deriving (Functor, Foldable, Traversable, Data)

instance Show (f a) => Show (Meta f a) where
  showsPrec d (x :@: _) = showsPrec d x

instance (Typeable1 f) => Typeable1 (Meta f) where
  typeOf1 _ = T.mkTyConApp (T.mkTyCon3 "gust"
                            "Gust.AST"
                            "Meta")
              [ T.typeOf1 (undefined :: f a) ]

type Name = String

data Var =
  UserV  !Name
  | GenV !(Maybe Name) !Int
  deriving (Data, Typeable)

instance Show Var where
  showsPrec _ (UserV nm) = showString nm
  showsPrec _ (GenV (Just nm) i) = showString nm . shows i
  showsPrec _ (GenV Nothing i) = showString "G" . shows i

instance Eq Var where
  v1 == v2 = compare v1 v2 == EQ
  
instance Ord Var where
  (UserV nm1) `compare` (UserV nm2) = nm1 `compare` nm2
  (GenV _ i1) `compare` (GenV _ i2) = i1 `compare` i2
  (UserV _  ) `compare` (GenV _  _) = LT
  (GenV  _ _) `compare` (UserV _  ) = GT

-- | syntactic types
data SType' a =
  AppST     !Name ![SType a]
  | BoxST   !(SType a)
  | TupleST ![SType a]
  | FunST   ![TypeBinding] ![SType a] !(SType a)
  deriving (Functor, Foldable, Traversable, Data, Typeable, Show)

-- | A program is a sequence of decalarations
type Program a = [Decl a]

-- | A declaration declares either a term or a type
data Decl' a =
  TermD !Var !(TermDecl a)
  | AbstypeD !Name !TyBind
  deriving (Functor, Foldable, Traversable, Data, Typeable, Show)

-- | Term declarations
data TermDecl a =
  FunD !(FunDecl a)
  | ExternD !(SType a)
  deriving (Functor, Foldable, Traversable, Data, Typeable, Show)

-- | Function declarations
data FunDecl a =
  FunDecl {
    _fdTyArgs   :: ![TypeBinding]
    , _fdArgs   :: ![TermBinding a]
    , _fdResult :: !(SType a)
    , _fdBody   :: !(Expr a)
    }
  deriving (Functor, Foldable, Traversable, Data, Typeable, Show)
           
type TypeBinding = (Name, TyBind)
type TermBinding a = (Var, SType a)

-- | Expressions
data Expr' a =
  -- | Variables
  VarE     !Var
  -- | Tuple introduction
  | TupleE ![Expr a]
  -- | Tuple projection
  | PrjE !(Expr a) !Nat
    -- | Polymorphic function application  e <tys> (es)  or e (es)
  | ApplyE !(Expr a) ![SType a] ![Expr a]
    -- | Type ascription  (e as t)
  | AscribeE !(Expr a) !(SType a)
    -- | compound expresions: let stmts in e
  | BlockE ![Stmt a] !(Expr a)
    deriving (Functor, Foldable, Traversable, Data, Typeable, Show)

-- | Statements
data Stmt' a =
  -- | Variable definition (scopes over the rest of the block)
  VarS !Var !(Expr a)
  deriving (Functor, Foldable, Traversable, Data, Typeable, Show)
 
type Decl     = Meta Decl'
type SType    = Meta SType'
type Expr     = Meta Expr'
type Stmt     = Meta Stmt'

makeLenses ''Meta
makeLenses ''FunDecl

