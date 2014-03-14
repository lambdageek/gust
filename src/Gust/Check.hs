{-#
  LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , ScopedTypeVariables
  , TemplateHaskell
  #-}
module Gust.Check where

import Prelude hiding (sequence, mapM)

import Control.Applicative
import Control.Arrow (first, second)
import Control.Lens
import Control.Monad.Error hiding (sequence, mapM)
import Control.Monad.Reader hiding (sequence, mapM)
import Data.Monoid
import qualified Data.Map as Map
import Data.Traversable

import Data.Order

import Gust.AST
import Gust.Type
import Gust.Typed

import Gust.ElabType

newtype TermEnv = TermEnv {unTermEnv :: Map.Map Var Type }

termEnvMapping :: Iso' TermEnv (Map.Map Var Type)
termEnvMapping = iso unTermEnv TermEnv

data ElabEnv =
  ElabEnv {
    _eeTyEnv :: TypeEnv
    , _eeTmEnv :: TermEnv
    }

makeLenses ''ElabEnv

instance HasTyEnv ElabEnv where
  tyEnv = eeTyEnv


extendTermEnv :: [(Var, Type)] -> ElabEnv -> ElabEnv
extendTermEnv xs = eeTmEnv.termEnvMapping %~ mappend (Map.fromList xs)

type MonadElaborate m =
  (Applicative m, MonadReader ElabEnv m
  , MonadError String m)

elabVar :: MonadElaborate m
           => Maybe Type
           -> Var
           -> m (Var, Type)
elabVar meTy v = do
  mty <- view $ eeTmEnv.termEnvMapping.at v
  case (mty, meTy) of
    (Just aTy, Just eTy) -> do
      assertTypeRel (<=:) aTy " a subtype of " eTy
      return (v, aTy)
    (Just aTy, Nothing) -> return (v, aTy)
    _ -> typeError v " not in scope"

elabExpr :: MonadElaborate m
           => Maybe Type
           -> Expr a
           -> m (Expr (Typed a))
elabExpr meTy = elab $ \e -> case e of
  VarE v -> do
    (v, ty) <- elabVar meTy v
    ty                                  -:- VarE v
  _ -> undefined

elaborateFunDecl :: forall m a . MonadElaborate m
                    => FunDecl a
                    -> m (Type, FunDecl (Typed a))
elaborateFunDecl funDecl = 
  local (extendTypeEnv $ funDecl^.fdTyArgs) $ do
    args' <- funDecl^!!fdArgs.folded.alongside id (act elabTy)
    result' <- elabTy (funDecl^.fdResult)
    local (extendTermEnv (args' & traverse._2 %~ view ty)) $ do
      e' <- elabExpr (Just $ result'^.ty) (funDecl^.fdBody)
      let
        t = funT (funDecl^.fdTyArgs) (args'^..folded._2.ty) (result'^.ty)
      t                                 -:- FunDecl { _fdTyArgs =
                                                         funDecl^.fdTyArgs
                                                    , _fdArgs = args'
                                                    , _fdResult = result'
                                                    , _fdBody = e'
                                                    }
    

elaborateTermDecl :: MonadElaborate m
                     => TermDecl a
                     -> m (Type, TermDecl (Typed a))
elaborateTermDecl (FunD fd) = second FunD <$> (elaborateFunDecl fd)

elaborateDecl :: MonadElaborate m
                 => Decl a
                 -> m (Decl (Typed a))
elaborateDecl = elab $ \d -> case d of
  TermD v td -> do
    (tp, td') <- elaborateTermDecl td
    tp                                  -:- TermD v td'
  AbstypeD _n _k -> undefined

elaborateProgram :: MonadElaborate m
                    => [Decl a]
                    -> m [Decl (Typed a)]
elaborateProgram = mapM elaborateDecl

assertTypeRel :: MonadError String m =>
                 (Type -> Type -> Bool) -> Type -> String -> Type -> m ()
assertTypeRel relTo t1 relationship t2 =
  if t1 `relTo` t2 then return () else typeError t1 (" was not "
                                                     ++ relationship ++ show t2)

typeError :: (Show a, MonadError String m) =>
             a -> String -> m b
typeError what msg = throwError $ "Type Error: " ++ show what ++ msg
             
