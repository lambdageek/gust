{-#
  LANGUAGE
    FlexibleContexts
  , ConstraintKinds
  , TemplateHaskell
  , RankNTypes
  #-}
module Gust.ElabType where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Error.Class
import Control.Lens

import qualified Data.Map as Map

import Data.Order

import qualified Gust.AST as S

import qualified Gust.Type as T
import Gust.Typed
import Gust.Kind

newtype TypeEnv = TypeEnv (Map.Map S.Name TyConBind)

makeIso ''TypeEnv

class HasTyEnv e where
  tyEnv :: Lens' e TypeEnv

instance HasTyEnv TypeEnv where
  tyEnv = id

extendTypeEnv :: HasTyEnv e => [(S.Name, TyConBind)] -> e -> e
extendTypeEnv xs = tyEnv . from typeEnv %~ Map.union (Map.fromList xs)

elab :: (MonadError String m, Show (syn c))
        => (syn c -> m (T.Type, syn (Typed c)))
        -> S.Meta syn c
        -> m (S.Meta syn (Typed c))
elab f (a S.:@: m) =
  (liftM (\(t, a') -> a' S.:@: (m :-: t)) (f a))
  `catchError` (\errMsg -> throwError $ errMsg ++ "\n  near " ++ show a)

type MonadElabTy r m = (Applicative m, HasTyEnv r , MonadReader r m,
                        MonadError String m)
     
(-:-) :: Monad m => t -> a -> m (t, a)
t -:- x = return $ (t, x)

elabTy :: MonadElabTy r m => S.SType c -> m (S.SType (Typed c))
elabTy = elab $ \t -> case t of
  S.TupleST ts -> do
    ts' <- traverse elabTy ts
    T.tupleT (ts' ^..folded.ty) -:- S.TupleST ts'
  S.TopST n -> do
    T.topT (KTy n)              -:- S.TopST n
  S.BoxST t1 -> do
    t1' <- elabTy t1
    T.boxT (t1'^.ty)            -:- S.BoxST t1'
  S.AppST tv tys -> do
    mtb <- view $ tyEnv . from typeEnv . at tv
    case mtb of
      Nothing -> throwError $ "unbound type variable " ++ show tv
      Just (AbsTB ks kout) -> do
        tys' <- traverse elabTy tys
        assertElab (length ks == length tys) ("type " ++ show tv
                                              ++ " applied to "
                                              ++ show (length ks)
                                              ++ " arguments, but got "
                                              ++ show (length tys))
        mapM_ (\(arg, k) ->
                assertElab (arg^.ty.T.tyKnd <=: k)
                (" expected " ++ show arg ++ " to have kind " ++ show k))
          (zip tys' ks)
        let
          targs' = tys'^..folded.ty
        T.varT tv kout targs'           -:- S.AppST tv tys'
  S.FunST tvks doms cod -> do
    let
      -- turn kinds into tycon bindings: v:Tk  becomes v:<>Tk
      tvcs = map (\(v,k) -> (v, AbsTB [] k)) tvks
    (doms', cod') <- local (extendTypeEnv tvcs) $ do
      (,) <$> traverse elabTy doms <*> elabTy cod
    T.funT tvks (doms'^..folded.ty) (cod'^.ty)
                                -:- S.FunST tvks doms' cod'

bug :: MonadError String m => String -> m a
bug = throwError

assertElab :: MonadError String m => Bool -> String -> m ()
assertElab cond msg =
  if cond then return ()
  else throwError $ "ElaborationError: " ++ msg
