{-#
  LANGUAGE
    FlexibleContexts
  , TemplateHaskell
  #-}
module Gust.ElabType where

import Control.Applicative
import Control.Monad.Reader.Class
import Control.Monad.Error.Class
import Control.Lens

import qualified Data.Map as Map

import qualified Unbound.LocallyNameless as U

import qualified Gust.AST as S

import qualified Gust.Type as T
import Gust.Typed
import Gust.Kind

newtype TyEnv = TyEnv (Map.Map S.Name TyBind)

data TyBind =
  AbsTB [Kind] Kind 

makeIso ''TyEnv

elab :: Functor f => (syn c -> f (T.Type, syn (Typed c))) -> S.Meta syn c -> f (S.Meta syn (Typed c))
elab f (a S.:@: m) =
  (\(t, a') -> a' S.:@: (m :-: t)) <$> f a

class (Applicative m, MonadReader TyEnv m, MonadError String m) => MonadElabTy m where
     
(-:-) :: Monad m => t -> a -> m (t, a)
t -:- x = return $ (t, x)

elabTy :: MonadElabTy m => S.SType c -> m (S.SType (Typed c))
elabTy = elab $ \t -> case t of
  S.TupleST ts -> do
    ts' <- traverse elabTy ts
    T.TupleT (ts' ^..folded.ty) -:- S.TupleST ts'
  S.AppST tv tys -> do
    mtb <- view $ from tyEnv . at tv
    case mtb of
      Nothing -> throwError $ "unbound type variable " ++ show tv
      Just (AbsTB ks _kout) | null ks && null tys ->
        T.VarT (U.s2n tv)  -:- S.AppST tv []
                            | otherwise ->
        bug "expected nullary tyvar applied to zero arguments"
  S.FunST tvks doms cod -> do
    let newBs = Map.fromList $ map (\(v,k) -> (v, AbsTB [] k)) tvks
    (doms', cod') <- local (from tyEnv %~ Map.union newBs) $ do
      (,) <$> traverse elabTy doms <*> elabTy cod
    T.FunT (U.bind (map (\(v,k) -> (U.s2n v, k)) tvks)
            $ T.ArrowType (doms'^..folded.ty) (cod'^.ty))
                           -:- S.FunST tvks doms' cod'

bug :: MonadError String m => String -> m a
bug = throwError