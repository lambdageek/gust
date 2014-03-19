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
import Control.Lens
import Control.Monad.Error hiding (sequence, mapM)
import Control.Monad.Reader hiding (sequence, mapM)
import Data.Monoid
import qualified Data.Map as Map

import qualified Unbound.LocallyNameless as U

import Data.Order

import Gust.AST
import Gust.Type
import Gust.Typed
import Gust.Kind

import Gust.ElabType

import Gust.LTI

newtype TermEnv = TermEnv {unTermEnv :: Map.Map Var Type }

termEnvMapping :: Iso' TermEnv (Map.Map Var Type)
termEnvMapping = iso unTermEnv TermEnv

data ElabEnv =
  ElabEnv {
    _eeTyEnv :: TypeEnv
    , _eeTmEnv :: TermEnv
    }

emptyElabEnv :: ElabEnv
emptyElabEnv = ElabEnv {
  _eeTyEnv = mempty ^. typeEnv
  , _eeTmEnv = mempty ^. from termEnvMapping
  }
               
makeLenses ''ElabEnv

instance HasTyEnv ElabEnv where
  tyEnv = eeTyEnv


extendTermEnv :: [(Var, Type)] -> ElabEnv -> ElabEnv
extendTermEnv xs = eeTmEnv.termEnvMapping %~ mappend (Map.fromList xs)

type MonadElaborate m =
  (Applicative m, MonadReader ElabEnv m
  , MonadError String m, U.Fresh m)

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
    (v', t') <- elabVar meTy v
    t'                                  -:- VarE v'
  BlockE stmts e1 ->
    elabStmts stmts $ \stmts' -> do
      e1' <- elabExpr meTy e1
      let e' = BlockE stmts' e1'
          t' = (e1'^.ty)
      guardExpectedResult meTy e' t'
      t'                                -:- e'
  AscribeE e1 t1 -> do
    t1' <- elabTy t1
    e1' <- elabExpr (Just $ t1'^.ty) e1
    assertTypeRel (<=:) (e1'^.ty) "a subtype of ascribed type " (t1'^.ty)
    let e' = AscribeE e1' t1'
        t' = t1'^.ty
    guardExpectedResult meTy  e' t'
    t'                                  -:- e'
  ApplyE efun tyargs eargs -> do
    efun' <- elabExpr Nothing efun
    (bvs, arr) <- expectPolyFunType (efun'^.ty)
    if null bvs
      then do
      when (not $ null tyargs) $ do
        typeError efun' (" applied to " ++ show (length tyargs)
                         ++ " types, expected none")
      elabMonoApp meTy (ApplyE efun' []) arr eargs
      else elabPolyApp meTy efun' bvs arr tyargs eargs
  _ -> unimplemented $ show e

expectPolyFunType :: MonadElaborate m
                     => Type
                     -> m ([(TyName, TyBind)], ArrowType)
expectPolyFunType t =
  case t^.tyRep of
    FunT bnd -> U.unbind bnd
    _ -> typeError t " not a polymorphic function type"
      

elabMonoApp :: MonadElaborate m
               => Maybe Type
               -> ([Expr (Typed a)] -> Expr' (Typed a))
               -> ArrowType
               -> [Expr a]
               -> m (Type, Expr' (Typed a))
elabMonoApp meTy efunhead arr eargs = do
  unless (length (arrDom arr) == length eargs) $ do
    typeError eargs (" expected exactly "
                     ++ show (length $ arrDom arr) ++ " arguments")
  eargs' <- zipWithM (\argTy earg -> elabExpr (Just argTy) earg)
            (arrDom arr) eargs
  let
    e' = efunhead eargs'
    t' = arrCod arr
  guardExpectedResult meTy e' t'
  t'                                    -:- e'

guardExpectedResult :: MonadElaborate m
                       => Maybe Type
                       -> Expr' (Typed a)
                       -> Type
                       -> m ()
guardExpectedResult meTy e t =
  case meTy of
    Nothing -> return ()
    Just eTy -> assertTypeRel (<=:) t (" inferred type of "
                                       ++ show e ++ " is a subtype of ") eTy

elabPolyApp :: MonadElaborate m
               => Maybe Type
               -> Expr (Typed a)
               -> [(TyName, TyBind)]
               -> ArrowType
               -> [SType a]
               -> [Expr a]
               -> m (Type, Expr' (Typed a))
elabPolyApp meTy efun' bvs arr tyargs eargs =
  case (length bvs, length tyargs) of
    (nparams, nargs) | nparams == nargs -> do
      -- e<ts>(es) where e : ∀αs.τs→σ.  We typecheck es against
      -- τs[ts/αs] and give result σ[ts/αs]
      tyargs' <- traverse elabTy tyargs
      let
        substitution = zipWith (\(param, _) arg -> (param, arg^.ty)) bvs tyargs'
        arr' = U.substs substitution arr
      elabMonoApp meTy (ApplyE efun' tyargs') arr' eargs
                     | nparams > 0 && nargs == 0 -> do
      -- synthesize function arguments
      eargs' <- traverse (elabExpr Nothing) eargs
      -- infer omitted type args
      constrainedTypeInference meTy efun' bvs arr eargs'
                     | otherwise -> do
      typeError efun' $ " has "
        ++ show nparams ++ " type parameters, but was given "
        ++ show nargs ++ " actual type arguments"

constrainedTypeInference :: MonadElaborate m
                            => Maybe Type
                            -> Expr (Typed a)
                            -> [(TyName, TyBind)]
                            -> ArrowType
                            -> [Expr (Typed a)]
                            -> m (Type, Expr' (Typed a))
constrainedTypeInference meTy efun' bvs arr eargs' = do
  let
    tvs = map fst bvs
    ts = eargs'^..folded.ty
    msubst = case meTy of
      Just expectedType -> anySatisfyingSubstitution tvs arr ts expectedType
      Nothing -> principalSubstitution tvs arr ts
  sigma <- case msubst of
    Left err -> typeError efun' (show err)
    Right ok -> return $ applySubstitution ok

  let
    -- targs' = map (\(tv, AbsTB _ k) -> sigma (varT' tv k)) bvs
    -- TODO: want a place to hang the targs'

    t' = case meTy of
      Nothing -> sigma (arrCod arr)
      Just expectedType -> expectedType

  -- This next pair of checks isn't necessary if LTI is implemented
  -- correctly, but it brings piece of mind.
  mapM_ (\(e,t) -> assertTypeRel (<=:) (e^.ty) "a subtype of " t)
    $ zip eargs' (map sigma $ arrDom arr)
  assertTypeRel (<=:) (arrCod arr) "a subtype of" t'

  t'                                -:- ApplyE efun' [] eargs'

elabStmts :: MonadElaborate m
             => [Stmt a]
             -> ([Stmt (Typed a)] -> m b)
             -> m b
elabStmts [] kont = kont []
elabStmts (stmt:stmts) kont =
  elabStmt stmt $ \stmt' ->
  elabStmts stmts $ \stmts' ->
  kont (stmt':stmts')

elabStmt :: (MonadElaborate m)
            => Stmt a
            -> (Stmt (Typed a) -> m b)
            -> m b
elabStmt stmt0 = elabStmtCont stmt0 $ \stmt k ->
  case stmt of
    VarS v e -> do
      e' <- elabExpr Nothing e
      local (extendTermEnv [(v, e'^.ty)]) $ do
        k (VarS v e') (e'^.ty)

elabStmtCont :: MonadElaborate m
            => Stmt a
            -> (Stmt' a
                -> (Stmt' (Typed a) -> Type -> m b)
                -> m b)
            -> (Stmt (Typed a) -> m b)
            -> m b
elabStmtCont s0 kwrap kont =
  case s0 of
    (s :@: meta) -> kwrap s $ \ s' t ->
      kont (s' :@: (meta :-: t))

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
elaborateTermDecl td0 = case td0 of
  FunD fd -> do
    (t', fd') <- elaborateFunDecl fd
    t'                                  -:- FunD fd'
  ExternD t -> do
    t' <- elabTy t
    (t'^.ty)                            -:- ExternD t'

elaborateDecl :: MonadElaborate m
                 => Decl a
                 -> m (Decl (Typed a))
elaborateDecl = elab $ \d -> case d of
  TermD v td -> do
    (tp, td') <- elaborateTermDecl td
    tp                                  -:- TermD v td'
  AbstypeD n (AbsTB ta k) -> varT n k   -:- AbstypeD n (AbsTB ta k)

elaborateProgram :: MonadElaborate m
                    => [Decl a]
                    -> m [Decl (Typed a)]
elaborateProgram = let
  go [] k = k []
  go (d:ds) k = do
    d' <- elaborateDecl d
    local (extendElabEnv d') $ go ds $ \ds' -> k (d' : ds')
  in
   flip go return

extendElabEnv :: Decl (Typed a) -> ElabEnv -> ElabEnv
extendElabEnv d0 = case d0^.mValue of
  TermD v _td -> eeTmEnv . termEnvMapping %~ Map.insert v (d0^.ty)
  AbstypeD n tb -> eeTyEnv %~ extendTypeEnv [(n, tb)]

assertTypeRel :: MonadError String m =>
                 (Type -> Type -> Bool) -> Type -> String -> Type -> m ()
assertTypeRel relTo t1 relationship t2 =
  if t1 `relTo` t2 then return () else typeError t1 (" was not "
                                                     ++ relationship ++ show t2)

typeError :: (Show a, MonadError String m) =>
             a -> String -> m b
typeError what msg = throwError $ "Type Error: " ++ show what ++ " " ++ msg
             
unimplemented :: MonadError String m => String -> m a
unimplemented what = throwError $ "Unimplemented " ++ show what
