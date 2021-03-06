{-#
  LANGUAGE
    DeriveDataTypeable
  , FlexibleInstances
  , FlexibleContexts
  , TemplateHaskell
  , MultiParamTypeClasses
  , UndecidableInstances
  #-}
module Gust.Type where

import Prelude hiding (sequence)

import Control.Arrow (first)
import Control.Lens
import Control.Monad hiding (sequence)
import Data.Maybe (isJust)
import Data.Traversable (sequence)

import Generics.RepLib.R hiding (to)
import qualified Unbound.LocallyNameless as U
import qualified Unbound.LocallyNameless.Subst as U

import Data.Order

import Gust.Kind
import qualified Gust.AST as S

type TyName = U.Name Type

data Type' =
  VarT TyName ![Type] -- invariant: fully applied tyvar
  | TopT
  | BotT
  | BoxT !Type
  | TupleT ![Type]
  | FunT (U.Bind [(TyName, Kind)] ArrowType)
    deriving (Show)

data ArrowType =
  ArrowType {
    arrDom :: [Type]
    , arrCod :: Type
    }
  deriving (Show)

data Type = Type {
  _tyRep :: Type'
  , _tyKnd :: Kind
  }
  deriving (Show)

makeLenses ''Type
           
-- derive the RepLib representations
U.derive [''Type, ''Type', ''ArrowType]

instance U.Alpha Type

instance U.Alpha Type'

instance U.Alpha ArrowType

instance U.Subst Type Type' where
  -- only 0-arg variables are variables, if there are more, it's a
  -- type constructor application which we don't currently substitute for.
  isCoerceVar (VarT nm [])     = Just $ U.SubstCoerce nm (\b -> Just $ b^.tyRep)
  isCoerceVar (VarT _nm (_:_)) = Nothing
  isCoerceVar _                = Nothing

-- there are no variable occurrences directly in ArrowType or in Kinds
instance U.Subst Type ArrowType

instance U.Subst Type Kind
instance U.Subst Type TyConBind

instance U.Subst Type Type


instance Eq Type where
  (==) = U.aeq

tupleT :: [Type] -> Type
tupleT ts = Type {
  _tyRep = TupleT ts
  , _tyKnd = KTy (sumOf (folded . tyKnd . to kSize) ts)
  }

boxT :: Type -> Type
boxT t = Type { _tyRep = BoxT t, _tyKnd = KTy 1 }

topT :: Kind -> Type
topT k = Type {
  _tyRep = TopT
  , _tyKnd = k
  }

botT :: Type
botT = Type { _tyRep = BotT, _tyKnd = KTy 0}

varT :: S.Name -> Kind -> [Type] -> Type
varT s = varT' (U.s2n s) 

varT' :: TyName -> Kind -> [Type] -> Type
varT' x k args = Type {
  _tyRep = VarT x args
  , _tyKnd = k
  }

funT' :: [(TyName, Kind)] -> ArrowType -> Type
funT' bound arr = let
  in Type {
    _tyRep = FunT (U.bind bound arr)
    , _tyKnd = KTy 1
    }

funT :: [(S.Name, Kind)] -> [Type] -> Type -> Type
funT tvks doms cod = let
  bound = map (first U.s2n) tvks
  in funT' bound $ ArrowType doms cod

arrT :: [Type] -> Type -> Type
arrT = funT []


----------------------------------------

widthSubtype :: U.LFresh m => Type -> Type -> m Bool
widthSubtype t1 t2 = (t1^.tyRep) ≼ (t2^.tyRep)
  where
    (≼) :: U.LFresh m => Type' -> Type' -> m Bool
    TupleT ts1 ≼ TupleT ts2 =
      if length ts1 >= length ts2
      then liftM and $ zipWithM (depthCompare EQ) ts1 ts2
      else  depthCompare EQ t1 t2
    _          ≼ _ = depthCompare EQ t1 t2
               
widthJoin :: U.LFresh m => Type -> Type -> m (Maybe Type)
widthJoin t1 t2 = (t1^.tyRep) ⋎? (t2^.tyRep)
  where
    (⋎?) :: U.LFresh m => Type' -> Type' -> m (Maybe Type)
    TupleT ts1 ⋎? TupleT ts2 = do
      -- join is the longest common subsequence
      ts' <- zipWithM (depthCombine EQ) ts1 ts2
      let ts'' = sequence $ takeWhile isJust ts'
      return $ fmap tupleT ts''
    _          ⋎? _          = depthCombine EQ t1 t2

widthMeet :: U.LFresh m => Type -> Type -> m (Maybe Type)
widthMeet t1 t2 = (t1^.tyRep) ⋏? (t2^.tyRep)
  where
    (⋏?) :: U.LFresh m => Type' -> Type' -> m (Maybe Type)
    TupleT ts1 ⋏? TupleT ts2 = do
      -- meet is the type such that the other one is a prefix of it
      common <- liftM sequence $ zipWithM (depthCombine EQ) ts1 ts2
      let suffix = case length ts1 `compare` length ts2 of
            LT -> drop (length ts1) ts2
            GT -> drop (length ts2) ts1
            EQ -> []
      return $ fmap tupleT (fmap (++suffix) common)
    _          ⋏? _          = depthCombine EQ t1 t2

arrSubtype :: U.LFresh m => ArrowType -> ArrowType -> m Bool
arrSubtype a1 a2 = do
  let
    argsOk = length (arrDom a1) == length (arrDom a2)
  domOk <- depthCompares LT (arrDom a2) (arrDom a1)
  codOk <- arrCod a1 `depthSubtype` arrCod a2
  return $ argsOk && domOk && codOk
  
depthSubtype :: U.LFresh m => Type -> Type -> m Bool
depthSubtype t1 t2 = (t1^.tyRep) ≤ (t2^.tyRep)
    where
      -- (≤) :: U.LFresh m => Type' -> Type' -> m Bool
      BotT       ≤         _  = return True
      _          ≤ TopT       = return $ t1^.tyKnd <=: t2^.tyKnd
      VarT v1 args1 ≤ VarT v2 args2 | v1 == v2 =
        -- assume all type constructors are invariant in their arguments.
        -- TODO: add polarity declarations to variables
        depthCompares EQ args1 args2
      TupleT ts1 ≤ TupleT ts2 = depthCompares LT ts1 ts2
      BoxT t1'   ≤ BoxT t2'   = widthSubtype t1' t2'
      FunT barr1 ≤ FunT barr2 =
        U.lunbind2 barr1 barr2 $ \r ->
        case r of
          Nothing -> return False -- different number of bound vars
          Just (_, arr1, _, arr2) -> arrSubtype arr1 arr2
      _          ≤ _          = return $ t1 `U.aeq` t2
     
depthCompares :: U.LFresh m => Direction -> [Type] -> [Type] -> m Bool
depthCompares dir xs ys
  | length xs == length ys = liftM and $ zipWithM (depthCompare dir) xs ys
  | otherwise              = return False

depthCompare :: U.LFresh m => Direction -> Type -> Type -> m Bool
depthCompare LT = depthSubtype
depthCompare GT = flip depthSubtype
depthCompare EQ = \t1 t2 ->
  liftM2 (&&) (depthSubtype t1 t2) (depthSubtype t2 t1)

depthMeet :: U.LFresh m => Type -> Type -> m (Maybe Type)
depthMeet t1 t2 = (t1^.tyRep) ⋏? (t2^.tyRep)
  where
    FunT bnd1 ⋏? FunT bnd2 =
      U.lunbind2 bnd1 bnd2 $ \r ->
      case r of
        Nothing -> return Nothing
        Just (vks1, arr1, _vks2, arr2) ->
          liftM (liftM (funT' vks1)) $ depthMeetArr arr1 arr2

    TupleT ts1 ⋏? TupleT ts2 =
      liftM (liftM tupleT . sequence) $ zipWithM depthMeet ts1 ts2
    BoxT s1 ⋏? BoxT s2 =
      widthMeet s1 s2
    _ ⋏? _ = do
      sb1 <- depthSubtype t1 t2
      if sb1
        then return $ Just t1
        else do
        sb2 <- depthSubtype t2 t1
        if sb2
          then return $ Just t2
          else return Nothing

depthJoin :: U.LFresh m => Type -> Type -> m (Maybe Type)
depthJoin t1 t2 = (t1^.tyRep) ⋎? (t2^.tyRep)
  where
    FunT bnd1 ⋎? FunT bnd2 =
      U.lunbind2 bnd1 bnd2 $ \r ->
      case r of
        Nothing -> return Nothing
        Just (vks1, arr1, _vks2, arr2) ->
          liftM (liftM (funT' vks1)) $ depthJoinArr arr1 arr2
    TupleT ts1 ⋎? TupleT ts2 =
      liftM (liftM tupleT . sequence) $ zipWithM depthJoin ts1 ts2
    BoxT s1 ⋎? BoxT s2 =
      widthJoin s1 s2
    _ ⋎? _ = do
      sb2 <- depthSubtype t1 t2
      if sb2
        then  return $ Just t2
        else do
        sb1 <- depthSubtype t2 t1
        if sb1
          then return $ Just t1
          else return Nothing
        

depthCombine :: U.LFresh m => Direction -> Type -> Type -> m (Maybe Type)
depthCombine LT = depthMeet
depthCombine GT = depthJoin
depthCombine EQ = \t1 t2 -> do
  mt <- depthMeet t1 t2
  jn <- depthJoin t1 t2
  case (mt, jn) of
    (Just mt', Just jn') -> do
      e <- depthCompare EQ mt' jn'
      return $ if e then Just jn' else Nothing
    _ -> return Nothing

depthMeetArr :: U.LFresh m => ArrowType -> ArrowType -> m (Maybe ArrowType)
depthMeetArr arr1 arr2 = do
  doms' <- liftM sequence $ zipWithM depthJoin (arrDom arr1) (arrDom arr2)
  cod' <- depthMeet (arrCod arr2) (arrCod arr2)
  return $ liftM2 ArrowType doms' cod'

depthJoinArr :: U.LFresh m => ArrowType -> ArrowType -> m (Maybe ArrowType)
depthJoinArr arr1 arr2 = do
  dom' <- liftM sequence $ zipWithM depthMeet (arrDom arr1) (arrDom arr2)
  cod' <- depthJoin (arrCod arr1) (arrCod arr2)
  return $ liftM2 ArrowType dom' cod'

instance Preorder Type where
  (<=:) = preorderCompare LT
  (~:)  = preorderCompare EQ
  preorderCompare dir t1 t2 = U.runLFreshM (depthCompare dir t1 t2)
  (/\?) = preorderCombine LT
  (\/?) = preorderCombine GT
  (~~?) = preorderCombine EQ
  preorderCombine dir t1 t2 = U.runLFreshM (depthCombine dir t1 t2)

