-- | This module implements the "variable elimination" algorithm from
-- Pierce-Turner Local Type Inference (TOPLAS 2000).
module Gust.LTI.Avoid where

import Control.Monad
import Control.Lens
  
import qualified Data.List
import qualified Data.Set as Set

import qualified Unbound.LocallyNameless as U

import Gust.Type
import Gust.Internal.Utils ((∈))

alsoAvoid :: [(TyName, a)] -> Set.Set TyName -> Set.Set TyName
alsoAvoid ws = Set.union (Set.fromList $ map fst ws)

-- | Variable elimination by promotion.
-- S⇑V returns a type T such that S ≤ T with FV(T)∩V = ∅
-- and T is the least such type.
-- 
-- Such a type always exists because we have ⊤ᵏ in our type language
-- for every kind k.
avoidUp :: U.LFresh m => Set.Set TyName -> Type -> m Type
avoidUp vs s = case s^.tyRep of
  VarT n args
    | n ∈ vs         -> return $ topT (s^.tyKnd)
    | otherwise      -> return $ if all (doesntMention vs) args
                                 then s
                                 else topT (s^.tyKnd)
  TopT               -> return s
  BotT               -> return s
  BoxT s1            -> do
    return $ case avoidWidthUp vs s1 of
      Just t         -> boxT t
      Nothing        -> topT (s^.tyKnd)
  TupleT ss          -> liftM tupleT $ mapM (avoidUp vs) ss
  FunT bnd           -> U.lunbind bnd $ \(bnds, arr) ->
    liftM (funT' bnds) $ avoidUpArr (alsoAvoid bnds vs) arr

avoidUpArr :: U.LFresh m => Set.Set TyName -> ArrowType -> m ArrowType
avoidUpArr vs arr =
  liftM2 ArrowType (mapM (avoidDown vs) $ arrDom arr) (avoidUp vs $ arrCod arr)

-- | Variable elimination by demotion.
-- S⇓V returns a type T such that T ≤ S with FV(S)∩V = ∅
-- and T is the greatest such type.
--   
-- Such a type T always exists because we have ⊥ in our type language
-- below every well-formed type.
avoidDown :: U.LFresh m => Set.Set TyName -> Type -> m Type
avoidDown vs s = case s^.tyRep of
  VarT n args
    | n ∈ vs    -> return $ botT
    | otherwise -> return $ if all (doesntMention vs) args then s else botT
  TopT          -> return s
  BotT          -> return s
  BoxT s1       -> return $ if doesntMention vs s1 then s else botT
  TupleT ss     -> liftM tupleT $ mapM (avoidDown vs) ss
  FunT bnd      -> U.lunbind bnd $ \(bnds, arr) ->
    liftM (funT' bnds) $ avoidDownArr (alsoAvoid bnds vs) arr

avoidDownArr :: U.LFresh m => Set.Set TyName -> ArrowType -> m ArrowType
avoidDownArr vs arr =
  liftM2 ArrowType (mapM (avoidUp vs) $ arrDom arr) (avoidDown vs $ arrCod arr)


-- | Variable elimination by narrowing.
-- S⇑w V returns Just T where type T is
-- such that S ≤w T with FV(S)∩V = ∅
-- and T is the least such type.
--
-- Such a type may not exist (because ≤w does not have a top element
-- for all types), in which case we return Nothing.
avoidWidthUp :: Set.Set TyName -> Type -> Maybe Type
avoidWidthUp vs s = case s^.tyRep of
  TupleT ss -> let
    -- for tuples, keep the longest prefix that doesn't mention the
    -- bad variables and drop the remaining tail.
    ss' = Data.List.takeWhile (doesntMention vs) ss
    in Just $ tupleT ss'
  _ -> Nothing
     


-- | 'doesntMention vs t' == True iff fv(t)∩vs=∅
doesntMention :: Set.Set TyName -> Type -> Bool
doesntMention vs t =
  Set.null $ U.fv t `Set.intersection` vs
