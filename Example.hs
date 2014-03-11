{-#
  LANGUAGE
    FlexibleInstances
  #-}
module Example where

import Control.Applicative
import Control.Lens
import Control.Monad.Reader

import Data.Monoid

import Text.Parsec (parse, ParseError, eof)
import Gust.Parse (SourceCode(..))
import Gust.AST as S
import Gust.Typed
import Gust.Type
import Gust.Located
import Gust.ElabType

import Data.Order

data ExampleError =
  ExParseE ParseError -- ^ parser error
  | ExElabE String -- ^ elaboration error
    deriving Show

instance MonadElabTy (ReaderT TyEnv (Either String)) where

r :: String -> Either ExampleError (S.SType (Typed (Located ())))
r s = case parse (parser <* eof) "___" s of
  Left err -> Left (ExParseE err)
  Right t -> over _Left ExElabE $ runReaderT (elabTy t) (mempty ^. tyEnv)

rr :: String -> Type
rr s = let
  Right ans = over _Right (view ty) $ r s
  in ans

test1 = rr "forall a, b . (a) -> b"

test2 = rr "forall a, b . (a, a) -> b"

test3 = rr "forall a, b . (box (a, a)) -> b"

test4 = rr "forall a, b . (box (a, a, a)) -> b"

testCmp34 = test3 <=: test4

testMt34 = test3 /\? test4
