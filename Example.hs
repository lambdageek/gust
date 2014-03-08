{-#
  LANGUAGE
    FlexibleInstances
  #-}
module Example where

import Control.Applicative
import Control.Lens

import Data.Monoid

import Text.Parsec (parse, ParseError, eof)
import Gust.Parse (SourceCode(..))
import Gust.AST as S
import Gust.Typed
import Gust.Located
import Gust.ElabType

import Control.Monad.Reader

data ExampleError =
  ExParseE ParseError -- ^ parser error
  | ExElabE String -- ^ elaboration error
    deriving Show

instance MonadElabTy (ReaderT TyEnv (Either String)) where

r :: String -> Either ExampleError (S.SType (Typed (Located ())))
r s = case parse (parser <* eof) "___" s of
  Left err -> Left (ExParseE err)
  Right t -> over _Left ExElabE $ runReaderT (elabTy t) (mempty ^. tyEnv)

test1 = over _Right (view ty) $ r "forall a, b . (a) -> b"
