{-#
  LANGUAGE
    FlexibleInstances
  #-}
module Example where

import Control.Applicative
import Control.Lens
import Control.Monad.Reader
import Control.Monad.Error

import Data.Monoid

import Text.Parsec (parse, ParseError, eof)

import qualified Unbound.LocallyNameless as U

import Gust.Parse (SourceCode(..), Parser, parseProgram)
import Gust.AST as S
import Gust.Typed
import Gust.Type
import Gust.Located
import Gust.ElabType
import qualified Gust.Check (elaborateProgram, emptyElabEnv)


import Data.Order

data ExampleError =
  ExParseE ParseError -- ^ parser error
  | ExElabE String -- ^ elaboration error

instance Show ExampleError where
  showsPrec _ (ExParseE pe) = showString "Parser Error: " . shows pe
  showsPrec _ (ExElabE msg) = showString "Elaboration Error: " . showString msg


p :: Parser a -> FilePath -> IO (Either ExampleError a)
p parseIt fp = do
  s <- readFile fp
  return $ over _Left ExParseE $ parse (parseIt <* eof) fp s

elaborateType :: (S.SType (Located ()))
              -> Either ExampleError (S.SType (Typed (Located ())))
elaborateType t =
  over _Left ExElabE $ runReaderT (elabTy t) (mempty ^. typeEnv)

elaborateProgram  :: Program (Located ())
                     -> Either ExampleError (Program (Typed (Located ())))
elaborateProgram prog =
  over _Left ExElabE
  $ runIdentity
  $ runErrorT
  $ U.runFreshMT
  $ runReaderT (Gust.Check.elaborateProgram prog) Gust.Check.emptyElabEnv

r :: String -> Either ExampleError (S.SType (Typed (Located ())))
r s = case parse (parser <* eof) "___" s of
  Left err -> Left (ExParseE err)
  Right t -> elaborateType t

rr :: String -> Type
rr s = let
  Right ans = over _Right (view ty) $ r s
  in ans

rf :: FilePath -> IO Type
rf fp = do
  t0 <- p parser fp
  case t0 >>= elaborateType  of
    Left err -> error $ show err
    Right ans -> return $ ans^.ty

rp :: FilePath -> IO (Program (Typed (Located ())))
rp fp = do
  t0 <- p parseProgram fp
  case t0 >>= elaborateProgram of
    Left err -> do { putStrLn (show err) ; error "elaboration failed" }
    Right ans -> return ans

-- Not doing higher order quantification yet.
-- test1 :: Type
-- test1 = rr "forall a : <T,T>T, b . (a (b,b)) -> b"

test2 :: Type
test2 = rr "forall a, b . (a, a) -> b"

test3 :: Type
test3 = rr "forall a, b . (box (a, a)) -> b"

test4 :: Type
test4 = rr "forall a, b . (box (a, a, a)) -> b"

test5 :: Type
test5 = rr "(⊤, (), ⊤ 2)"

testCmp34 :: Bool
testCmp34 = test3 <=: test4

testMt34 :: Maybe Type
testMt34 = test3 /\? test4

testF1 :: IO Type
testF1 = rf "examples/ex1.gt"

testF2 :: IO (Program (Typed (Located ())))
testF2 = rp "examples/ex2.gt"
