module Gust.Parse where

import Control.Lens

import Control.Applicative hiding (many)
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language (haskellStyle)
import qualified Text.Parsec.Token as Tok

import Gust.AST
import Gust.Kind
import Gust.Located

type Parser = Parsec String ()

parseProgram :: Parser (Program (Located ()))
parseProgram = many1 parser <* eof

class SourceCode t where
  parser :: Parser (Meta t (Located ()))

hereIs :: Parser (t (Located ())) -> Parser (Meta t (Located ()))
hereIs cmd = do
  p1 <- getPosition
  x <- cmd
  p2 <- getPosition
  let l = Location (sourceName p1)
                   (sourceLine p1) (sourceColumn p1)
                   (sourceLine p2) (sourceColumn p2)
  return $ x :@: Located l ()
  
instance SourceCode SType' where
  parser =
    hereIs
    ((BoxST
          <$> (box *> parser))
     <|> try (AppST
              <$> identifier
              <*> parens (commaSep parser))
     <|> (tupleOrFun
          <$> atomicType
          <*> optionMaybe (arrow *> parser))
     <|> (FunST
          <$> option [] (forall *> (typeBindings <* dot))
          <*> parens (commaSep parser)
          <*> (arrow *> parser))
      <?> "type")
    where
      atomicType =
        parens (commaSep parser)
        <|> identType

      identType =
        singleton
        <$> hereIs (AppST <$> identifier <*> pure [])

      tupleOrFun [x] Nothing = x^.mValue
      tupleOrFun xs Nothing = TupleST xs
      tupleOrFun xs (Just y) = FunST [] xs y

      singleton x = [x]

instance SourceCode Decl' where
  parser =
    hereIs 
      (kw "fun" *> parseFun
       <|> kw "abstype" *> parseAbstype
       <|> kw "extern" *> kw "var" *> parseExternVar
       <?> "declaration")

parseAbstype :: Parser (Decl' (Located ()))
parseAbstype = AbstypeD <$> identifier <*> (colon *> parseTyBind)
  
parseTyBind :: Parser TyBind
parseTyBind = AbsTB 
              <$> (option [] $ angles (commaSep parseKind))
              <*> parseKind

instance SourceCode Expr' where
  parser =
    hereIs ((applicationOrAtom
             <$> atomicExpr
             <*> optionMaybe ((,)
                              <$> option [] (angles (commaSep parser))
                              <*> parens (commaSep parser)))
            <?> "expression")
    where
      atomicExpr =
        hereIs ((VarE <$> pvar)
                <|> parens tuplishExpr
                <|> (BlockE
                     <$> (kw "let" *> many parser)
                     <*> (kw "in" *> parser)))

      tuplishExpr =
        mkTuplishExpr
        <$> parser
        <*> optionMaybe (Left <$> (comma *> commaSep parser)
                         <|> Right <$> (kw "as" *> parser))

      mkTuplishExpr firstE Nothing = firstE^.mValue
      mkTuplishExpr firstE (Just (Left restE)) = TupleE (firstE : restE)
      mkTuplishExpr firstE (Just (Right tp)) = AscribeE firstE tp

      applicationOrAtom e Nothing = e^.mValue
      applicationOrAtom e (Just (ts, es)) = ApplyE e ts es
    
instance SourceCode Stmt' where
  parser =
    hereIs ((VarS
             <$> (kw "var" *> pvar)
             <*> (equals *> parser)))
    <?> "statement"

pvar :: Parser Var
pvar = UserV <$> identifier

parseKind :: Parser Kind
parseKind = parens parseKind
            <|> (kw "T" *> pure KTy)

typeBindings :: Parser [TypeBinding]
typeBindings = commaSep ((,)
                         <$> identifier
                         <*> option (AbsTB [] KTy) (colon *> parseTyBind))
               <?> "type variable binding(s)"

termBindings :: Parser [TermBinding (Located ())]
termBindings = commaSep ((,)
                         <$> pvar
                         <*> (colon *> parser))
               <?> "term variable binding(s)"

-- (fun) name <types> (binds) : rt = e
parseFun :: Parser (Decl' (Located ()))
parseFun = mkFunDecl
           <$> pvar
           <*> option [] (angles typeBindings)
           <*> parens termBindings
           <*> (colon *> parser)
           <*> (equals *> parser)
  where
    mkFunDecl name tyBinds tmBinds retT e =
      TermD name $ FunD $ FunDecl {
        _fdTyArgs = tyBinds
        , _fdArgs = tmBinds
        , _fdResult = retT
        , _fdBody = e
        }

-- (extern var) name : type
parseExternVar :: Parser (Decl' (Located ()))
parseExternVar =
  mkExternVarDecl
  <$> pvar
  <*> (colon *> parser)               
  where
    mkExternVarDecl name t = TermD name $ ExternD t


gustDef :: Tok.LanguageDef st
gustDef = haskellStyle {
  Tok.reservedNames = [
     -- declarations
     "fun", "abstype", "extern"
     -- expressions
     , "let", "in", "as"
     -- statements
     , "var"
     -- types
     , "forall", "box"
     -- kinds
     , "T"
     ]
  , Tok.reservedOpNames = [
     "->", "→", "∀", "̱□"
     ]
  }

tok :: Tok.TokenParser ()
tok = Tok.makeTokenParser gustDef

kw :: String -> Parser ()
kw = Tok.reserved tok

parens :: Parser a -> Parser a
parens = Tok.parens tok

angles :: Parser a -> Parser a
angles = Tok.angles tok
  
colon :: Parser ()
colon = Tok.colon tok >> return ()

dot :: Parser ()
dot = Tok.dot tok >> return ()

comma :: Parser ()
comma = Tok.comma tok >> return ()

equals :: Parser ()
equals = Tok.reservedOp tok "="

arrow :: Parser ()
arrow = Tok.reservedOp tok "->" <|> Tok.reservedOp tok "→"

forall :: Parser ()
forall = kw "forall" <|> Tok.reservedOp tok "∀"

box :: Parser ()
box = kw "box" <|> Tok.reservedOp tok "□"

identifier :: Parser String
identifier = Tok.identifier tok

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep tok

test :: String -> IO ()
test = parseTest (parser <* eof :: Parser (Decl (Located ())))

example1 :: String
example1 = "fun v<a:(T),b> (x:()) : () = let var y = x in y <b> (x)"
