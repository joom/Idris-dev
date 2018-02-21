{-|
Module      : Idris.SExp
Description : Idris' SExp to be used with communication with the editor
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE FlexibleInstances, IncoherentInstances, PatternGuards #-}

module Idris.SExp(parseMessage, convSExp, toSExp, SExp(..), SExpable, sExpToString, decodeTerm, decodeErr) where

import Idris.Core.Binary ()
import Idris.Core.TT

import Control.Applicative hiding (Const)
import Control.Arrow (left)
import qualified Data.Binary as Binary
import qualified Data.ByteString.Base64 as Base64
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.ByteString.UTF8 as UTF8
import Data.List
import Data.Maybe (isJust)
import qualified Data.Text as T
import Numeric
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import Text.Printf

data SExp = SexpList [SExp]
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String
          deriving ( Eq, Show )

sExpToString :: SExp -> String
sExpToString (StringAtom s)   = "\"" ++ escape s ++ "\""
sExpToString (BoolAtom True)  = ":True"
sExpToString (BoolAtom False) = ":False"
sExpToString (IntegerAtom i)  = printf "%d" i
sExpToString (SymbolAtom s)   = ":" ++ s
sExpToString (SexpList l)     = "(" ++ intercalate " " (map sExpToString l) ++ ")"

class SExpable a where
  toSExp :: a -> SExp

instance SExpable SExp where
  toSExp a = a

instance SExpable Bool where
  toSExp True  = BoolAtom True
  toSExp False = BoolAtom False

instance SExpable String where
  toSExp s = StringAtom s

instance SExpable Integer where
  toSExp n = IntegerAtom n

instance SExpable Int where
  toSExp n = IntegerAtom (toInteger n)

instance SExpable Name where
  toSExp s = StringAtom (show s)

instance (SExpable a) => SExpable (Maybe a) where
  toSExp Nothing  = SexpList [SymbolAtom "Nothing"]
  toSExp (Just a) = SexpList [SymbolAtom "Just", toSExp a]

instance (SExpable a) => SExpable [a] where
  toSExp l = SexpList (map toSExp l)

instance (SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (l, r) = SexpList [toSExp l, toSExp r]

instance (SExpable a, SExpable b, SExpable c) => SExpable (a, b, c) where
  toSExp (l, m, n) = SexpList [toSExp l, toSExp m, toSExp n]

instance (SExpable a, SExpable b, SExpable c, SExpable d) => SExpable (a, b, c, d) where
  toSExp (l, m, n, o) = SexpList [toSExp l, toSExp m, toSExp n, toSExp o]

instance (SExpable a, SExpable b, SExpable c, SExpable d, SExpable e) =>
         SExpable (a, b, c, d, e) where
   toSExp (l, m, n, o, p) = SexpList [toSExp l, toSExp m, toSExp n, toSExp o, toSExp p]

instance SExpable NameOutput where
  toSExp TypeOutput      = SymbolAtom "type"
  toSExp FunOutput       = SymbolAtom "function"
  toSExp DataOutput      = SymbolAtom "data"
  toSExp MetavarOutput   = SymbolAtom "metavar"
  toSExp PostulateOutput = SymbolAtom "postulate"

maybeProps :: SExpable a => [(String, Maybe a)] -> [(SExp, SExp)]
maybeProps [] = []
maybeProps ((n, Just p):ps) = (SymbolAtom n, toSExp p) : maybeProps ps
maybeProps ((n, Nothing):ps) = maybeProps ps

constTy :: Const -> String
constTy (I _) = "Int"
constTy (BI _) = "Integer"
constTy (Fl _) = "Double"
constTy (Ch _) = "Char"
constTy (Str _) = "String"
constTy (B8 _) = "Bits8"
constTy (B16 _) = "Bits16"
constTy (B32 _) = "Bits32"
constTy (B64 _) = "Bits64"
constTy _ = "Type"

namespaceOf :: Name -> Maybe String
namespaceOf (NS _ ns) = Just (intercalate "." $ reverse (map T.unpack ns))
namespaceOf _         = Nothing

instance SExpable OutputAnnotation where
  toSExp (AnnName n ty d t) = toSExp $ [(SymbolAtom "name", StringAtom (show n)),
                                        (SymbolAtom "implicit", BoolAtom False),
                                        (SymbolAtom "key", StringAtom (encodeName n))] ++
                                       maybeProps [("decor", ty)] ++
                                       maybeProps [("doc-overview", d), ("type", t)] ++
                                       maybeProps [("namespace", namespaceOf n)]
  toSExp (AnnBoundName n imp)    = toSExp [(SymbolAtom "name", StringAtom (show n)),
                                           (SymbolAtom "decor", SymbolAtom "bound"),
                                           (SymbolAtom "implicit", BoolAtom imp)]
  toSExp (AnnConst c)            = toSExp [(SymbolAtom "decor",
                                            SymbolAtom (if constIsType c then "type" else "data")),
                                           (SymbolAtom "type", StringAtom (constTy c)),
                                           (SymbolAtom "doc-overview", StringAtom (constDocs c)),
                                           (SymbolAtom "name", StringAtom (show c))]
  toSExp (AnnData ty doc)        = toSExp [(SymbolAtom "decor", SymbolAtom "data"),
                                           (SymbolAtom "type", StringAtom ty),
                                           (SymbolAtom "doc-overview", StringAtom doc)]
  toSExp (AnnType name doc)      = toSExp $ [(SymbolAtom "decor", SymbolAtom "type"),
                                             (SymbolAtom "type", StringAtom "Type"),
                                             (SymbolAtom "doc-overview", StringAtom doc)] ++
                                             if not (null name) then [(SymbolAtom "name", StringAtom name)] else []
  toSExp AnnKeyword              = toSExp [(SymbolAtom "decor", SymbolAtom "keyword")]
  toSExp (AnnFC fc)      = toSExp [(SymbolAtom "source-loc", toSExp fc)]
  toSExp (AnnTextFmt fmt) = toSExp [(SymbolAtom "text-formatting", SymbolAtom format)]
      where format = case fmt of
                       BoldText      -> "bold"
                       ItalicText    -> "italic"
                       UnderlineText -> "underline"
  toSExp (AnnLink url) = toSExp [(SymbolAtom "link-href", StringAtom url)]
  toSExp (AnnTerm bnd tm)
    | termSmallerThan 1000 tm = toSExp [(SymbolAtom "tt-term", StringAtom (encodeTerm bnd tm))]
    | otherwise = SexpList []
  toSExp (AnnSearchResult ordr) = toSExp [(SymbolAtom "doc-overview",
      StringAtom ("Result type is " ++ descr))]
      where descr = case ordr of
              EQ -> "isomorphic"
              LT -> "more general than searched type"
              GT -> "more specific than searched type"
  toSExp (AnnErr e) = toSExp [(SymbolAtom "error", StringAtom (encodeErr e))]
  toSExp (AnnNamespace ns file) =
    toSExp $ [(SymbolAtom "namespace", StringAtom (intercalate "." (map T.unpack ns)))] ++
             [(SymbolAtom "decor", SymbolAtom $ if isJust file then "module" else "namespace")] ++
             maybeProps [("source-file", file)]
  toSExp AnnQuasiquote = toSExp [(SymbolAtom "quasiquotation", True)]
  toSExp AnnAntiquote = toSExp [(SymbolAtom "antiquotation", True)]
  toSExp (AnnSyntax c) = SexpList []

encodeName :: Name -> String
encodeName n = UTF8.toString . Base64.encode . Lazy.toStrict . Binary.encode $ n

encodeTerm :: [(Name, Bool)] -> Term -> String
encodeTerm bnd tm = UTF8.toString . Base64.encode . Lazy.toStrict . Binary.encode $
                    (bnd, tm)

decodeTerm :: String -> ([(Name, Bool)], Term)
decodeTerm = Binary.decode . Lazy.fromStrict . Base64.decodeLenient . UTF8.fromString

encodeErr :: Err -> String
encodeErr e = UTF8.toString . Base64.encode . Lazy.toStrict . Binary.encode $ e

decodeErr :: String -> Err
decodeErr = Binary.decode . Lazy.fromStrict . Base64.decodeLenient . UTF8.fromString

instance SExpable FC where
  toSExp (FC f (sl, sc) (el, ec)) =
    toSExp ((SymbolAtom "filename", StringAtom f),
            (SymbolAtom "start",  IntegerAtom (toInteger sl), IntegerAtom (toInteger sc)),
            (SymbolAtom "end", IntegerAtom (toInteger el), IntegerAtom (toInteger ec)))
  toSExp NoFC = toSExp ([] :: [String])
  toSExp (FileFC f) = toSExp [(SymbolAtom "filename", StringAtom f)]

escape :: String -> String
escape = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar c    = [c]

type Parser a = P.Parsec () String a

sexp :: Parser SExp
sexp = SexpList <$> P.between (P.char '(') (P.char ')') (sexp `P.sepBy` (P.char ' '))
    <|> atom

atom :: Parser SExp
atom = SexpList [] <$ P.string "nil"
   <|> P.char ':' *> atomC
   <|> StringAtom <$> P.between (P.char '"') (P.char '"') (P.many quotedChar)
   <|> do ints <- some P.digitChar
          case readDec ints of
            ((num, ""):_) -> return (IntegerAtom (toInteger num))
            _ -> return (StringAtom ints)

atomC :: Parser SExp
atomC = BoolAtom True  <$ P.string "True"
    <|> BoolAtom False <$ P.string "False"
    <|> SymbolAtom <$> many (P.noneOf " \n\t\r\"()")

quotedChar :: Parser Char
quotedChar = P.try ('\\' <$ P.string "\\\\")
         <|> P.try ('"' <$ P.string "\\\"")
         <|> P.noneOf "\""

parseMessage :: String -> Either Err (SExp, Integer)
parseMessage x = case receiveString x of
                   Right (SexpList [cmd, (IntegerAtom id)]) -> Right (cmd, id)
                   Right x -> Left . Msg $ "Invalid message " ++ show x
                   Left err -> Left err

receiveString :: String -> Either Err SExp
receiveString = left (const $ Msg "parse failure") . P.parse sexp "(unknown)"

convSExp :: SExpable a => String -> a -> Integer -> String
convSExp pre s id =
  let sex = SexpList [SymbolAtom pre, toSExp s, IntegerAtom id] in
      let str = sExpToString sex in
          (getHexLength str) ++ str

getHexLength :: String -> String
getHexLength s = printf "%06x" (1 + (length s))
