module Language.Reflection.Editor

import Language.Reflection
import Language.Reflection.Elab
import Language.Reflection.Errors

%access public export

||| The S-expression data type. Has a direct correspondence to the S-expression
||| type in the IDE mode in the Idris implementation.
data SExp =
   SExpList (List SExp) | StringAtom String | BoolAtom Bool |
   IntegerAtom Integer | SymbolAtom String

escape : String -> String
escape = foldr (++) "" . map escapeChar . unpack
  where
    escapeChar : Char -> String
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar c    = singleton c

implementation Show SExp where
  show (StringAtom s) = "\"" ++ escape s ++ "\""
  show (BoolAtom True) = ":True"
  show (BoolAtom False) = ":False"
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s
  show (SExpList l) = "(" ++ mid ++ ")"
    where mid = foldr (++) "" (intersperse " " (map show l))

implementation Eq SExp where
  (StringAtom x) == (StringAtom y) = x == y
  (BoolAtom x) == (BoolAtom y) = x == y
  (IntegerAtom x) == (IntegerAtom y) = x == y
  (SymbolAtom x) == (SymbolAtom y) = x == y
  (SExpList xs) == (SExpList ys) = assert_total (xs == ys)
  _ == _ = False

implementation Cast SExp String where
  cast x = assert_total (show x)

implementation Quotable SExp TT where
  quotedTy = `(SExp)
  quote (SExpList xs) = assert_total `(SExpList ~(quote xs))
  quote (StringAtom s) = `(StringAtom ~(quote s))
  quote (SymbolAtom s) = `(SymbolAtom ~(quote s))
  quote (BoolAtom True) = `(BoolAtom True)
  quote (BoolAtom False) = `(BoolAtom False)
  quote (IntegerAtom i) = `(IntegerAtom ~(quote i))

implementation Quotable SExp Raw where
  quotedTy = `(SExp)
  quote (SExpList xs) = assert_total `(SExpList ~(quote xs))
  quote (StringAtom s) = `(StringAtom ~(quote s))
  quote (SymbolAtom s) = `(SymbolAtom ~(quote s))
  quote (BoolAtom True) = `(BoolAtom True)
  quote (BoolAtom False) = `(BoolAtom False)
  quote (IntegerAtom i) = `(IntegerAtom ~(quote i))

||| Limits the types that the compiler knows how to specially serialize
||| into S-expressions. It is different from the compiler's `SExpable`
||| in that certain reflection types like `TTName`, `TT`, `TyDecl`, `DataDefn`,
||| `FunDefn`, `FunClause` are primitives, which go through delaboration
||| and pretty printing in the compiler.
interface Editorable a where
  fromEditor : SExp -> Either Err a
  toEditor : a -> SExp

-- These primitives should never appear when we are normalizing terms
-- when we run tactics in the editor or when we use Editorable in the REPL.
-- However, they will appear when we run the compiled program
implementation Editorable TT where
  fromEditor x = prim__fromEditorTT x
  toEditor   x = prim__toEditorTT x

implementation Editorable TyDecl where
  fromEditor x = prim__fromEditorTyDecl x
  toEditor   x = prim__toEditorTyDecl x

implementation Editorable DataDefn where
  fromEditor x = prim__fromEditorDataDefn x
  toEditor   x = prim__toEditorDataDefn x

implementation Editorable (FunDefn TT) where
  fromEditor x = prim__fromEditorFunDefnTT x
  toEditor   x = prim__toEditorFunDefnTT x

implementation Editorable (FunClause TT) where
  fromEditor x = prim__fromEditorFunClauseTT x
  toEditor   x = prim__toEditorFunClauseTT x

implementation Editorable TTName where
  fromEditor (StringAtom s) = namify s
    where namify s = case reverse (map pack (splitOn '.' (unpack s))) of
                        [] => Left (Msg "Empty string can't be a TTName")
                        [x] => pure (UN x)
                        (x :: xs) => pure (NS (UN x) xs)
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a TTName")

  toEditor n = StringAtom (stringify n)
    where
      stringify (UN x) = x
      stringify (NS x []) = stringify x
      stringify (NS x xs) =
        concat (intersperse "." (reverse ("" :: xs))) ++ stringify x
      stringify (MN i x) = "__" ++ x ++ show i
      stringify (SN sn) = "" -- TODO fix

implementation Editorable Unit where
  fromEditor (SExpList []) = pure ()
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Unit")
  toEditor () = SExpList []

implementation Editorable Void where
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Void")
  toEditor _ impossible

implementation Editorable String where
  fromEditor (StringAtom s) = pure s
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a String")
  toEditor = StringAtom

implementation Editorable Char where
  fromEditor (StringAtom s) = case unpack s of
                                   [c] => pure c
                                   _ => Left (Msg "More than one character")
  fromEditor _ = Left (Msg "Can't parse SExp for Char")
  toEditor c = StringAtom (pack [c])

implementation Editorable Integer where
  fromEditor (IntegerAtom n) = pure n
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as an Integer")
  toEditor = IntegerAtom

implementation Editorable Int where
  fromEditor (IntegerAtom n) = pure (fromInteger n)
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as an Int")
  toEditor = IntegerAtom . cast

implementation Editorable Nat where
  fromEditor (IntegerAtom n) = pure (fromInteger n)
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Nat")
  toEditor = IntegerAtom . cast

implementation Editorable Bool where
  fromEditor (BoolAtom b) = pure b
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Bool")
  toEditor = BoolAtom

implementation Editorable a => Editorable (List a) where
  fromEditor (SExpList xs) = sequence (map fromEditor xs)
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a List")
  toEditor xs = SExpList (map toEditor xs)

implementation Editorable a => Editorable (Maybe a) where
  fromEditor (SExpList [SymbolAtom "Nothing"]) = pure Nothing
  fromEditor (SExpList [SymbolAtom "Just", x]) = Just <$> fromEditor x
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Maybe")
  toEditor (Just x) = SExpList [SymbolAtom "Just", toEditor x]
  toEditor Nothing = SExpList [SymbolAtom "Nothing"]

implementation (Editorable a, Editorable b) => Editorable (Either a b) where
  fromEditor (SExpList [SymbolAtom "Left", x]) = Left <$> fromEditor x
  fromEditor (SExpList [SymbolAtom "Right", y]) = Right <$> fromEditor y
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as an Either")
  toEditor (Left x) = SExpList [SymbolAtom "Left", toEditor x]
  toEditor (Right y) = SExpList [SymbolAtom "Right", toEditor y]

implementation (Editorable a, Editorable b) => Editorable (a, b) where
  fromEditor (SExpList [x, y]) = MkPair <$> fromEditor x <*> fromEditor y
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a Pair")
  toEditor (x, y) = SExpList [toEditor x, toEditor y]

implementation Editorable SourceLocation where
  fromEditor (SExpList [SymbolAtom "FileLoc", x, y, z]) =
    FileLoc <$> fromEditor x <*> fromEditor y <*> fromEditor z
  fromEditor x = Left (Msg $ "Can't parse the SExp " ++ show x ++ " as a SourceLocation")
  toEditor (FileLoc x y z) =
    SExpList [SymbolAtom "FileLoc", toEditor x, toEditor y, toEditor z]
