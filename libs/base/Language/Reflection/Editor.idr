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
  fromEditor : SExp -> Maybe a
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
                        [] => Nothing
                        [x] => Just (UN x)
                        (x :: xs) => Just (NS (UN x) xs)
  fromEditor _ = Nothing

  toEditor n = StringAtom (stringify n)
    where
      stringify (UN x) = x
      stringify (NS x []) = stringify x
      stringify (NS x xs) =
        concat (intersperse "." (reverse ("" :: xs))) ++ stringify x
      stringify (MN i x) = "__" ++ x ++ show i
      stringify (SN sn) = "" -- TODO fix

implementation Editorable Unit where
  fromEditor (SExpList []) = Just ()
  fromEditor _ = Nothing
  toEditor () = SExpList []

implementation Editorable Void where
  fromEditor _ = Nothing
  toEditor _ impossible

implementation Editorable String where
  fromEditor (StringAtom s) = Just s
  fromEditor _ = Nothing
  toEditor = StringAtom

implementation Editorable Char where
  fromEditor (StringAtom s) = case unpack s of
                                   [c] => Just c
                                   _ => Nothing
  fromEditor _ = Nothing
  toEditor c = StringAtom (pack [c])

implementation Editorable Integer where
  fromEditor (IntegerAtom n) = Just n
  fromEditor _ = Nothing
  toEditor = IntegerAtom

implementation Editorable Int where
  fromEditor (IntegerAtom n) = Just (fromInteger n)
  fromEditor _ = Nothing
  toEditor = IntegerAtom . cast

implementation Editorable Nat where
  fromEditor (IntegerAtom n) = Just (fromInteger n)
  fromEditor _ = Nothing
  toEditor = IntegerAtom . cast

implementation Editorable Bool where
  fromEditor (BoolAtom b) = Just b
  fromEditor _ = Nothing
  toEditor = BoolAtom

implementation Editorable a => Editorable (List a) where
  fromEditor (SExpList xs) = sequence (map fromEditor xs)
  fromEditor _ = Nothing
  toEditor xs = SExpList (map toEditor xs)

implementation Editorable a => Editorable (Maybe a) where
  fromEditor (SExpList [SymbolAtom "Nothing"]) = Just Nothing
  fromEditor (SExpList [SymbolAtom "Just", x]) = Just <$> fromEditor x
  fromEditor _ = Nothing
  toEditor (Just x) = SExpList [SymbolAtom "Just", toEditor x]
  toEditor Nothing = SExpList [SymbolAtom "Nothing"]

implementation (Editorable a, Editorable b) => Editorable (Either a b) where
  fromEditor (SExpList [SymbolAtom "Left", x]) = Left <$> fromEditor x
  fromEditor (SExpList [SymbolAtom "Right", y]) = Right <$> fromEditor y
  fromEditor _ = Nothing
  toEditor (Left x) = SExpList [SymbolAtom "Left", toEditor x]
  toEditor (Right y) = SExpList [SymbolAtom "Right", toEditor y]

implementation (Editorable a, Editorable b) => Editorable (a, b) where
  fromEditor (SExpList [x, y]) = MkPair <$> fromEditor x <*> fromEditor y
  fromEditor _ = Nothing
  toEditor (x, y) = SExpList [toEditor x, toEditor y]

implementation Editorable SourceLocation where
  fromEditor (SExpList [SymbolAtom "FileLoc", x, y, z]) =
    FileLoc <$> fromEditor x <*> fromEditor y <*> fromEditor z
  fromEditor _ = Nothing
  toEditor (FileLoc x y z) =
    SExpList [SymbolAtom "FileLoc", toEditor x, toEditor y, toEditor z]
