module Language.Reflection.Editor

import Language.Reflection
import Language.Reflection.Elab
import Language.Reflection.Errors

%access public export

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
    where mid = assert_total $ foldr (++) "" (intersperse " " (map show l))

implementation Eq SExp where
  (StringAtom x) == (StringAtom y) = x == y
  (BoolAtom x) == (BoolAtom y) = x == y
  (IntegerAtom x) == (IntegerAtom y) = x == y
  (SymbolAtom x) == (SymbolAtom y) = x == y
  (SExpList xs) == (SExpList ys) = assert_total (xs == ys)
  _ == _ = False

implementation Cast SExp String where
  cast x = assert_total (show x)

||| Limits the types that the compiler knows how to specially serialize
||| into S-expressions. It is different from the compiler's `SExpable`
||| in that certain reflection types like `TTName`, `TT`, `TyDecl`, `DataDefn`,
||| `FunDefn`, `FunClause` are primitives, which go through delaboration
||| and pretty printing in the compiler.
interface Editorable a where
  fromEditor : SExp -> Elab a
  toEditor : a -> Elab SExp

-- These primitives should never appear when we are normalizing terms
-- when we run tactics in the editor or when we use Editorable in the REPL.
-- However, they will appear when we run the compiled program
implementation Editorable TT where
  fromEditor x = prim__fromEditor x
  toEditor x = prim__toEditor x

implementation Editorable TyDecl where
  fromEditor x = prim__fromEditor x
  toEditor x = prim__toEditor x

implementation Editorable DataDefn where
  fromEditor x = prim__fromEditor x
  toEditor x = prim__toEditor x

implementation Editorable (FunDefn TT) where
  fromEditor x = prim__fromEditor x
  toEditor x = prim__toEditor x

implementation Editorable (FunClause TT) where
  fromEditor x = prim__fromEditor x
  toEditor x = prim__toEditor x

implementation Editorable TTName where
  fromEditor (StringAtom s) = namify s
    where
      namify : String -> Elab TTName
      namify s =
        case reverse (map pack (splitOn '.' (unpack s))) of
          [] => fail [TextPart "Empty string can't be a TTName"]
          [x] => pure (UN x)
          (x :: xs) => pure (NS (UN x) xs)
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{TTName} ]

  toEditor n = StringAtom <$> stringify n
    where
      stringify : TTName -> Elab String
      stringify (UN x) = pure x
      stringify (NS x []) = stringify x
      stringify (NS x xs) =
        pure $ concat (intersperse "." (reverse ("" :: xs))) ++ !(stringify x)
      stringify (MN i x) = pure ("__" ++ x ++ show i)
      stringify n'@(SN sn) =
        fail [ TextPart "Don't know how to make"
             , NamePart n', TextPart "into"
             , NamePart `{StringAtom}]

implementation Editorable SExp where
  fromEditor x = pure x
  toEditor x = pure x

implementation Editorable Unit where
  fromEditor (SExpList []) = pure ()
  fromEditor x = fail [ TextPart "Can't parse the"
                      , NamePart `{SExp}
                      , TextPart (show x ++ "as a")
                      , NamePart `{Unit} ]
  toEditor () = pure (SExpList [])

implementation Editorable Void where
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{Void} ]
  toEditor _ impossible

implementation Editorable String where
  fromEditor (StringAtom s) = pure s
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{{String}} ]
  toEditor = pure . StringAtom

implementation Editorable Char where
  fromEditor (StringAtom s) = case unpack s of
                                   [c] => pure c
                                   _ => fail [TextPart "More than one character"]
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{{Char}} ]
  toEditor c = pure (StringAtom (pack [c]))

implementation Editorable Integer where
  fromEditor (IntegerAtom n) = pure n
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as an")
         , NamePart `{{Integer}} ]
  toEditor = pure . IntegerAtom

implementation Editorable Int where
  fromEditor (IntegerAtom n) = pure (fromInteger n)
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as an")
         , NamePart `{{Int}} ]
  toEditor = pure . IntegerAtom . cast

implementation Editorable Nat where
  fromEditor (IntegerAtom n) = pure (fromInteger n)
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{Nat} ]
  toEditor = pure . IntegerAtom . cast

implementation Editorable Bool where
  fromEditor (BoolAtom b) = pure b
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{Bool} ]
  toEditor = pure . BoolAtom

implementation Editorable a => Editorable (List a) where
  fromEditor (SExpList xs) = traverse fromEditor xs
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{List} ]
  toEditor xs = SExpList <$> traverse toEditor xs

implementation Editorable a => Editorable (Maybe a) where
  fromEditor (SExpList [SymbolAtom "Nothing"]) = pure Nothing
  fromEditor (SExpList [SymbolAtom "Just", x]) = Just <$> fromEditor x
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{Maybe} ]
  toEditor (Just x) = pure $ SExpList [SymbolAtom "Just", !(toEditor x)]
  toEditor Nothing = pure $ SExpList [SymbolAtom "Nothing"]

implementation (Editorable a, Editorable b) => Editorable (Either a b) where
  fromEditor (SExpList [SymbolAtom "Left", x]) = Left <$> fromEditor x
  fromEditor (SExpList [SymbolAtom "Right", y]) = Right <$> fromEditor y
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as an")
         , NamePart `{Either} ]
  toEditor (Left x) = pure $ SExpList [SymbolAtom "Left", !(toEditor x)]
  toEditor (Right y) = pure $ SExpList [SymbolAtom "Right", !(toEditor y)]

implementation (Editorable a, Editorable b) => Editorable (a, b) where
  fromEditor (SExpList [x, y]) = MkPair <$> fromEditor x <*> fromEditor y
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{Pair} ]
  toEditor (x, y) = pure $ SExpList [!(toEditor x), !(toEditor y)]

implementation Editorable SourceLocation where
  fromEditor (SExpList [SymbolAtom "FileLoc", x, y, z]) =
    FileLoc <$> fromEditor x <*> fromEditor y <*> fromEditor z
  fromEditor x =
    fail [ TextPart "Can't parse the"
         , NamePart `{SExp}
         , TextPart (show x ++ "as a")
         , NamePart `{SourceLocation} ]
  toEditor (FileLoc x y z) =
    pure $ SExpList [SymbolAtom "FileLoc", !(toEditor x), !(toEditor y), !(toEditor z)]
