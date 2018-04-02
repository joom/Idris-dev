module Idris.Parser where

import Idris.AbsSyntaxTree
import Idris.Parser.Stack

parseExpr :: IState -> String -> Either ParseError PTerm
parseFnDecl :: IState -> String -> Either ParseError PDecl
