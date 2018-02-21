module Idris.Parser where

import {-# SOURCE #-} Idris.AbsSyntaxTree
import Idris.Parser.Stack

parseExpr :: IState -> String -> Either ParseError PTerm
