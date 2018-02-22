module Idris.AbsSyntax where

import Idris.Core.TT
import {-# SOURCE #-} Idris.AbsSyntaxTree

addImpl :: [Name] -> IState -> PTerm -> PTerm
