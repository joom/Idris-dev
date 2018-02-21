module Idris.Elab.Term where

import {-# SOURCE #-} Idris.AbsSyntaxTree
import Idris.Core.TT

data ElabMode = ETyDecl | ETransLHS | ELHS | EImpossible | ERHS
instance Eq ElabMode

data ElabResult
resultTerm :: ElabResult -> Term

runElabAction :: ElabInfo -> IState -> FC -> Env -> Term -> [String] -> ElabD Term

build :: IState -> ElabInfo -> ElabMode -> FnOpts -> Name -> PTerm -> ElabD ElabResult
