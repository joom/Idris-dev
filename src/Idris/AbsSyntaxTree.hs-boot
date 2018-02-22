module Idris.AbsSyntaxTree where

import {-# SOURCE #-} Idris.Core.Elaborate

data IState
idrisInit :: IState

data EState
initEState :: EState

type ElabD a = Elab' EState a

data ElabInfo

constraintNS :: ElabInfo -> String

toplevel :: ElabInfo

data PTerm

data FnOpt

type FnOpts = [FnOpt]
