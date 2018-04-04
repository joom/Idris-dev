module Idris.AbsSyntaxTree where

import Idris.Core.TT

import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

data IState

idris_sourcemap :: IState -> SourceMap

type Idris = StateT IState (ExceptT Err IO)

updateSourceMap :: SourceMap -> Idris ()
