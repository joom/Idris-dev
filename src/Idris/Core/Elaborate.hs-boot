module Idris.Core.Elaborate where

import Idris.Core.TT
import {-# SOURCE #-} Idris.Core.ProofState
import Control.Monad.State.Strict
import {-# SOURCE #-} Idris.Core.Evaluate

data ElabState aux
type Elab' aux a = StateT (ElabState aux) TC a

runElab :: aux -> Elab' aux a -> ProofState -> TC (a, ElabState aux)

elaborate :: String -> Context -> Ctxt TypeInfo -> Int -> Name -> Type -> aux -> Elab' aux a -> TC (a, String)
