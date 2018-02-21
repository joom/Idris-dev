module Idris.Core.Typecheck where

import Idris.Core.TT
import {-# SOURCE #-} Idris.Core.Evaluate

check :: Context -> Env -> Raw -> TC (Term, Type)
