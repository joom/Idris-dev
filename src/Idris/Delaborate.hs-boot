module Idris.Delaborate where

import {-# SOURCE #-} Idris.AbsSyntaxTree
import Idris.Core.TT

delabSugared :: IState -> TT Name -> PTerm
