module Idris.Reflection where

import Idris.Core.TT
import {-# SOURCE #-} Idris.AbsSyntaxTree
import Idris.SExp

-- The functions in Idris.Reflection that are used in Idris.Core.Evaluate
-- for edit-time tactics

editN :: String -> Name
reflm :: String -> Name

reifySExp :: Term -> ElabD SExp

reflect :: Term -> Raw
