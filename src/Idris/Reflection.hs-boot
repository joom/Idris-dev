module Idris.Reflection where

import Idris.Core.TT
import {-# SOURCE #-} Idris.AbsSyntaxTree
import Idris.SExp

-- The functions in Idris.Reflection that are used in Idris.Core.Evaluate
-- for edit-time tactics

editN :: String -> Name
editNS :: Name -> Name
reflm :: String -> Name

reifySExp :: Term -> ElabD SExp
reifyTT :: Term -> ElabD Term

reflect :: Term -> Raw
reflectMaybe :: Maybe Raw -> Raw -> Raw
reflectSExp :: SExp -> Raw
