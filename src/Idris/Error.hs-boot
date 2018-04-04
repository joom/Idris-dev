module Idris.Error where

import Idris.Core.TT
import {-# SOURCE #-} Idris.AbsSyntaxTree

tclift :: TC a -> Idris a
