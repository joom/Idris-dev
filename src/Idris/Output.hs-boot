module Idris.Output where

import Idris.Core.TT
import Util.Pretty

type OutputDoc = Doc OutputAnnotation

class Message a where
  messageExtent :: a -> FC
  messageText :: a -> OutputDoc
  messageSource :: a -> Maybe String
