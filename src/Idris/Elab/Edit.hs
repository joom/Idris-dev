{-|
Module      : Idris.Elab.Edit
Description : Handles editor interaction with Elab actions.
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Elab.Edit where

import Control.Monad
import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Core.Evaluate
import Idris.Core.Elaborate
import Idris.Core.TT
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.Error
import Idris.IdeMode
import Idris.Reflection
import Idris.Output

-- | Collect the non-arrow types in a given type.
-- If the input is the syntax tree for @Bool -> Nat@, then the result should
-- be a list of the syntax trees for @Bool@ and @Nat@.
collectTypes :: Type -> Idris [Type]
collectTypes (Bind _ (Pi _ _ t1 _) t2) = (t1 :) <$> collectTypes t2
collectTypes (Proj t _) = fail "Don't know how to collect Proj"
collectTypes t = return [t]

-- | Gets a list of non-arrow types and returns the ones that do not have
-- an implementation for the Editorable interface.
getNotEditorables :: [Type] -> Idris [Type]
getNotEditorables l = undefined

convertSExpArgs :: Name -> [SExp] -> Idris [PTerm]
convertSExpArgs name args = -- TODO elab
  do i <- getIState
     -- 1) lookup the name and type of the editor action
     ctxt <- getContext
     (ns, ty) <- case lookupTyNameExact name ctxt of
                   Nothing -> fail "No such editor action"
                   Just x -> return x
     -- 2) check if the tactic has been declared "%editor"
     case lookupCtxtExact ns (idris_flags i) of
       Nothing -> fail "The action is not declared anything"
       Just opts -> unless (EditorAction `elem` opts) $
                      fail "The action is not declared %editor"
     -- 3) check if the number of arguments in the type match with the given arguments
     collected <- collectTypes ty
     let (countArgs, countCollected) = (length args, length collected)
     unless (countArgs == countCollected) $
       fail $ "Editor action argument number (" ++ show countCollected
            ++ ") given arguments (" ++ show countArgs ++ ")"
     -- 4) get the Editorable instances of each of the types
            -- overriding instances?
            -- only override in interpreter, not the compiler
     -- 5) call fromEditor for each of the SExps and get PTerms
     --   * reflect Haskell SExps to Idris SExp ASTs
     -- 6) build up a PTerm which is a function application
     --    of the original tactic and all the functions
     undefined
     -- case parseExpr i term of
     --   Left err -> iPrintError . show . parseErrorDoc $ err
     --   Right t -> return [t] -- process fn (ElabEditAt line (sUN name) t)

elabEditAt
  :: FilePath -- ^ The file name in which the Elab action is run
  -> Name -- ^ The name of the action
  -> [PTerm] -- ^ The tactic expression, of type 'Elab a' for some 'a'.
  -> Int -- ^ The line number the action is run on
  -> Idris ()
elabEditAt fn name args l = do
  -- TODO fix
  -- (tm, ty) <- elabVal toplevel ERHS pterm
  ctxt <- getContext
  ist <- getIState
  -- (tm', _) <- tclift $ elaborate "(toplevel)" ctxt (idris_datatypes ist)
  --         (idris_name ist) (sMN 0 "elabAction") ty initEState
  --         (transformErr RunningElabScript
  --         (erun NoFC (runElabAction toplevel ist NoFC [] tm [] >>= reifyTT)))
  -- let pterm' = delabSugared ist (inlineSmall ctxt [] tm')
  -- iRenderResult $ prettyIst ist pterm'
  undefined

