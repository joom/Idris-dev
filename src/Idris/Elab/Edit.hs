{-# LANGUAGE LambdaCase #-}
{-|
Module      : Idris.Elab.Edit
Description : Handles editor interaction with Elab actions.
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Elab.Edit where

import Control.Monad
import Data.List.Split
import qualified Data.Text as T

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Core.Evaluate
import Idris.Core.Elaborate
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Elab.Term
import Idris.Error
import Idris.Reflection
import Idris.SExp
import Idris.Output

namify :: String -> Idris Name
namify s = case reverse (splitOn "." s) of
  [] -> fail "Empty string"
  [x] -> return $ sUN x
  (x:xs) -> return $ sNS (sUN x) xs

-- | Collect the non-arrow types in a given type.
-- If the input is the syntax tree for @Bool -> Nat@, then the result should
-- be a list of the syntax trees for @Bool@ and @Nat@.
collectTypes :: Type -> Idris [Type]
collectTypes (Bind _ (Pi _ _ t1 _) t2) = (t1 :) <$> collectTypes t2
collectTypes (Proj t _) = fail "Don't know how to collect Proj"
collectTypes t = return [t]

elabEditAt
  :: FilePath -- ^ The file name in which the Elab action is run
  -> String -- ^ The name of the action
  -> Int -- ^ The line number the action is run on
  -> [SExp] -- ^ The tactic expression, of type 'Elab a' for some 'a'.
  -> Idris ()
elabEditAt fn nameStr l args =
  do ctxt <- getContext
     ist <- getIState
     name <- namify nameStr
     -- 1) lookup the name and type of the editor action
     (ns, ty) <- case lookupTyNameExact name ctxt of
                   Nothing -> fail "No such editor action"
                   Just x -> return x
     -- 2) check if the tactic has been declared "%editor"
     case lookupCtxtExact ns (idris_flags ist) of
       Nothing -> fail "The action is not declared anything"
       Just opts -> unless (EditorAction `elem` opts) $
                      fail "The action is not declared %editor"
     -- 3) check if the number of arguments in the type match with the given arguments
     -- note that `collected` also includes the output type
     collected <- collectTypes ty
     let (countArgs, countCollected) = (length args, length collected - 1)
     unless (countArgs == countCollected) $
       fail $ "Editor action argument number (" ++ show countCollected
            ++ ") doesn't match given arguments (" ++ show countArgs ++ ")"
     -- 4) call fromEditor for each of the SExps and get Terms
     --   * reflect Haskell SExps to Idris SExp ASTs
     rawArgs <- forM (zip collected args) $ \(argTy, sexp) -> do
         let from = raw_apply (Var $ editN "fromEditor")
                    [ forget argTy
                    -- TODO 1: we don't know that the type is TT
                    -- TODO 2: we don't know the namespace of the implementation yet,
                    -- it might not be editNS
                    , Var (editNS (SN $ ImplementationN (editN "Editorable") [T.pack "TT"]))
                    , reflectSExp sexp]
         (tm, maybeTy) <- tclift $ check ctxt [] from
         let tm' = normalise ctxt [] tm
         (tm'', _) <- tclift $ elaborate "(toplevel)" ctxt emptyContext 0 (sMN 0 "editElab")
            Erased initEState (reifyMaybe tm' >>=
              \case Just x -> return x ; _ -> fail "Nothing")
         return $ forget tm''
     -- 5) build up a Term which is a function application
     --    of the original tactic and all the functions
     let app = raw_apply (Var ns) rawArgs
     (app', _) <- tclift $ check ctxt [] app
    -- 6) run the tactic
     (res, _) <- tclift $ elaborate "(toplevel)" ctxt emptyContext 0 (sMN 0 "editElab")
            Erased initEState (runElabAction toplevel ist NoFC [] app' [] >>= reifyTT)
            -- TODO fix reifyTT!!! It doesn't have to be TT. take toEditor into account!
     -- 7) delaborate into a PTerm
     -- iputStrLn $ show res
     let pterm = delabSugared ist (inlineSmall ctxt [] res)
     -- 8) pretty print the result
     iRenderResult $ prettyIst ist pterm
