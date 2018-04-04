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
import System.IO

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Core.Evaluate
import Idris.Core.Elaborate
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.Error
import Idris.Reflection
import Idris.SExp
import Idris.Output

-- | Simple function to parse a string like "Language.Reflection.TT"
-- into the 'Name' that refers to it.
namify :: Monad m => String -> m Name
namify s = case reverse (splitOn "." s) of
  [] -> fail "Empty string"
  [x] -> return $ sUN x
  (x:xs) -> return $ sNS (sUN x) xs

-- | Takes @Elab a@ and returns @a@. Otherwise fails.
tyInElab :: Monad m => Type -> m Type
tyInElab (App _ (P _ n _) ty) | n == tacN "Elab" = return ty
tyInElab x = fail $ "The term " ++ show x ++ " is not an Elab type"

-- | Collect the non-arrow types in a given type.
-- If the input is the syntax tree for @Bool -> Nat@, then the result should
-- be a list of the syntax trees for @Bool@ and @Nat@.
collectTypes :: Monad m => Type -> m [Type]
collectTypes (Bind _ (Pi _ _ t1 _) t2) = (t1 :) <$> collectTypes t2
collectTypes (Proj t _) = fail "Don't know how to collect Proj"
collectTypes t = return [t]

-- | Where all the action happens.
elabEditAt
  :: FilePath -- ^ The file name in which the Elab action is run
  -> String -- ^ The name of the action
  -> Int -- ^ The line number the action is run on
  -> [SExp] -- ^ The arguments to the action
  -> Idris ()
elabEditAt fn nameStr l args =
  do ctxt <- getContext
     ist <- getIState
     name <- namify nameStr
     -- 1) lookup the name and type of the editor action
     (tacTT, ty) <- elabVal toplevel ERHS (PRef NoFC [] name)
     ns <- case tacTT of
             P _ ns _ -> return ns
             _ -> fail $ "The term " ++ show tacTT ++ " is not a variable reference"
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
       fail $ "Editor action has " ++ show countCollected
            ++ " arguments but only " ++ show countArgs ++ " are given"
     -- 4) call fromEditor for each of the SExps and get Terms
     --   * reflect Haskell SExps to Idris SExp ASTs
     rawArgs <- forM (zip collected args) $ \(argTy, sexp) -> do
         sexpPTerm <- tclift $ (delab ist . fst) <$> check ctxt [] (reflectSExp sexp)
         let pterm = PApp NoFC (PRef NoFC [] (editN "fromEditor"))
                               [ PImp 1 True [] (sUN "a") (delab ist argTy)
                               , PExp 1 [] (sMN 0 "arg") sexpPTerm ]
         -- Elaborate `pterm` into TT for interface resolution
         (tm, _) <- elabVal toplevel ERHS pterm
         let tm' = normalise ctxt [] tm
         (tm'', _) <- elaborate "(toplevel)" ctxt
            (idris_datatypes ist) (idris_name ist) (sMN 0 "editElab")
            Erased initEState
            (runElabAction toplevel ist NoFC [] tm' [])
         return $ forget tm''
     -- 5) build up a Term which is a function application
     --    of the original tactic and all the functions
     (app, _) <- tclift $ check ctxt [] (raw_apply (Var ns) rawArgs)
     -- 6) run the tactic
     lastTyInElab <- tyInElab (last collected)
     (res, _) <- tclift $ elaborateTC "(toplevel)" ctxt
                   (idris_datatypes ist) (idris_name ist) (sMN 0 "editElab")
                   lastTyInElab initEState
                   (runElabAction toplevel ist NoFC [] app [])
     -- 7) call toEditor on the result
     let pterm = PApp NoFC (PRef NoFC [] (editN "toEditor"))
                               [ PImp 1 True [] (sUN "a") (delab ist lastTyInElab)
                               , PExp 1 [] (sMN 0 "arg") (delab ist res) ]
     (tm, _) <- elabVal toplevel ERHS pterm
     let tm' = normalise ctxt [] tm
     -- reify the SExp TT term into a Haskell SExp
     (resSExp, _) <- tclift $ elaborateTC "(toplevel)" ctxt
       (idris_datatypes ist) (idris_name ist) (sMN 0 "editElab")
       Erased initEState
       (runElabAction toplevel ist NoFC [] tm' [] >>= reifySExp)
     -- send it back to the editor
     case idris_outputmode ist of
       RawOutput _ -> fail "Not in IDE mode"
       IdeMode n h -> do
         runIO . hPutStrLn h $ convSExp "return"
           [SymbolAtom "ok", resSExp, SexpList []] n
