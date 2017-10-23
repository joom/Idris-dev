{-|
Module      : Idris.ElabAction
Description : Handles editor interaction with Elab actions.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.ElabAction where

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Core.Evaluate
import Idris.Core.Elaborate
import Idris.Core.TT
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.Error
import Idris.Reflection
import Idris.Output

data ActionData =
    TermData PTerm
  | TyData
  | FunData

elabActionAt :: FilePath -> Int -> Name -> PTerm -> Idris ()
elabActionAt fn l name pterm
  = do
       (tm, ty) <- elabVal toplevel ERHS pterm
       ctxt <- getContext
       ist <- getIState
       let info = toplevel
       let fc = NoFC
       let ns = []
       (ElabResult tm' defer is ctxt' newDecls highlights newGName, log) <-
          tclift $ elaborate "(toplevel)" ctxt (idris_datatypes ist) (idris_name ist)
                 (sMN 0 "elabAction") ty initEState
                 (transformErr RunningElabScript
                   (erun fc (do
                                tm <- runElabAction info ist fc [] tm ns
                                EState is _ impls highlights _ _ <- getAux
                                ctxt <- get_context
                                let ds = [] -- todo
                                log <- getLog
                                newGName <- get_global_nextname
                                return (ElabResult tm ds (map snd is) ctxt impls highlights newGName))))
       ist <- getIState
       let tm'' = inlineSmall ctxt [] tm'
       let pterm' = delabSugared ist tm''
       iRenderResult $ prettyIst ist pterm'

