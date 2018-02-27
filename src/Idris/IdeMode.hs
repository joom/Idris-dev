{-|
Module      : Idris.IdeMode
Description : Idris' IDE Mode

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.IdeMode(WhatDocs(..), IdeModeCommand(..), sexpToCommand, Opt(..), ideModeEpoch, getLen, getNChar) where

import Idris.Core.Binary ()
import Idris.Core.TT
import Idris.SExp

import Numeric
import System.IO

getNChar :: Handle -> Int -> String -> IO (String)
getNChar _ 0 s = return (reverse s)
getNChar h n s = do c <- hGetChar h
                    getNChar h (n - 1) (c : s)

getLen :: Handle -> IO (Either Err Int)
getLen h = do s <- getNChar h 6 ""
              case readHex s of
                ((num, ""):_) -> return $ Right num
                _             -> return $ Left . Msg $ "Couldn't read length " ++ s

data Opt = ShowImpl | ErrContext deriving Show

data WhatDocs = Overview | Full

data IdeModeCommand = REPLCompletions String
                    | Interpret String
                    | TypeOf String
                    | ElabEdit String [SExp] Int
                    | CaseSplit Int String
                    | AddClause Int String
                    | AddProofClause Int String
                    | AddMissing Int String
                    | MakeWithBlock Int String
                    | MakeCaseBlock Int String
                    | ProofSearch Bool Int String [String] (Maybe Int) -- ^^ Recursive?, line, name, hints, depth
                    | MakeLemma Int String
                    | LoadFile String (Maybe Int)
                    | DocsFor String WhatDocs
                    | Apropos String
                    | GetOpts
                    | SetOpt Opt Bool
                    | Metavariables Int -- ^^ the Int is the column count for pretty-printing
                    | WhoCalls String
                    | CallsWho String
                    | BrowseNS String
                    | TermNormalise [(Name, Bool)] Term
                    | TermShowImplicits [(Name, Bool)] Term
                    | TermNoImplicits [(Name, Bool)] Term
                    | TermElab [(Name, Bool)] Term
                    | PrintDef String
                    | ErrString Err
                    | ErrPPrint Err
                    | GetIdrisVersion

sexpToCommand :: SExp -> Maybe IdeModeCommand
sexpToCommand (SexpList ([x]))                                                              = sexpToCommand x
sexpToCommand (SexpList [SymbolAtom "interpret", StringAtom cmd])                           = Just (Interpret cmd)
sexpToCommand (SexpList [SymbolAtom "repl-completions", StringAtom prefix])                 = Just (REPLCompletions prefix)
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename, IntegerAtom line])    = Just (LoadFile filename (Just (fromInteger line)))
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename])                      = Just (LoadFile filename Nothing)
sexpToCommand (SexpList [SymbolAtom "type-of", StringAtom name])                            = Just (TypeOf name)
sexpToCommand (SexpList [SymbolAtom "elab-edit", StringAtom name, SexpList args, IntegerAtom line]) =
    Just (ElabEdit name args (fromInteger line))
sexpToCommand (SexpList [SymbolAtom "case-split", IntegerAtom line, StringAtom name])       = Just (CaseSplit (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-clause", IntegerAtom line, StringAtom name])       = Just (AddClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-proof-clause", IntegerAtom line, StringAtom name]) = Just (AddProofClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-missing", IntegerAtom line, StringAtom name])      = Just (AddMissing (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "make-with", IntegerAtom line, StringAtom name])        = Just (MakeWithBlock (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "make-case", IntegerAtom line, StringAtom name])        = Just (MakeCaseBlock (fromInteger line) name)
-- The Boolean in ProofSearch means "search recursively"
-- If it's False, that means "refine", i.e. apply the name and fill in any
-- arguments which can be done by unification.
sexpToCommand (SexpList (SymbolAtom "proof-search" : IntegerAtom line : StringAtom name : rest))
  | [] <- rest = Just (ProofSearch True (fromInteger line) name [] Nothing)
  | [SexpList hintexp] <- rest
  ,  Just hints <- getHints hintexp = Just (ProofSearch True (fromInteger line) name hints Nothing)
  | [SexpList hintexp, IntegerAtom depth] <- rest
 , Just hints <- getHints hintexp = Just (ProofSearch True (fromInteger line) name hints (Just (fromInteger depth)))
 where getHints = mapM (\h -> case h of
                                StringAtom s -> Just s
                                _            -> Nothing)
sexpToCommand (SexpList [SymbolAtom "make-lemma", IntegerAtom line, StringAtom name])   = Just (MakeLemma (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "refine", IntegerAtom line, StringAtom name, StringAtom hint]) = Just (ProofSearch False (fromInteger line) name [hint] Nothing)
sexpToCommand (SexpList [SymbolAtom "docs-for", StringAtom name])                       = Just (DocsFor name Full)
sexpToCommand (SexpList [SymbolAtom "docs-for", StringAtom name, SymbolAtom s])
  | Just w <- lookup s opts                                                             = Just (DocsFor name w)
    where opts = [("overview", Overview), ("full", Full)]
sexpToCommand (SexpList [SymbolAtom "apropos", StringAtom search])                      = Just (Apropos search)
sexpToCommand (SymbolAtom "get-options")                                                = Just GetOpts
sexpToCommand (SexpList [SymbolAtom "set-option", SymbolAtom s, BoolAtom b])
  | Just opt <- lookup s opts                                                           = Just (SetOpt opt b)
    where opts = [("show-implicits", ShowImpl), ("error-context", ErrContext)] --TODO support more options. Issue #1611 in the Issue tracker. https://github.com/idris-lang/Idris-dev/issues/1611
sexpToCommand (SexpList [SymbolAtom "metavariables", IntegerAtom cols])                 = Just (Metavariables (fromIntegral cols))
sexpToCommand (SexpList [SymbolAtom "who-calls", StringAtom name])                      = Just (WhoCalls name)
sexpToCommand (SexpList [SymbolAtom "calls-who", StringAtom name])                      = Just (CallsWho name)
sexpToCommand (SexpList [SymbolAtom "browse-namespace", StringAtom ns])                 = Just (BrowseNS ns)
sexpToCommand (SexpList [SymbolAtom "normalise-term", StringAtom encoded])              = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermNormalise bnd tm)
sexpToCommand (SexpList [SymbolAtom "show-term-implicits", StringAtom encoded])         = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermShowImplicits bnd tm)
sexpToCommand (SexpList [SymbolAtom "hide-term-implicits", StringAtom encoded])         = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermNoImplicits bnd tm)
sexpToCommand (SexpList [SymbolAtom "elaborate-term", StringAtom encoded])              = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermElab bnd tm)
sexpToCommand (SexpList [SymbolAtom "print-definition", StringAtom name])               = Just (PrintDef name)
sexpToCommand (SexpList [SymbolAtom "error-string", StringAtom encoded])                = Just . ErrString . decodeErr $ encoded
sexpToCommand (SexpList [SymbolAtom "error-pprint", StringAtom encoded])                = Just . ErrPPrint . decodeErr $ encoded
sexpToCommand (SymbolAtom "version")                                                    = Just GetIdrisVersion
sexpToCommand _                                                                         = Nothing

-- | The version of the IDE mode command set. Increment this when you
-- change it so clients can adapt.
ideModeEpoch :: Int
ideModeEpoch = 1
