module Helper
  ( TestM (..)
  , runCheck
  , checkFile
  , parseOrFail
  , replace
  ) where


import Data.Functor.Identity (Identity (..))
import Data.List (isPrefixOf)
import Test.Hspec (expectationFailure)

import Control.Monad.InteractT (Interact (..), run'interact)

import Check.Check (Command (..), Q (..))
import Check.Environment (init'env)
import Check.Error (Error)
import Check.Module (check'module)
import Check.State (empty'state)
import Parser.Parser (parse'module)
import Syntax.Module (Module)


-- | Deterministic stand-in for the interactive console prompter.
-- Proof-search questions are answered with IDK and progress reports are
-- dropped, so tests never block on stdin.
newtype TestM a = TestM { unTestM :: Identity a }


instance Functor TestM where
  fmap f (TestM m) = TestM (fmap f m)


instance Applicative TestM where
  pure = TestM . pure
  TestM f <*> TestM x = TestM (f <*> x)


instance Monad TestM where
  TestM m >>= k = TestM (m >>= unTestM . k)


instance Interact Q TestM where
  request (What'Next _ _) = return IDK
  request (Inform _ _) = return ()


-- | Parse and check a module source without touching stdin.
-- A Left covers both parse errors and whole-module checker failures;
-- per-theorem results mirror what app/Main.hs prints per theorem.
runCheck :: Bool -> String -> Either String [(String, Maybe Error)]
runCheck lem src =
  case parse'module src of
    Left err -> Left err
    Right modul ->
      case runIdentity (unTestM (run'interact empty'state (init'env lem) (check'module modul))) of
        Left err -> Left (show err)
        Right (_, results) -> Right results


-- | Read a .dt file and run 'runCheck' on its contents.
checkFile :: Bool -> FilePath -> IO (Either String [(String, Maybe Error)])
checkFile lem path = runCheck lem <$> readFile path


-- | Parse a source string, failing the test with the parser message on Left.
parseOrFail :: String -> IO Module
parseOrFail src =
  case parse'module src of
    Left err -> expectationFailure ("expected parse success, got: " ++ err) >> fail "unreachable"
    Right modul -> return modul


-- | Replace all occurrences of a needle with a replacement.
replace :: String -> String -> String -> String
replace _ _ [] = []
replace needle repl hay@(c : cs)
  | needle `isPrefixOf` hay = repl ++ replace needle repl (drop (length needle) hay)
  | otherwise = c : replace needle repl cs
