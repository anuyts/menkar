module Menkar.Main where

import qualified System.Environment
import Control.Monad
import System.IO
import qualified Menkar.Parser as P
import qualified Menkar.Scoper as S
import Menkar.TC.Monad.DTT
import Menkar.Fine
import Menkar.TC

import Control.Exception.AssertFalse

import Data.Functor.Identity
import GHC.Generics (U1 (..))
import Control.Monad.Except

printConstraint :: Constraint U1 U1 U1 -> IO ()
printConstraint c = do
  putStrLn $ "Constraint " ++ show (constraint'id c) ++ ":"
  putStrLn $ show $ constraint'judgement c
  putStrLn ""
  putStrLn $ constraint'reason c
  case constraint'parent c of
    Nothing -> return ()
    Just parent -> do
      putStrLn ""
      printConstraint parent

printReport :: TCReport -> IO ()
printReport r = do
  putStrLn $ _tcReport'reason r
  putStrLn ""
  printConstraint $ _tcReport'parent r
  

------------------------------------

{-| Repeats 'action' until it returns 'False' -}
doUntilFail :: Monad m => m Bool -> m ()
doUntilFail action = do
  succes <- action
  when succes $ doUntilFail action

{-| prints 'prefix' as a sign that the user should provide input; then returns the input. -}
prompt :: String -> IO String
prompt prefix = do
  putStr prefix
  hFlush stdout
  getLine

giveHelp :: IO ()
giveHelp = putStrLn "Type 'quit' to quit. Other than that, I ain't got much to tell ya, to be fair."

runCommand :: String -> IO ()
runCommand "help" = giveHelp
runCommand command = putStrLn command

consumeCommand :: IO Bool
consumeCommand = do
  command <- prompt "> "
  if command == "quit"
    then return False
    else do
      runCommand command
      return True

interactiveMode :: TCState m -> IO ()
interactiveMode s = do
  putStrLn "-------------------------"
  putStrLn "START OF INTERACTIVE MODE"
  putStrLn "-------------------------"
  putStrLn "Type 'quit' to quit, 'help' for help."
  doUntilFail consumeCommand
  return ()

mainArgs :: [String] -> IO ()
mainArgs args = do
  case args of
    [path] -> do
      code <- readFile path
      let errorOrRawFile = P.parse P.file path code
      case errorOrRawFile of
        Left e -> putStrLn $ show e
        Right rawFile -> do
          let tcResult = runExcept $ flip runTC initTCState $ do
                fineFile <- S.file (CtxEmpty U1) rawFile
                addNewConstraint
                  (JudEntry (CtxEmpty U1) fineFile)
                  Nothing
                  "Type-checking the file."
          case tcResult of
            Right ((), s) -> do
              interactiveMode s
            Left e -> case e of
              TCErrorConstraintBound -> unreachable
              TCErrorBlocked reason -> unreachable
              TCErrorTCFail report s -> do
                putStrLn "------------"
                putStrLn "TYPING ERROR"
                putStrLn "------------"
                printReport report
                interactiveMode s
              TCErrorScopeFail msg -> do
                putStrLn "-------------"
                putStrLn "SCOPING ERROR"
                putStrLn "-------------"
                putStrLn msg
    xs -> do
      putStrLn "This program should be given a file path as its sole argument."

main :: IO ()
main = mainArgs =<< (System.Environment.getArgs :: IO [String])
