module Menkar.Main where

import qualified System.Environment
import Control.Monad
import System.IO

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

main :: IO ()
main = do
  args <- (System.Environment.getArgs :: IO [String])
  case args of
    [arg0] -> do
      code <- readFile arg0
      putStrLn "Type 'quit' to quit, 'help' for help."
      doUntilFail consumeCommand
      return ()
    xs -> do
      putStrLn "This program should be given a file path as its sole argument."
