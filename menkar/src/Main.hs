module Main where

import qualified System.Environment
import Control.Monad
import System.IO

doUntilFail :: Monad m => m Bool -> m ()
doUntilFail action = do
  succes <- action
  when succes $ doUntilFail action

prompt :: String -> IO String
prompt text = do
  putStr text
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
  print args
  putStrLn "Type 'quit' to quit, 'help' for help."
  doUntilFail consumeCommand
  return ()
