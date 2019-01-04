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
import Data.Foldable
import Control.Lens

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

{-
printMetaInfo :: TCState m -> MetaInfo m -> IO ()
printMetaInfo s info = do
  putStrLn $ "Context:"
  putStrLn $ "--------"
  --todo: separate existential from record in MetaInfo
  --putStrLn $ show $ _metaInfo'context info
  putStrLn $ ""
  case _metaInfo'maybeSolution of
    Right solutionInfo -> do
      putStrLn "Solution:"
      putStrLn "---------"
      --todo: print solution to meta
      --putStrLn $ show $ _solutionInfo'solution 
    Left blocks -> do
      putStrLn "Unsolved"
      putStrLn "--------"
      putStrLn $ "Blocking " ++ (show $ length blocks) ++ " constraints."
      --todo: print hampered constraints
  case _metaInfo'maybeParent of
    Nothing -> return ()
    Just parent -> do
      putStrLn $ ""
      putStrLn $ "Trace of creation:"
      putStrLn $ "------------------"
      putStrLn $ _metaInfo'reason
      putStrLn $ ""
      printConstraint parent
-}

printOverview :: TCState m -> IO ()
printOverview s = do
  let nUnsolved = length $ filter (not . isSolved) $ toList $ _tcState'metaMap s
  putStrLn $ (show $ _tcState'metaCounter s) ++ " metavariables (meta i), of which "
    ++ show nUnsolved ++ " unsolved (metas),"
  putStrLn $ (show $ _tcState'constraintCounter s) ++ " constraints (constraint i),"
  putStrLn $ (show $ length $ _tcState'reports s) ++ " reports (reports)."

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
giveHelp = do
  putStrLn $ "quit          Quit Menkar."
  putStrLn $ "overview      Give an overview of the type-checking results."
  putStrLn $ "metas         Give an overview of the unsolved meta-variables."
  putStrLn $ "meta i        Give information about meta-variable ?i (where i is an integer)."
  putStrLn $ "constraint i  Give information about constraint i (where i is an integer)."
  putStrLn $ "reports       List other reports produced during type-checking (including goals)."
  putStrLn $ "help          Print this help."
  --putStrLn "Type 'quit' to quit. Other than that, I ain't got much to tell ya, to be fair."

runCommand :: TCState m -> [String] -> IO ()
runCommand s [] = return ()
runCommand s ("help" : _) = giveHelp
runCommand s ("overview" : _) = printOverview s
runCommand s (command : args) = do
  putStrLn $ "Unknown command : " ++ command
  putStrLn $ "Type 'help' for help."

consumeCommand :: TCState m -> IO Bool
consumeCommand s = do
  command <- prompt "> "
  let splitCommand = words command
  case splitCommand of
    "quit" : _ -> return False
    _ -> do
      runCommand s splitCommand
      return True

interactiveMode :: TCState m -> IO ()
interactiveMode s = do
  putStrLn "-------------------------"
  putStrLn "START OF INTERACTIVE MODE"
  putStrLn "-------------------------"
  printOverview s
  putStrLn ""
  putStrLn "Type 'quit' to quit, 'help' for help."
  doUntilFail (consumeCommand s)
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
              TCErrorBlocked parent reason -> unreachable
              TCErrorTCFail report s -> do
                putStrLn "------------"
                putStrLn "TYPING ERROR"
                putStrLn "------------"
                printReport report
                let s' = over (tcState'reports) (report :) s
                interactiveMode s'
              TCErrorScopeFail msg -> do
                putStrLn "-------------"
                putStrLn "SCOPING ERROR"
                putStrLn "-------------"
                putStrLn msg
    xs -> do
      putStrLn "This program should be given a file path as its sole argument."

main :: IO ()
main = mainArgs =<< (System.Environment.getArgs :: IO [String])
