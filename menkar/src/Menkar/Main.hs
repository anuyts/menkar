module Menkar.Main where

import qualified System.Environment
import Control.Monad
import System.IO
import qualified Menkar.Parser as P
import qualified Menkar.Scoper as S
import Menkar.TC.Monad.DTT
import qualified Menkar.Raw as Raw
import Menkar.Fine
import Menkar.Fine.Multimode.Trivial.MagicContext
import Menkar.TC

import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context

import Control.Exception.AssertFalse

import Text.Megaparsec.Error as MP

import Data.IntMap.Strict hiding (filter, toList)
import Data.Maybe
import Data.Proxy
import Data.Functor.Identity
import Data.Functor.Compose
import GHC.Generics (U1 (..))
import Control.Monad.Except
import Data.Foldable
import Control.Lens
import System.Exit

printConstraint :: Constraint U1 U1 U1 -> IO ()
printConstraint c = do
  putStrLn $ "Constraint " ++ show (constraint'id c) ++ ":"
  putStr $ show $ constraint'judgement c

printTrace :: Constraint U1 U1 U1 -> IO ()
printTrace c = do
  printConstraint c
  putStrLn ""
  putStrLn $ constraint'reason c
  case constraint'parent c of
    Nothing -> return ()
    Just parent -> do
      putStrLn ""
      printTrace parent

printBlockInfo :: DeBruijnLevel v => TCState m -> ([Int], BlockInfo m v) -> IO ()
printBlockInfo s (blockingMetas, blockInfo) = do
  putStrLn $ ""
  putStrLn $ "Reason for blocking: " ++ _blockInfo'reasonBlock blockInfo
  putStrLn $ "Reason for requesting: " ++ _blockInfo'reasonAwait blockInfo -- not super-useful.
  putStrLn $ "Blocked on:" ++ (fold $ (" ?" ++) . show <$> blockingMetas)
  printConstraint $ _blockInfo'parent blockInfo

printMetaInfo :: DeBruijnLevel v => TCState m -> Int -> MetaInfo m v -> IO ()
printMetaInfo s meta info = do
  putStrLn $ "Context:"
  putStrLn $ "--------"
  let tMeta = Expr3 $ TermMeta True meta $ Compose $ Var3 <$> listAll Proxy
  putStr $ show $ JudTerm (_metaInfo'context info) tMeta (Type $ Expr3 $ TermWildcard)
  putStrLn $ ""
  case _metaInfo'maybeSolution info of
    Right solutionInfo -> do
      putStrLn "Solution:"
      putStrLn "---------"
      putStr   $ fine2string (ctx2scCtx $ _metaInfo'context info) tMeta
      putStr   $ " = "
      putStrLn $ fine2string (ctx2scCtx $ _metaInfo'context info) $ _solutionInfo'solution solutionInfo
      printConstraint $ _solutionInfo'parent solutionInfo
    Left blocks -> do
      putStrLn "Unsolved"
      putStrLn "--------"
      putStrLn $ "Blocking " ++ (show $ length blocks) ++ " constraints."
      sequenceA_ $ blocks <&> printBlockInfo s
  putStrLn $ ""
  putStrLn $ "Creation"
  putStrLn $ "--------"
  putStrLn $ "Reason: " ++ _metaInfo'reason info
  case _metaInfo'maybeParent info of
    Nothing -> putStrLn "(Created at scope-checking time.)"
    Just parent -> printConstraint parent

printConstraintByIndex :: TCState m -> Int -> IO ()
printConstraintByIndex s i =
  if (i < 0 || i >= _tcState'constraintCounter s)
  then putStrLn $ "Constraint index out of bounds."
  else printTrace $ fromMaybe unreachable $ view (tcState'constraintMap . at i) s

printMeta :: TCState m -> Int -> IO ()
printMeta s meta =
  if (meta < 0 || meta >= _tcState'metaCounter s)
  then putStrLn $ "Meta index out of bounds."
  else do
    let metaInfo = fromMaybe unreachable $ view (tcState'metaMap . at meta) s
    forThisDeBruijnLevel (printMetaInfo s meta) metaInfo

summarizeUnsolvedMeta :: TCState m -> Int -> MetaInfo m v -> IO ()
summarizeUnsolvedMeta s meta metaInfo = case _metaInfo'maybeSolution metaInfo of
  Right solutionInfo -> return ()
  Left blocks -> putStrLn $
    "?" ++ show meta ++ "    (" ++ show (length blocks) ++ " constraints)    Creation: " ++ _metaInfo'reason metaInfo

printUnsolvedMetas :: TCState m -> IO ()
printUnsolvedMetas s = sequenceA_ $ flip mapWithKey (_tcState'metaMap s) $ \ meta metaInfo ->
  summarizeUnsolvedMeta s meta `forThisDeBruijnLevel` metaInfo

printReport :: TCState m -> TCReport -> IO ()
printReport s report = do
  putStrLn $ "Report"
  putStrLn $ "------"
  putStrLn $ "Reason: " ++ _tcReport'reason report
  printConstraint $ _tcReport'parent report
  putStrLn $ ""

printOverview :: TCState m -> IO ()
printOverview s = do
  let nUnsolved = length $ filter (not . forThisDeBruijnLevel isSolved) $ toList $ _tcState'metaMap s
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
  putStrLn $ "q       quit          Quit Menkar."
  putStrLn $ "o       overview      Give an overview of the type-checking results."
  putStrLn $ "m       metas         Give an overview of the unsolved meta-variables."
  putStrLn $ "m i     meta i        Give information about meta-variable ?i (where i is an integer)."
  putStrLn $ "c i     constraint i  Give information about constraint i (where i is an integer)."
  putStrLn $ "c 0     constraint 0  Print the internal representation of the entire program."
  putStrLn $ "r       reports       List other reports produced during type-checking (including goals)."
  putStrLn $ "h       help          Print this help."
  --putStrLn "Type 'quit' to quit. Other than that, I ain't got much to tell ya, to be fair."

runCommandMeta :: TCState m -> [String] -> IO ()
runCommandMeta s args = case args of
  [arg] -> case readsPrec 0 arg :: [(Int, String)] of
    [(meta, "")] -> printMeta s meta
    _ -> putStrLn $ "Argument to 'meta' should be an integer."
  _ -> putStrLn $ "Command 'meta' expects one integer argument, e.g. 'meta 5'."
runCommandConstraint :: TCState m -> [String] -> IO ()
runCommandConstraint s args = case args of
  [arg] -> case readsPrec 0 arg :: [(Int, String)] of
    [(i, "")] -> printConstraintByIndex s i
    _ -> putStrLn $ "Argument to 'constraint' should be an integer."
  _ -> putStrLn $ "Command 'constraint' expects one integer argument, e.g. 'constraint 5'."
runCommandReports :: TCState m -> IO ()
runCommandReports s = sequenceA_ $ _tcState'reports s <&> printReport s

runCommand :: TCState m -> [String] -> IO ()
runCommand s [] = return ()
runCommand s ("help" : _) = giveHelp
runCommand s ("h" : _) = giveHelp
runCommand s ("metas" : _) = printUnsolvedMetas s
runCommand s ("m" : []) = printUnsolvedMetas s
runCommand s ("meta" : args) = runCommandMeta s args
runCommand s ("m" : args) = runCommandMeta s args
runCommand s ("constraint" : args) = runCommandConstraint s args
runCommand s ("c" : args) = runCommandConstraint s args
runCommand s ("reports" : _) = runCommandReports s
runCommand s ("r" : _) = runCommandReports s
runCommand s ("overview" : _) = printOverview s
runCommand s ("o" : _) = printOverview s
runCommand s (command : args) = do
  putStrLn $ "Unknown command : " ++ command
  putStrLn $ "Type 'help' for help."

consumeCommand :: TCState m -> IO Bool
consumeCommand s = do
  command <- prompt "> "
  let splitCommand = words command
  case splitCommand of
    "quit" : _ -> return False
    "q" : _ -> return False
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

interactAfterTask :: TC () -> IO ()
interactAfterTask task = do
          let (tcResult, s) = flip getTC initTCState $ task
          case tcResult of
            Right () -> interactiveMode s
            Left e -> case e of
              TCErrorConstraintBound -> unreachable
              TCErrorBlocked parent reason blocks -> unreachable
              TCErrorTCFail report -> do
                putStrLn "------------"
                putStrLn "TYPING ERROR"
                putStrLn "------------"
                printReport s report
                let s' = over (tcState'reports) (report :) s
                interactiveMode s'
              TCErrorScopeFail msg -> do
                putStrLn "-------------"
                putStrLn "SCOPING ERROR"
                putStrLn "-------------"
                putStrLn msg
              TCErrorInternal maybeParent msg -> do
                putStrLn "------------------------------"
                putStrLn "INTERNAL ERROR (please report)"
                putStrLn "------------------------------"
                putStrLn msg
                case maybeParent of
                  Nothing -> return ()
                  Just parent -> printConstraint parent
                interactiveMode s
  

checkMagic :: IO ()
checkMagic = interactAfterTask $ do
  addNewConstraint
    magicModuleCorrect
    Nothing
    "Checking the magic module."
  typeCheck
  
mainArgs :: [String] -> IO ()
mainArgs args = do
  rawEntries <- fmap concat $ sequenceA $ args <&> \path -> do
    code <- readFile path
    let errorOrRawFile = P.parse P.bulk path code
    case errorOrRawFile of
      Left e -> do
          putStrLn "-------------"
          putStrLn "PARSING ERROR"
          putStrLn "-------------"
          putStrLn $ "path: " ++ path
          putStrLn $ MP.errorBundlePretty e
          exitSuccess
      Right rawEntries -> return rawEntries
  interactAfterTask $ do
    fineModule <- S.bulk magicContext rawEntries
    addNewConstraint
      (JudEntry magicContext fineModule)
      Nothing
      "Type-checking everything."
    typeCheck
{-
mainArgs args = do
  case args of
    [path] -> do
      code <- readFile path
      let errorOrRawFile = P.parse P.file path code
      case errorOrRawFile of
        Left e -> do
          putStrLn "-------------"
          putStrLn "PARSING ERROR"
          putStrLn "-------------"
          putStrLn $ MP.errorBundlePretty e
        Right rawFile -> interactAfterTask $ do
                fineFile <- S.file magicContext rawFile
                addNewConstraint
                  (JudEntry magicContext fineFile)
                  Nothing
                  "Type-checking the file."
                typeCheck
    xs -> do
      putStrLn "This program should be given a file path as its sole argument."
-}

main :: IO ()
main = mainArgs =<< (System.Environment.getArgs :: IO [String])
