module Menkar.Main where

import qualified Menkar.Parser as P
import qualified Menkar.Scoper as S
import Menkar.Monads.DTT
import qualified Menkar.Raw as Raw
import Menkar.Fine
import Menkar.Systems.Trivial.Trivial
import Menkar.Systems.Trivial.MagicContext
import Menkar.TC
import Menkar.Monad.Monad

import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context

import Control.Exception.AssertFalse
import Control.Monad.DoUntilFail
import Data.Omissible
import Text.PrettyPrint.Tree

import Text.Megaparsec.Error as MP

import qualified System.Environment
import Control.Monad
import System.IO
import Data.IntMap.Strict hiding (filter, toList)
import Data.Maybe hiding (mapMaybe)
import Data.Proxy
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Foldable
import Data.IORef
import GHC.Generics (U1 (..))
import Control.Monad.Except
import Control.Lens
import System.Exit
import qualified System.Console.Terminal.Size as System

quickRead :: forall a . Read a => String -> Maybe a
quickRead str = case (readsPrec 0 str :: [(a, String)]) of
  [(a, "")] -> Just a
  _ -> Nothing

--------------------------

data MainState = MainState {
  _main'fine2prettyOptions :: Fine2PrettyOptions Trivial}

makeLenses ''MainState

instance Omissible MainState where
  omit = MainState {
    _main'fine2prettyOptions = omit}

class WithMainState where
  mainState :: IORef MainState

--------------------------

printConstraint :: IORef MainState -> Constraint Trivial -> IO ()
printConstraint ref c = do
  mainState <- readIORef ref
  putStrLn $ "Constraint " ++ show (constraint'id c) ++ ":"
  putStr $ jud2string (constraint'judgement c) $ _main'fine2prettyOptions mainState

printTrace :: IORef MainState -> Constraint Trivial -> IO ()
printTrace ref c = do
  printConstraint ref c
  putStrLn ""
  putStrLn $ constraint'reason c
  case constraint'parent c of
    Nothing -> return ()
    Just parent -> do
      putStrLn ""
      printTrace ref parent

printBlockInfo :: (DeBruijnLevel v, AllowsMetas Trivial descr t, Fine2Pretty Trivial t) =>
  IORef MainState -> TCState Trivial m -> ([Int], BlockInfo Trivial m t v) -> IO ()
printBlockInfo ref s (blockingMetas, blockInfo) = do
  putStrLn $ ""
  putStrLn $ "Reason for blocking: " ++ _blockInfo'reasonBlock blockInfo
  putStrLn $ "Reason for requesting: " ++ _blockInfo'reasonAwait blockInfo -- not super-useful.
  putStrLn $ "Blocked on:" ++ (fold $ (" ?" ++) . show <$> blockingMetas)
  printConstraint ref $ _blockInfo'parent blockInfo

printMetaInfo :: (DeBruijnLevel v, AllowsMetas Trivial descr t, Fine2Pretty Trivial t) =>
  IORef MainState -> TCState Trivial m -> Int -> MetaInfo Trivial m t v -> IO ()
printMetaInfo ref s meta info = do
  mainState <- readIORef ref
  putStrLn $ "Context:"
  putStrLn $ "--------"
  let tMeta = Expr2 $ TermMeta MetaBlocked meta (Compose $ Var2 <$> listAll Proxy) (Compose Nothing)
  putStr $ jud2string (JudTerm (_metaInfo'context info) tMeta (Type $ Expr2 $ TermWildcard))
           $ _main'fine2prettyOptions mainState
  putStrLn $ ""
  case _metaInfo'maybeSolution info of
    Right solutionInfo -> do
      putStrLn "Solution:"
      putStrLn "---------"
      mainState <- readIORef ref
      putStr   $ fine2string (ctx2scCtx $ _metaInfo'context info) tMeta
                 $ mainState ^. main'fine2prettyOptions & fine2pretty'printSolutions .~ Nothing
      putStr   $ " = "
      putStrLn $ fine2string (ctx2scCtx $ _metaInfo'context info) (_solutionInfo'solution solutionInfo)
                 $ mainState ^. main'fine2prettyOptions
      printConstraint ref $ _solutionInfo'parent solutionInfo
    Left blocks -> do
      putStrLn "Unsolved"
      putStrLn "--------"
      putStrLn $ "Blocking " ++ (show $ length blocks) ++ " constraints."
      sequenceA_ $ blocks <&> printBlockInfo ref s
  putStrLn $ ""
  putStrLn $ "Creation"
  putStrLn $ "--------"
  putStrLn $ "Reason: " ++ _metaInfo'reason info
  case _metaInfo'maybeParent info of
    Nothing -> putStrLn "(Created at scope-checking time.)"
    Just parent -> printConstraint ref parent

printConstraintByIndex :: IORef MainState -> TCState Trivial m -> Int -> IO ()
printConstraintByIndex ref s i =
  if (i < 0 || i >= _tcState'constraintCounter s)
  then putStrLn $ "Constraint index out of bounds."
  else printTrace ref $ fromMaybe unreachable $ view (tcState'constraintMap . at i) s

printMeta :: IORef MainState -> TCState Trivial m -> Int -> IO ()
printMeta ref s meta =
  if (meta < 0 || meta >= _tcState'metaCounter s)
  then putStrLn $ "Meta index out of bounds."
  else do
    let metaInfo = fromMaybe unreachable $ view (tcState'metaMap . at meta) s
    forThisDeBruijnLevel (forThisClassWithMetas (printMetaInfo ref s meta)) metaInfo

summarizeUnsolvedMeta :: forall m descr t v .
  (AllowsMetas Trivial descr t) =>
  IORef MainState -> TCState Trivial m -> Int -> MetaInfo Trivial m t v -> IO ()
summarizeUnsolvedMeta ref s meta metaInfo = case _metaInfo'maybeSolution metaInfo of
  Right solutionInfo -> return ()
  Left blocks -> putStrLn $
    "?" ++ show meta ++ "    (" ++ show (length blocks) ++ " constraints)    Creation: " ++ _metaInfo'reason metaInfo

printUnsolvedMetas :: IORef MainState -> TCState Trivial m -> IO ()
printUnsolvedMetas ref s = sequenceA_ $ flip mapWithKey (_tcState'metaMap s) $ \ meta metaInfo ->
  forThisDeBruijnLevel (forThisClassWithMetas (summarizeUnsolvedMeta ref s meta)) metaInfo
  
  --summarizeUnsolvedMeta ref s meta (forThisDeBruijnLevel . forThisClassWithMetas) metaInfo

printReport :: IORef MainState -> TCState Trivial m -> TCReport Trivial -> IO ()
printReport ref s report = do
  putStrLn $ "Report"
  putStrLn $ "------"
  putStrLn $ "Reason: " ++ _tcReport'reason report
  printConstraint ref $ _tcReport'parent report
  putStrLn $ ""

printOverview :: IORef MainState -> TCState Trivial m -> IO ()
printOverview ref s = do
  let nUnsolved = length $ filter (not . forThisDeBruijnLevel (forThisClassWithMetas isSolved)) $ toList $ _tcState'metaMap s
  putStrLn $ (show $ _tcState'metaCounter s) ++ " metavariables (meta i), of which "
    ++ show nUnsolved ++ " unsolved (metas),"
  putStrLn $ (show $ _tcState'constraintCounter s) ++ " constraints (constraint i),"
  putStrLn $ (show $ length $ _tcState'reports s) ++ " reports (reports)."

------------------------------------

{-| prints 'prefix' as a sign that the user should provide input; then returns the input. -}
prompt :: String -> IO String
prompt prefix = do
  putStr prefix
  hFlush stdout
  getLine

giveHelp :: IORef MainState -> IO ()
giveHelp ref = do
  putStrLn $ "q       quit          Quit Menkar."
  putStrLn $ "o       overview      Give an overview of the type-checking results."
  putStrLn $ "m       metas         Give an overview of the unsolved meta-variables."
  putStrLn $ "m i     meta i        Give information about meta-variable ?i (where i is an integer)."
  putStrLn $ "c i     constraint i  Give information about constraint i (where i is an integer)."
  putStrLn $ "c 0     constraint 0  Print the internal representation of the entire program."
  putStrLn $ "r       reports       List other reports produced during type-checking (including goals)."
  putStrLn $ "h       help          Print this help."
  putStrLn $ "s help  set help      Get help on the set command."
  --putStrLn "Type 'quit' to quit. Other than that, I ain't got much to tell ya, to be fair."

runCommandMeta :: IORef MainState -> TCState Trivial m -> [String] -> IO ()
runCommandMeta ref s args = case args of
  [arg] -> case quickRead arg :: Maybe Int of
    Just meta -> printMeta ref s meta
    Nothing -> putStrLn $ "Argument to 'meta' should be an integer."
  _ -> putStrLn $ "Command 'meta' expects one integer argument, e.g. 'meta 5'."
runCommandConstraint :: IORef MainState -> TCState Trivial m -> [String] -> IO ()
runCommandConstraint ref s args = case args of
  [arg] -> case quickRead arg :: Maybe Int of
    Just i -> printConstraintByIndex ref s i
    Nothing -> putStrLn $ "Argument to 'constraint' should be an integer."
  _ -> putStrLn $ "Command 'constraint' expects one integer argument, e.g. 'constraint 5'."
runCommandReports :: IORef MainState -> TCState Trivial m -> IO ()
runCommandReports ref s = sequenceA_ $ _tcState'reports s <&> printReport ref s

------------------------

forceLength :: Int -> [a] -> ([a] -> IO ()) -> IO ()
forceLength l as k
  | length as == l = k as
  | otherwise = putStrLn $ "Incorrect number of arguments."

readBool :: String -> (Bool -> IO ()) -> IO ()
readBool str k
  | str `elem` ["T", "t", "tt", "true",  "True",  "TRUE",  "y", "Y", "yes", "Yes"] = k True
  | str `elem` ["F", "f", "ff", "false", "False", "FALSE", "n", "N", "no",  "No" ] = k False
  | otherwise = putStrLn $ "Not a boolean: " ++ str

readInt :: String -> (Int -> IO ()) -> IO ()
readInt str k = case quickRead str of
  Just int -> k int
  Nothing -> putStrLn $ "Not an integer: " ++ str

giveHelpSet :: IORef MainState -> TCState Trivial m -> IO ()
giveHelpSet ref s = do
  putStrLn $ "set help                          Get this help."
  putStrLn $ "set explicit-division <BOOL>      Print left division explicitly."
  putStrLn $ "set factory                       Restore to factory settings."
  putStrLn $ "set print-algorithms <INT>        Print algorithm annotations (smart elimination/goal/resolution)."
  putStrLn $ "                                    0: omit entirely; 1: replace with '_'; 2: print fully."
  putStrLn $ "set print-entries <INT>           How to print entries (declarations)."
  putStrLn $ "                                    0: just their name; 1: also annotations; 2: entirely."
  putStrLn $ "set print-meta-algorithms <BOOL>  Instead of printing a meta's dependencies, print its algorithm."
  putStrLn $ "set print-modules <INT>           How to print modules. 0: omit contents; n+1: print entries as <n>."
  putStrLn $ "set print-modules-ctx <INT>       How to print modules in context. 0: not at all; n+1: modules as <n>."
  putStrLn $ "set print-solutions <BOOL>        Print solutions instead of metas."
  putStrLn $ "set print-types <BOOL>            Print pedantic type annotations."
  putStrLn $ "set width <INT>                   Set line width."

printMetaSolutionsOn :: IORef MainState -> TCState Trivial m -> IO ()
printMetaSolutionsOn ref s = do
  let setSolutionMap maybeMap = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printSolutions .~ maybeMap
  setSolutionMap $ Just $ _tcState'metaMap s & (mapMaybe $
        \ (ForSomeDeBruijnLevel (ForSomeClassWithMetas metaInfo)) -> case _metaInfo'maybeSolution metaInfo of
          Left blocks -> Nothing
          Right solutionInfo -> Just $ ForSomeDeBruijnLevel $ _solutionInfo'solution solutionInfo
      )

runCommandSet :: IORef MainState -> TCState Trivial m -> [String] -> IO ()
runCommandSet ref s [] = giveHelpSet ref s
runCommandSet ref s ("help" : _) = giveHelpSet ref s
runCommandSet ref s ("explicit-division" : args) = forceLength 1 args $ \[str] -> readBool str $ \bool ->
    modifyIORef ref $ main'fine2prettyOptions . fine2pretty'explicitLeftDivision .~ bool
runCommandSet ref s ("factory" : _) = prepMainState >>= writeIORef ref
runCommandSet ref s ("print-algorithms" : args) = forceLength 1 args $ \[str] -> readInt str $ \int -> do
  let setVerbosity v = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printAlgorithm .~ v
  case int of
    0 -> setVerbosity DontPrintAlgorithm
    1 -> setVerbosity PrintAlgorithmUnderscore
    2 -> setVerbosity PrintAlgorithm
    _ -> putStrLn $ "Integer argument should be in [0..2]."
runCommandSet ref s ("print-entries" : args) = forceLength 1 args $ \[str] -> readInt str $ \int -> do
  let setVerbosity v = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printEntry .~ v
  case int of
    0 -> setVerbosity PrintEntryName
    1 -> setVerbosity PrintEntryNameAnnots
    2 -> setVerbosity PrintEntryEntirely
    _ -> putStrLn $ "Integer argument should be in [0..2]."
runCommandSet ref s ("print-meta-algoriths" : args) = forceLength 1 args $ \[str] -> readBool str $ \bool ->
    modifyIORef ref $ main'fine2prettyOptions . fine2pretty'humanReadableMetas .~ bool
runCommandSet ref s ("print-modules" : args) = forceLength 1 args $ \[str] -> readInt str $ \int -> do
  let setVerbosity v = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printModule .~ PrintModuleVerbosity v
  case int of
    0 -> setVerbosity $ Nothing
    1 -> setVerbosity $ Just PrintEntryName
    2 -> setVerbosity $ Just PrintEntryNameAnnots
    3 -> setVerbosity $ Just PrintEntryEntirely
    _ -> putStrLn $ "Integer argument should be in [0..3]."
runCommandSet ref s ("print-modules-ctx" : args) = forceLength 1 args $ \[str] -> readInt str $ \int -> do
  let setVerbosity v = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printModuleInContext .~ v
  case int of
    0 -> setVerbosity $ Nothing
    1 -> setVerbosity $ Just $ PrintModuleVerbosity $ Nothing
    2 -> setVerbosity $ Just $ PrintModuleVerbosity $ Just PrintEntryName
    3 -> setVerbosity $ Just $ PrintModuleVerbosity $ Just PrintEntryNameAnnots
    4 -> setVerbosity $ Just $ PrintModuleVerbosity $ Just PrintEntryEntirely
    _ -> putStrLn $ "Integer argument should be in [0..4]."
runCommandSet ref s ("print-solutions" : args) = forceLength 1 args $ \[str] -> readBool str $ \bool -> do
  let setSolutionMap maybeMap = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printSolutions .~ maybeMap
  if bool
    then printMetaSolutionsOn ref s
    else setSolutionMap $ Nothing
runCommandSet ref s ("print-types" : args) = forceLength 1 args $ \[str] -> readBool str $ \bool ->
    modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printTypeAnnotations .~ bool
runCommandSet ref s ("width" : args) = forceLength 1 args $ \[str] -> readInt str $ \w ->
    modifyIORef ref $ main'fine2prettyOptions . fine2pretty'renderOptions . render'widthLeft .~ w
runCommandSet ref s _ = giveHelpSet ref s

------------------------

runCommand :: IORef MainState -> TCState Trivial m -> [String] -> IO ()
runCommand ref s [] = return ()
runCommand ref s ("constraint" : args) = runCommandConstraint ref s args
runCommand ref s ("c" : args) = runCommandConstraint ref s args
runCommand ref s ("help" : _) = giveHelp ref
runCommand ref s ("h" : _) = giveHelp ref
runCommand ref s ("metas" : _) = printUnsolvedMetas ref s
runCommand ref s ("m" : []) = printUnsolvedMetas ref s
runCommand ref s ("meta" : args) = runCommandMeta ref s args
runCommand ref s ("m" : args) = runCommandMeta ref s args
runCommand ref s ("overview" : _) = printOverview ref s
runCommand ref s ("o" : _) = printOverview ref s
runCommand ref s ("reports" : _) = runCommandReports ref s
runCommand ref s ("r" : _) = runCommandReports ref s
runCommand ref s ("set" : args) = runCommandSet ref s args
runCommand ref s ("s" : args) = runCommandSet ref s args
runCommand ref s ("git" : _) = putStrLn $ "I do not take git commands, for my name is Menkar."
runCommand ref s (command : args) = do
  putStrLn $ "Unknown command : " ++ command
  putStrLn $ "Type 'help' for help."

consumeCommand :: IORef MainState -> TCState Trivial m -> IO Bool
consumeCommand ref s = do
  command <- prompt "> "
  let splitCommand = words command
  case splitCommand of
    "quit" : _ -> return False
    "q" : _ -> return False
    _ -> do
      runCommand ref s splitCommand
      return True

interactiveMode :: IORef MainState -> TCState Trivial m -> IO ()
interactiveMode ref s = do
  printMetaSolutionsOn ref s
  putStrLn "-------------------------"
  putStrLn "START OF INTERACTIVE MODE"
  putStrLn "-------------------------"
  printOverview ref s
  putStrLn ""
  putStrLn "Type 'quit' to quit, 'help' for help."
  doUntilFail (consumeCommand ref s)
  return ()

interactAfterTask :: TC Trivial () -> IO ()
interactAfterTask task = do
          ref <- initMainState
          let (tcResult, s) = flip getTC initTCState $ task
          case tcResult of
            Right () -> interactiveMode ref s
            Left e -> case e of
              TCErrorConstraintBound -> unreachable
              TCErrorBlocked parent reason blocks -> unreachable
              TCErrorTCFail report -> do
                putStrLn "------------"
                putStrLn "TYPING ERROR"
                putStrLn "------------"
                printReport ref s report
                let s' = over (tcState'reports) (report :) s
                interactiveMode ref s'
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
                  Just parent -> printConstraint ref parent
                interactiveMode ref s

----------------------------

checkMagic :: IO ()
checkMagic = interactAfterTask $ do
  addNewConstraint
    magicModuleCorrect
    Nothing
    "Checking the magic module."
  typeCheck

getWidth :: IO (Maybe Int)
getWidth = fmap ((\x -> x - 4) . System.width) <$> System.size

prepMainState :: IO MainState
prepMainState = do
  maybeWidth <- getWidth
  return $ omit & fromMaybe id
    (maybeWidth <&> \width -> main'fine2prettyOptions . fine2pretty'renderOptions . render'widthLeft .~ width)

initMainState :: IO (IORef MainState)
initMainState = prepMainState >>= newIORef

----------------------------
  
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
