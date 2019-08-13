{-# LANGUAGE AllowAmbiguousTypes #-}

module Menkar.Main where

import Menkar.ID
import qualified Menkar.Parser as P
import qualified Menkar.Scoper as S
import Menkar.Monads.DTT
import qualified Menkar.Raw as Raw
import Menkar.Fine
import Menkar.Systems
import Menkar.TC
import Menkar.Monad.Monad
import Menkar.Analyzer
import Menkar.System.MagicContext
import Menkar.MagicContext.MagicContext
import Menkar.System.System

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
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Foldable
import Data.IORef
import GHC.Generics
import Control.Monad.Except
import Control.Lens
import System.Exit
import qualified System.Console.Terminal.Size as System
import Text.Read

import Prelude hiding (lookup)

quickRead :: forall a . Read a => String -> Maybe a
quickRead str = case (readsPrec 0 str :: [(a, String)]) of
  [(a, "")] -> Just a
  _ -> Nothing

--------------------------

data MainState sys = MainState {
  _main'fine2prettyOptions :: Fine2PrettyOptions sys,
  _main'loop :: Int}

makeLenses ''MainState

instance Omissible (MainState sys) where
  omit = MainState {
    _main'fine2prettyOptions = omit,
    _main'loop = 100000}

newtype GeneralMainState = GeneralMainState {specializeMainState :: forall sys . (Sys sys) => MainState sys}
instance Omissible GeneralMainState where
  omit = GeneralMainState omit
mapGeneralMainState :: (forall sys . (Sys sys) => MainState sys -> MainState sys) -> GeneralMainState -> GeneralMainState
mapGeneralMainState f (GeneralMainState s) = GeneralMainState $ f s

--------------------------

printConstraint :: (Sys sys) => IORef (MainState sys) -> Constraint sys -> IO ()
printConstraint ref c = do
  mainState <- readIORef ref
  putStrLn $ "Constraint " ++ show (_constraint'id c)
  putStrLn $ jud2string (_constraint'judgement c) $ _main'fine2prettyOptions mainState

printConstraintWithReason :: (Sys sys) => IORef (MainState sys) -> Constraint sys -> IO ()
printConstraintWithReason ref c = do
  putStrLn $ _constraint'reason c
  putStrLn ""
  printConstraint ref c

printTrace :: (Sys sys) => IORef (MainState sys) -> Constraint sys -> IO ()
printTrace ref c = do
  case _constraint'parent c of
    Nothing -> return ()
    Just parent -> do
      printTrace ref parent
  printConstraintWithReason ref c

{-
printBlockInfo :: (Sys sys, DeBruijnLevel v) =>
  IORef (MainState sys) ->
  TCState sys m ->
  ([Int], BlockInfo sys m v, Constraint sys) ->
  IO ()
printBlockInfo ref s (blockingMetas, blockInfo, constraintJudBlock) = do
  putStrLn $ ""
  printConstraint ref $ constraintJudBlock
  {-putStrLn $ "Reason for blocking: " ++ _blockInfo'reasonBlock blockInfo
  putStrLn $ "Reason for requesting: " ++ _blockInfo'reasonAwait blockInfo -- not super-useful.
  putStrLn $ "Blocked on:" ++ (fold $ (" ?" ++) . show <$> blockingMetas)
  putStrLn $ "See constraint: " ++ show (_constraint'id constraintJudBlock)-}
  printConstraint ref $ _blockInfo'parent blockInfo
-}

printMetaInfo :: (Sys sys, DeBruijnLevel v) => IORef (MainState sys) -> TCState sys m -> Int -> MetaInfo sys m v -> IO ()
printMetaInfo ref s meta info = do
  mainState <- readIORef ref
  putStrLn $ "Context:"
  putStrLn $ "--------"
  let tMeta = Expr2 $ TermMeta
        MetaBlocked
        meta
        (Dependencies $ coy $ Compose $ forallVars $ (unreachable :*:) . Var2)
        (Compose Nothing)
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
    Left worryIDs -> do
      putStrLn $ "Unsolved"
      putStrLn $ "--------"
      putStrLn $ "Blocking worries: " ++ (join $ (++ ", ") . show <$> worryIDs)
  putStrLn $ ""
  putStrLn $ "Creation"
  putStrLn $ "--------"
  putStrLn $ "Reason: " ++ _metaInfo'reason info
  case _metaInfo'maybeParentID info of
    Nothing -> putStrLn "(Created at scope-checking time.)"
    Just parentID -> case lookup parentID $ _tcState'constraintMap s of
      Nothing -> putStrLn "(Parent judgement not retained.)"
      Just parent -> printConstraint ref parent
printBlockingMeta :: (Sys sys, DeBruijnLevel v) => IORef (MainState sys) -> TCState sys m -> BlockingMeta sys m v -> IO ()
printBlockingMeta ref s (BlockingMeta meta cont reasonAwait) =
  putStrLn $ "?" ++ show meta ++ " : " ++ reasonAwait
printWorry :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> WorryID -> Worry sys m -> IO ()
printWorry ref s iD worry = do
  mainState <- readIORef ref
  case _worry'unblockedBy worry of
    Nothing -> putStrLn $ "Still blocked."
    Just meta -> putStrLn $ "Unblocked by ?" ++ show meta
  putStrLn $ ""
  putStrLn $ "Blocking metas"
  putStrLn $ "--------------"
  sequenceA_ $ _worry'metas worry <&>
    \ (ForSomeDeBruijnLevel blockingMeta) -> printBlockingMeta ref s blockingMeta
  putStrLn $ ""
  putStrLn $ "Constraints"
  putStrLn $ "-----------"
  printConstraint ref $ fromMaybe unreachable $ _constraint'parent $ _worry'constraint worry
  printConstraintWithReason ref $ _worry'constraint worry
  case _worry'constraintUnblock worry of
    Nothing -> return ()
    Just constraintUnblock -> do
      printConstraintWithReason ref constraintUnblock

printConstraintByIndex :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> Int -> IO ()
printConstraintByIndex ref s i =
  case view (tcState'constraintMap . at i) s of
    Nothing -> putStrLn $
      "Sorry, I only retained constraints 0 and "
      ++ show (_tcState'constraintDeletionCounter s)
      ++ ".."
      ++ show (_tcState'constraintCounter s - 1)
    Just c -> printTrace ref c
printMeta :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> Int -> IO ()
printMeta ref s meta =
  if (meta < 0 || meta >= _tcState'metaCounter s)
  then putStrLn $ "Meta index out of bounds."
  else do
    let metaInfo = view (tcState'metaMap . at meta . _JustUnsafe) s
    forThisDeBruijnLevel (printMetaInfo ref s meta) metaInfo
printWorryByID :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> WorryID -> IO ()
printWorryByID ref s iD@(WorryID i) =
  case view (tcState'worryMap . at i) s of
    Nothing -> putStrLn $
      "Sorry, I only retained worries "
      ++ show (_tcState'worryDeletionCounter s)
      ++ ".."
      ++ show (_tcState'worryCounter s - 1)
    Just worry -> printWorry ref s iD worry

summarizeMetaIfUnsolved :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> Int -> MetaInfo sys m v -> IO ()
summarizeMetaIfUnsolved ref s meta metaInfo = case _metaInfo'maybeSolution metaInfo of
  Right solutionInfo -> return ()
  Left blocks -> putStrLn $
    "?" ++ show meta ++ "    (" ++ show (length blocks) ++ " worries)    Creation: " ++ _metaInfo'reason metaInfo
summarizeWorryIfBothering ::
  (Sys sys) => IORef (MainState sys) -> TCState sys m -> WorryID -> Worry sys m -> IO ()
summarizeWorryIfBothering ref s iD worry = case _worry'unblockedBy worry of
  Just _ -> return ()
  Nothing -> putStrLn $
    show iD
      ++ "  (constraint: " ++ (show $ _constraint'id $ _worry'constraint worry) ++ ")   "
      ++ "Reason: " ++ _worry'reason worry

printUnsolvedMetas :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
printUnsolvedMetas ref s = sequenceA_ $ flip mapWithKey (_tcState'metaMap s) $ \ meta metaInfo ->
  summarizeMetaIfUnsolved ref s meta `forThisDeBruijnLevel` metaInfo
printBotheringWorries :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
printBotheringWorries ref s = sequenceA_ $ flip mapWithKey (_tcState'worryMap s) $ \ iD worry ->
  summarizeWorryIfBothering ref s (WorryID iD) worry

printReport :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> TCReport sys -> IO ()
printReport ref s report = do
  putStrLn $ "Report"
  putStrLn $ "------"
  putStrLn $ "Reason: " ++ _tcReport'reason report
  printConstraint ref $ _tcReport'parent report
  putStrLn $ ""

printOverview :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
printOverview ref s = do
  let nUnsolved = _tcState'nUnsolvedMetas s
  putStrLn $ (show $ _tcState'metaCounter s) ++ " metavariables (meta i), of which "
    ++ show nUnsolved ++ " unsolved (metas),"
  let nBothering = _tcState'nBlockedWorries s
  putStrLn $ (show $ _tcState'worryCounter s) ++ " worries (worry i), of which "
    ++ show nBothering ++ " still bothering me (worries),"
  putStrLn $ (show $ _tcState'constraintCounter s) ++ " constraints (constraint i),"
  putStrLn $ (show $ length $ _tcState'reports s) ++ " reports (reports)."

------------------------------------

{-| prints 'prefix' as a sign that the user should provide input; then returns the input. -}
prompt :: String -> IO String
prompt prefix = do
  putStr prefix
  hFlush stdout
  getLine

giveHelp :: (Sys sys) => IORef (MainState sys) -> IO ()
giveHelp ref = do
  putStrLn $ "c i     constraint i  Give information about constraint i (where i is an integer)."
  putStrLn $ "c 0     constraint 0  Print the internal representation of the entire program."
  putStrLn $ "h       help          Print this help."
  putStrLn $ "m       metas         Give an overview of the unsolved meta-variables."
  putStrLn $ "m i     meta i        Give information about meta-variable ?i (where i is an integer)."
  putStrLn $ "o       overview      Give an overview of the type-checking results."
  putStrLn $ "q       quit          Quit Menkar."
  putStrLn $ "r       reports       List other reports produced during type-checking (including goals)."
  putStrLn $ "s help  set help      Get help on the set command."
  putStrLn $ "w       worries       Give an overview of the worries still bothering me."
  putStrLn $ "w i     worry i       Give information about worry i (where i is an integer)."
  --putStrLn "Type 'quit' to quit. Other than that, I ain't got much to tell ya, to be fair."

runCommandMeta :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> [String] -> IO ()
runCommandMeta ref s args = case args of
  [arg] -> case quickRead arg :: Maybe Int of
    Just meta -> printMeta ref s meta
    Nothing -> putStrLn $ "Argument to 'meta' should be an integer."
  _ -> putStrLn $ "Command 'meta' expects one integer argument, e.g. 'meta 5'."
runCommandConstraint :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> [String] -> IO ()
runCommandConstraint ref s args = case args of
  [arg] -> case quickRead arg :: Maybe Int of
    Just i -> printConstraintByIndex ref s i
    Nothing -> putStrLn $ "Argument to 'constraint' should be an integer."
  _ -> putStrLn $ "Command 'constraint' expects one integer argument, e.g. 'constraint 5'."
runCommandReports :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
runCommandReports ref s = sequenceA_ $ _tcState'reports s <&> printReport ref s
runCommandWorry :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> [String] -> IO ()
runCommandWorry ref s args = case args of
  [arg] -> case quickRead arg :: Maybe Int of
    Just i -> printWorryByID ref s (WorryID i)
    Nothing -> putStrLn $ "Argument to 'worry' should be an integer."
  _ -> putStrLn $ "Command 'worry' expects one integer argument, e.g. 'worry 5'."

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

giveHelpSet :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
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

printMetaSolutionsOn :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
printMetaSolutionsOn ref s = do
  let setSolutionMap maybeMap = modifyIORef ref $ main'fine2prettyOptions . fine2pretty'printSolutions .~ maybeMap
  setSolutionMap $ Just $ _tcState'metaMap s & (mapMaybe $
        \ (ForSomeDeBruijnLevel metaInfo) -> case _metaInfo'maybeSolution metaInfo of
          Left blocks -> Nothing
          Right solutionInfo -> Just $ ForSomeDeBruijnLevel $ _solutionInfo'solution solutionInfo
      )

runCommandSet :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> [String] -> IO ()
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
runCommandSet ref s ("print-meta-algorithms" : args) = forceLength 1 args $ \[str] -> readBool str $ \bool ->
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

runCommand :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> [String] -> IO ()
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
runCommand ref s ("worries" : _) = printBotheringWorries ref s
runCommand ref s ("w" : []) = printBotheringWorries ref s
runCommand ref s ("worry" : args) = runCommandWorry ref s args
runCommand ref s ("w" : args) = runCommandWorry ref s args
runCommand ref s ("git" : _) = putStrLn $ "I do not take git commands, for my name is Menkar."
runCommand ref s (command : args) = do
  putStrLn $ "Unknown command : " ++ command
  putStrLn $ "Type 'help' for help."

consumeCommand :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO Bool
consumeCommand ref s = do
  command <- prompt "> "
  let splitCommand = words command
  case splitCommand of
    "quit" : _ -> return False
    "q" : _ -> return False
    _ -> do
      runCommand ref s splitCommand
      return True

interactiveMode :: (Sys sys) => IORef (MainState sys) -> TCState sys m -> IO ()
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

interactAfterTask :: (Sys sys) => MainState sys -> TC sys () -> IO ()
interactAfterTask s task = do
          ref <- newIORef s
          let opts = TCOptions {
                _tcOptions'loop = _main'loop s
                }
          let (tcResult, s) = getTC opts initTCState $ task
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

checkMagic :: forall sys . (Sys sys) => MainState sys -> IO ()
checkMagic s = interactAfterTask s $ do
  addNewConstraint
    (magicModuleCorrect @sys)
    "Checking the magic module."
  typeCheck

getWidth :: IO (Maybe Int)
getWidth = fmap ((\x -> x - 4) . System.width) <$> System.size

prepMainState :: (Sys sys) => IO (MainState sys)
prepMainState = do
  GeneralMainState s <- initGeneralMainState
  return s

initMainState :: (Sys sys) => IO (IORef (MainState sys))
initMainState = prepMainState >>= newIORef

----------------------------

printCommandLineHelp :: IO ()
printCommandLineHelp = do
  putStrLn ""
  putStrLn "SYNOPSIS"
  putStrLn "    menkar [options] <system> [<file>...]"
  putStrLn "    menkar [options] --check-magic <system>"
  putStrLn ""
  putStrLn "OPTIONS"
  putStrLn "    <system> :   trivial : one mode, one modality"
  putStrLn "                 redltt :  degrees of relatedness - https://doi.org/10.1145/3209108.3209119"
  putStrLn "    --loop n :   After n constraints, conclude that you're in a loop and issue a typing error."
  putStrLn ""

runMenkar :: forall sys . (Sys sys) => MainState sys -> [String] -> IO ()
runMenkar s args = do
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
  interactAfterTask s $ do
    fineModule <- S.bulk (magicContext @sys) rawEntries
    addNewConstraint
      (Jud AnTokenEntry magicContext fineModule U1 (ClassifWillBe U1))
      "Type-checking everything."
    typeCheck

mainStateArgs :: GeneralMainState -> [String] -> IO ()
mainStateArgs s [] = printCommandLineHelp
mainStateArgs s (arg1 : args) = case arg1 of
  "trivial" -> runMenkar @Trivial (specializeMainState s) args
  "reldtt" -> runMenkar @Reldtt (specializeMainState s) args
  "--loop" -> case args of
    [] -> printCommandLineHelp
    arg2 : args -> case readMaybe arg2 :: Maybe Int of
      Nothing -> printCommandLineHelp
      Just n -> mainStateArgs (s & mapGeneralMainState (main'loop .~ n)) args
  "--check-magic" -> case args of
    "trivial" : [] -> checkMagic @Trivial (specializeMainState s)
    "reldtt" : [] -> checkMagic @Reldtt (specializeMainState s)
    _ -> printCommandLineHelp
  otherwise -> printCommandLineHelp

initGeneralMainState :: IO GeneralMainState
initGeneralMainState = do
  maybeWidth <- getWidth
  return $ GeneralMainState $ omit & fromMaybe id
    (maybeWidth <&> \width -> main'fine2prettyOptions . fine2pretty'renderOptions . render'widthLeft .~ width)
  
mainArgs :: [String] -> IO ()
mainArgs args = do
  s <- initGeneralMainState
  mainStateArgs s args

main :: IO ()
main = mainArgs =<< (System.Environment.getArgs :: IO [String])
