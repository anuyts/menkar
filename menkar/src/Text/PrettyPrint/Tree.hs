{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts, StandaloneDeriving, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, ApplicativeDo #-}

module Text.PrettyPrint.Tree where

import Data.Tree
import Data.Functor.Identity
import Data.Foldable
import Control.Monad.Reader
import Control.Monad.Writer

--type TreeText = Tree String

data PrettyTree l =
  {-| first line, sublines, then perhaps a continuation of the block -}
  PrettyTree l [PrettyTree l] (Maybe (PrettyTree l))
  deriving (Functor, Foldable, Traversable)

deriving instance Show l => Show (PrettyTree l)

lengthHoriz :: Traversable l => PrettyTree (l c) -> Int
lengthHoriz = sum . fmap length

data RenderState = RenderState {widthLeft :: Int, currentIndent :: String, indentStep :: String}

--printLn :: RenderState -> String -> String -> String

class (MonadReader RenderState m, MonadWriter String m) => MonadRenderer m where
  
askWidthLeft :: MonadRenderer m => m Int
askWidthLeft = widthLeft <$> ask
askCurrentIndent :: MonadRenderer m => m String
askCurrentIndent = currentIndent <$> ask
askIndentStep :: MonadRenderer m => m String
askIndentStep = indentStep <$> ask

indentedLine :: MonadRenderer m => String -> m String
indentedLine s = (++ (s ++ "\n")) <$> askCurrentIndent

indent :: MonadRenderer m => m a -> m a
indent = local $ \ state -> state {
  widthLeft = widthLeft state - length (indentStep state),
  currentIndent = currentIndent state ++ indentStep state
  }

newtype RendererT m a = RendererT {runRendererT :: ReaderT RenderState (WriterT String m) a} deriving (Functor, Applicative)
deriving instance (Monad m) => Monad (RendererT m)
deriving instance (Monad m) => MonadReader RenderState (RendererT m)
deriving instance (Monad m) => MonadWriter [Char] (RendererT m)
instance (Monad m) => MonadRenderer (RendererT m) where

type Renderer = RendererT Identity
unwrapRenderer :: Renderer a -> RenderState -> (a, String)
unwrapRenderer (RendererT rwa) s = runWriter $ runReaderT rwa s

printLn :: MonadRenderer m => String -> m ()
printLn s = indentedLine s >>= tell

renderM :: MonadRenderer m => PrettyTree String -> m ()
renderM tree@(PrettyTree line sublines rest) = do
  widthLeft <- askWidthLeft
  if lengthHoriz tree <= widthLeft
    then printLn $ fold tree
    else case rest of
           Just tree' -> do
             renderM (PrettyTree line sublines Nothing)
             renderM tree'
           Nothing -> do
             printLn line
             indent $ sequenceA_ $ renderM <$> sublines

render :: RenderState -> PrettyTree String -> String
render state tree = snd $ unwrapRenderer (renderM tree) state

-------------------------------------------------------

(\\\) :: PrettyTree a -> [PrettyTree a] -> PrettyTree a
PrettyTree line sublines Nothing \\\ lines = PrettyTree line (sublines ++ lines) Nothing
PrettyTree line sublines (Just rest) \\\ lines = PrettyTree line sublines (Just $ rest \\\ lines)

(|||) :: PrettyTree a -> PrettyTree a -> PrettyTree a
PrettyTree line sublines Nothing ||| tree = PrettyTree line sublines (Just tree)
PrettyTree line sublines (Just rest) ||| tree = PrettyTree line sublines (Just $ rest ||| tree)

(///) :: PrettyTree a -> PrettyTree a -> PrettyTree a
(///) = (|||)

infixl 6 \\\
infixl 6 |||
infixl 6 ///

ribbon :: a -> PrettyTree a
ribbon a = PrettyTree a [] Nothing
