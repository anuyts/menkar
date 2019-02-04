{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts, StandaloneDeriving, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, ApplicativeDo, NoDeriveAnyClass #-}

module Text.PrettyPrint.Tree where

import Data.Omissible

import Data.Functor.Identity
import Data.Foldable
import Data.Maybe
import Data.Char
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Exception.AssertFalse
import Control.Lens

data RenderState = RenderState {
  _render'widthLeft :: Int,
  _render'currentIndent :: String,
  _render'indentStep :: String}
type RenderOptions = RenderState
defaultRenderState = (RenderState 100 "  " "    ")

instance Omissible RenderState where
  omitted = defaultRenderState

makeLenses ''RenderState

--type TreeText = Tree String

{-| A @'PrettyTree' l@ is a consecution of zero or more groups, each optionally preceded by a ribbon.
    A ribbon is just an object of type 'l'. A group is a list of @'PrettyTree'@s.

    The idea is that they are rendered as follows (when @l = String@):

    * If there is only one group that is empty, then the first ribbon is rendered.

    * If all of the text in the first ribbon (if present), the first group, and the second ribbon (if present) fits a single
    line, then they are collapsed to a single ribbon and the result is rendered.

    * Otherwise, the first ribbon (if present) is printed. Then the trees of the first group are rendered, each starting
    on a fresh line, with increased indentation. Finally, the remainder of the tree is rendered.
-}
data PrettyTree l =
  {-| Optional first ribbon, trees in the first group, rest of the tree (if any). -}
  PrettyTree (Maybe l) [PrettyTree l] (Maybe (PrettyTree l))
  deriving (Functor, Foldable, Traversable)
deriving instance Show l => Show (PrettyTree l)

{-| Creates a @'PrettyTree'@ consisting of the given ribbon (if present) followed by an empty group. -}
ribbonMaybe :: Maybe a -> PrettyTree a
ribbonMaybe ma = PrettyTree ma [] Nothing
{-| Creates a @'PrettyTree'@ consisting of the given ribbon, followed by an empty group. -}
ribbon :: a -> PrettyTree a
ribbon = ribbonMaybe . Just
{-| Creates a @'PrettyTree'@ consisting solely of an empty group. -}
ribbonEmpty :: PrettyTree a
ribbonEmpty = ribbonMaybe Nothing

{-| Collapses the first ribbon (if present), the first group and the second ribbon (if present) into a single ribbon,
    preserving the remainder of the tree. -}
collapseOnce :: Monoid l => PrettyTree l -> PrettyTree l
collapseOnce (PrettyTree Nothing [] Nothing) = ribbonEmpty
collapseOnce (PrettyTree Nothing [] (Just rest)) = rest
collapseOnce tree@(PrettyTree line sublines Nothing) = ribbon $ fold tree
collapseOnce (PrettyTree line sublines (Just (PrettyTree line' sublines' rest')))
  = PrettyTree (Just $ fold $ PrettyTree line sublines (Just $ ribbonMaybe line')) sublines' rest'

{-| Number of characters in the tree. -}
lengthHoriz :: Traversable l => PrettyTree (l c) -> Int
lengthHoriz = sum . fmap length


--printLn :: RenderState -> String -> String -> String

class (MonadReader RenderState m, MonadWriter String m) => MonadRenderer m where
  
askWidthLeft :: MonadRenderer m => m Int
askWidthLeft = _render'widthLeft <$> ask
askCurrentIndent :: MonadRenderer m => m String
askCurrentIndent = _render'currentIndent <$> ask
askIndentStep :: MonadRenderer m => m String
askIndentStep = _render'indentStep <$> ask

indentedLine :: MonadRenderer m => String -> m String
indentedLine s = (++ (s ++ "\n")) <$> askCurrentIndent

indent :: MonadRenderer m => m a -> m a
indent = local $ \ state -> state {
  _render'widthLeft = _render'widthLeft state - length (_render'indentStep state),
  _render'currentIndent = _render'currentIndent state ++ _render'indentStep state
  }

newtype RendererT m a = RendererT {runRendererT :: ReaderT RenderState (WriterT String m) a} deriving (Functor, Applicative)
deriving instance (Monad m) => Monad (RendererT m)
deriving instance (Monad m) => MonadReader RenderState (RendererT m)
deriving instance (Monad m) => MonadWriter [Char] (RendererT m)
instance (Monad m) => MonadRenderer (RendererT m) where

type Renderer = RendererT Identity
unwrapRenderer :: Renderer a -> RenderState -> (a, String)
unwrapRenderer (RendererT rwa) s = runWriter $ runReaderT rwa s

removeLeadingWhitespace :: String -> String
removeLeadingWhitespace = dropWhile isSpace

printLn :: MonadRenderer m => String -> m ()
printLn s = indentedLine (removeLeadingWhitespace s) >>= tell

renderM :: MonadRenderer m => PrettyTree String -> m ()
renderM (PrettyTree Nothing [] Nothing) = return ()
renderM (PrettyTree Nothing [] (Just rest)) = renderM rest 
renderM (PrettyTree (Just line) [] Nothing) = printLn line
renderM tree@(PrettyTree line sublines rest) = do
  widthLeft <- askWidthLeft
  let collapsedTree@(PrettyTree lineMaybe' sublines' rest') = collapseOnce tree
  let line' = fromMaybe "" lineMaybe'
  if length line' <= widthLeft
    --then return ()
    then renderM collapsedTree
    else do
      sequenceA_ $ printLn <$> line
      indent $ sequenceA_ $ renderM <$> sublines
      case rest of
        Nothing -> return ()
        Just restTree -> renderM restTree
      --return ()

{-
renderM :: MonadRenderer m => PrettyTree String -> m ()
renderM tree@(PrettyTree line sublines rest) = do
  widthLeft <- askWidthLeft
  if lengthHoriz tree <= widthLeft
    then printLn $ fold tree
    else case rest of
           Just tree'@(PrettyTree line' sublines' rest') ->
             let flattenableTree = PrettyTree line sublines (ribbon line')
             in if lengthHoriz flattenableTree <= widthLeft
                  then do
                    printLn $ fold flattenableTree
                    _
                  else _
             --renderM (PrettyTree line sublines Nothing)
             --renderM tree'
           Nothing -> do
             printLn line
             indent $ sequenceA_ $ renderM <$> sublines
-}

render :: PrettyTree String -> RenderState -> String
render tree state = snd $ unwrapRenderer (renderM tree) state

-------------------------------------------------------

-- | Append a new indented group
(\\\) :: PrettyTree a -> [PrettyTree a] -> PrettyTree a
PrettyTree line [] Nothing \\\ lines = PrettyTree line lines Nothing
PrettyTree line sublines Nothing \\\ lines = PrettyTree line sublines (Just $ PrettyTree Nothing lines Nothing)
PrettyTree line sublines (Just rest) \\\ lines = PrettyTree line sublines (Just $ rest \\\ lines)

-- | Append to existing indented group
(\+\) :: PrettyTree a -> [PrettyTree a] -> PrettyTree a
PrettyTree line sublines Nothing \+\ lines = PrettyTree line (sublines ++ lines) Nothing
PrettyTree line sublines (Just rest) \+\ lines = PrettyTree line sublines (Just $ rest \+\ lines)

-- | New ribbon (non-obligatory)
(|||) :: PrettyTree a -> PrettyTree a -> PrettyTree a
PrettyTree line sublines Nothing ||| tree = PrettyTree line sublines (Just tree)
PrettyTree line sublines (Just rest) ||| tree = PrettyTree line sublines (Just $ rest ||| tree)

-- | Same as '|||'
(///) :: PrettyTree a -> PrettyTree a -> PrettyTree a
(///) = (|||)

-- | Same as '|+|'
(/+/) :: Monoid a => PrettyTree a -> PrettyTree a -> PrettyTree a
(/+/) = (|+|)

infixl 3 \\\, |||, ///, \+\, /+/

-------------------------------------------------------

(++|) :: Monoid a => a -> PrettyTree a -> PrettyTree a
a ++| (PrettyTree line sublines rest) = PrettyTree (Just a <> line) sublines rest

{-
(|++) :: Monoid a => PrettyTree a -> a -> PrettyTree a
(PrettyTree line [] Nothing) |++ a = PrettyTree (line <> a) [] Nothing
(PrettyTree line sublines Nothing) |++ a = PrettyTree line sublines (Just $ ribbon a)
(PrettyTree line sublines (Just rest)) |++ a = PrettyTree line sublines (Just $ rest |++ a)
-}

(|+|) :: Monoid a => PrettyTree a -> PrettyTree a -> PrettyTree a
(PrettyTree Nothing [] Nothing) |+| tree = tree
(PrettyTree (Just line) [] Nothing) |+| tree = line ++| tree
(PrettyTree line sublines Nothing) |+| tree = PrettyTree line sublines (Just tree)
(PrettyTree line sublines (Just rest)) |+| tree = PrettyTree line sublines (Just $ rest |+| tree)

(|++) :: Monoid a => PrettyTree a -> a -> PrettyTree a
tree |++ a = tree |+| ribbon a

treeGroup :: [PrettyTree a] -> PrettyTree a
treeGroup grp = PrettyTree Nothing grp Nothing

infixl 4 ++|, |++, |+|
