{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass, UndecidableInstances #-}

module Menkar.TC.Monad.TCDTT where

import Menkar.Basic
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Multimode.Trivial
import Menkar.TC.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context

import Text.PrettyPrint.Tree

import GHC.Generics (U1 (..))
import Data.Void
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Proxy
import Data.IntMap.Strict
import Control.Monad.Cont
import Control.Monad.State.Lazy
import Control.Monad.List
import Control.Monad.Except
import Control.Lens

data TCResult = TCSuccess | TCWaiting

data MetaInfo = forall v . (DeBruijnLevel v) => MetaInfo {
  _metaInfo'maybeParent :: Maybe (Constraint U1 U1 U1),
  _metaInfo'context :: Ctx Type U1 U1 v Void,
  --_metaInfo'deg :: U1 v,
  _metaInfo'reason :: String,
  _metaInfo'solution :: Maybe (Term U1 U1 v)
  }

data TCState = TCState {
  _tcState'metaCounter :: Int,
  _tcState'metaMap :: IntMap MetaInfo
  }

makeLenses ''TCState

data TCError =
  TCErrorConstraintBound |
  TCErrorBlocked |
  TCErrorTCFail |
  TCErrorScopeFail String

newtype TCT m a = TCT {unTCT :: ContT TCResult (StateT TCState ({-ListT-} (ExceptT TCError m))) a}
  deriving (Functor, Applicative, Monad, MonadState TCState)

runTCT :: (Monad m) => TCT m () -> TCState -> ExceptT TCError m (TCResult, TCState)
runTCT program initState = flip runStateT initState $ runContT (unTCT program) (\() -> return TCSuccess)

type TC = TCT Identity

runTC :: TC () -> TCState -> Except TCError (TCResult, TCState)
runTC = runTCT

instance {-# OVERLAPPING #-} (Monad m) => MonadScoper U1 U1 U1 (TCT m) where
  
  annot4annot gamma qstring args = case (qstring, args) of
    (Raw.Qualified [] "~", []) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render defaultRenderState $
             Raw.unparse' qstring \\\ fine2pretty (ctx2scCtx gamma) <$> args
           )

  newMetaTermNoCheck maybeParent deg gamma reason = do
    meta <- tcState'metaCounter <<%= (+1)
    tcState'metaMap %= (insert meta $ MetaInfo maybeParent gamma reason Nothing)
    let depcies = Compose $ Var3 <$> listAll Proxy
    return $ Expr3 $ TermMeta meta depcies

  newMetaMode maybeParent gamma reason = return U1

  newMetaModty maybeParent gamma reason = return U1

  scopeFail reason = TCT . lift . lift . throwError $ TCErrorScopeFail reason
