module Menkar.Systems.Reldtt.Scoper where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Basic
import qualified Menkar.Systems.Reldtt.Raw as Raw
import qualified Menkar.Systems.Reldtt.PrettyPrint.Raw as Raw
import Menkar.Systems.Reldtt.Fine
import Menkar.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Scoper
import Menkar.Systems.Reldtt.Analyzer

import Text.PrettyPrint.Tree
import Data.Omissible
import Control.Exception.AssertFalse

import Data.Maybe
import Data.Void
import Data.Functor.Compose
import Data.Functor.Coerce
import GHC.Generics
import Util (snocView)

scopeTailAspect :: (MonadScoper Reldtt sc, DeBruijnLevel v) =>
  Ctx Type Reldtt v Void ->
  Raw.ModtyTailAspect ->
  sc (ModtyTail v)
scopeTailAspect gamma (Raw.ModtyTailAspect str rawD) = do
  fineD <- ReldttMode !<$> exprC gamma rawD
  case str of
    "cont" -> return $ TailCont fineD
    "disc" -> return $ TailDisc fineD
    "forget" -> return $ TailForget fineD
    otherwise -> scopeFail $ "Illegal tail aspect: `" ++ str ++ "`."

foldTailAspects :: (MonadScoper Reldtt sc, DeBruijnLevel v) =>
  [ModtyTail v] ->
  sc (ModtyTail v)
foldTailAspects aspects = case snocView aspects of
  Nothing -> return $ TailEmpty
  Just (initAspects, lastAspect) -> do
    initFold <- foldTailAspects initAspects
    case (initFold, lastAspect) of
      (TailEmpty, _) -> return lastAspect
      (_, TailEmpty) -> unreachable
      (TailCont d, _) -> scopeFail "Tail aspect 'cont' must be the only tail aspect in the modality signature."
      (_, TailCont d) -> scopeFail "Tail aspect 'cont' must be the only tail aspect in the modality signature."
      (TailDisc cod, TailForget dom) -> return $ TailDiscForget dom cod
      (TailForget dom, TailDisc cod) -> return $ TailDiscForget dom cod
      (_, _) -> scopeFail "A tail aspect ('disc' or 'forget') occurs twice in the same modality signature."

instance SysScoper Reldtt where
  -- If you get an error here, consider modifying a meaningless comment in Menkar.Raw.Syntax.Syntax.
  -- That file somehow corrupts the state of the compiler.
  rawRootAnnots = [Raw.Annotation "*" $ Just $ Raw.ExprSys $ Raw.KnownModty (ModtySnout 0 0 []) (Raw.ModtyTail [])]
  
  scopeAnnotation gamma qstring maybeRawArg = do
    let dgamma' = ctx'mode gamma
    case qstring of
      {-Raw.Qualified [] "d" -> case maybeRawArg of
        Nothing -> scopeFail $ "Annotation `d` requires an argument."
        Just rawArg -> AnnotMode . ReldttMode <$> expr (crispModedModality dgamma' :\\ gamma) rawArg-}
      "*" -> case maybeRawArg of
        Nothing -> scopeFail $ "Annotation `*` requires an argument."
        Just rawArg -> do
          mu <- exprC (crispModedModality dgamma' :\\ gamma) rawArg
          ddom <- newMetaModeNoCheck gamma "Inferring domain of modality."
          dcod <- newMetaModeNoCheck gamma "Inferring codomain of modality."
          return $ AnnotModality $ wrapInChainModty ddom dcod mu
      _   -> scopeFail $ "Illegal annotation: " ++ (render
               (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
               $? id
             )
  scopeSysExprC gamma (Raw.KnownModty snout rawTail) = do
    fineTailAspects <- sequenceA $ scopeTailAspect gamma <$> Raw._modtyTail'aspects rawTail
    fineTail <- foldTailAspects fineTailAspects
    return $ BareKnownModty $ KnownModty snout fineTail
  newMetaModeNoCheck gamma reason = ReldttMode !<$> newMetaTermNoCheck gamma MetaBlocked Nothing reason
  newMetaModtyNoCheck gamma reason = do
    dom <- newMetaModeNoCheck gamma $ reason ++ " (domain)"
    cod <- newMetaModeNoCheck gamma $ reason ++ " (codomain)"
    tmu <- newMetaTermNoCheck gamma MetaBlocked Nothing reason
    --(meta, depcies) <- newMetaID gamma reason
    return $ wrapInChainModty dom cod tmu
      --ChainModtyMeta ddom dcod meta (Compose depcies)
    --Expr2 (TermMeta )
    --wrapInChainModty ddom dcod <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason

  newMetaClassif4sysASTNoCheck sysToken gamma t extraT reason =
    case (sysToken, t) of
      (AnTokenModeTerm, _) -> return U1
      (AnTokenModtyTerm, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
      (AnTokenKnownModty, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
      (AnTokenModtySnout, _) -> return U1
      (AnTokenModtyTail, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
