module Menkar.System.Scoper where

import Menkar.Fine
import Menkar.Monad
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Analyzer

import Data.Functor.Functor1

import Data.Void
import GHC.Generics

class SysSyntax (Term sys) sys => SysScoper sys where
  scopeAnnotation :: (MonadScoper sys sc, DeBruijnLevel v) => Ctx Type sys v Void -> 
    Raw.Qualified String -> Maybe (Raw.Expr) -> sc (Annotation sys v)
  newMetaModeNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Mode sys v)
  newMetaModtyNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Modality sys v)
  newMetaClassif4sysASTNoCheck :: forall sc t v .
    (MonadScoper sys sc, DeBruijnLevel v, SysAnalyzer sys, Analyzable sys t) =>
    SysAnalyzableToken sys t ->
    Maybe (Constraint sys) ->
    Ctx Type sys v Void ->
    t v ->
    AnalyzerExtraInput t v ->
    String ->
    sc (Classif t v)

newMetaModedModalityNoCheck :: (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  String ->
  sc (ModedModality sys v)
newMetaModedModalityNoCheck parent gamma reason = do
  dom <- newMetaModeNoCheck parent gamma reason
  cod <- newMetaModeNoCheck parent gamma reason
  mu <- newMetaModtyNoCheck parent gamma reason
  return $ ModedModality dom cod mu

newMetaClassif4astNoCheck :: forall sys sc t v .
  (MonadScoper sys sc, DeBruijnLevel v, SysScoper sys, SysAnalyzer sys, Analyzable sys t) =>
  --AnalyzableToken sys t ->
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  String ->
  sc (Classif t v)
newMetaClassif4astNoCheck maybeParent gamma t extraT reason = do
  case (analyzableToken :: AnalyzableToken sys t, t) of
    (AnTokenModedModality, _) -> do
      dom <- newMetaModeNoCheck maybeParent gamma reason
      cod <- newMetaModeNoCheck maybeParent gamma reason
      return $ dom :*: cod
    (AnTokenBinding tokenRHS, Binding seg rhs) -> do
      crhs <- newMetaClassif4astNoCheck maybeParent (gamma :.. VarFromCtx <$> seg) rhs U1 reason
      return $ U1 :*: ClassifBinding seg crhs
    (AnTokenClassifBinding tokenRHS, ClassifBinding seg rhs) -> do
      let Comp1 extraRHS = extraT
      crhs <- newMetaClassif4astNoCheck maybeParent (gamma :.. VarFromCtx <$> seg) rhs extraRHS reason
      return $ ClassifBinding seg crhs
    (AnTokenNamedBinding tokenRHS, NamedBinding maybeName (rhs :: rhs sys (VarExt v))) -> do
      --let seg = fst1 extraT
      --let extraRHS = unComp1 $ snd1 extraT
      let seg :*: Comp1 extraRHS = extraT
      crhs <- newMetaClassif4astNoCheck @sys @sc @(rhs sys) @(VarExt v)
        maybeParent (gamma :.. VarFromCtx <$> seg) rhs extraRHS reason
      return $ ClassifBinding seg crhs
    (AnTokenUniHSConstructor, _) -> newMetaModeNoCheck maybeParent gamma reason
    (AnTokenConstructorTerm, _) -> newMetaTypeNoCheck maybeParent gamma reason
    (AnTokenType, _) -> return U1
    (AnTokenDependentEliminator, _) -> return U1
    (AnTokenEliminator, _) -> newMetaTypeNoCheck maybeParent gamma reason
    (AnTokenTermNV, _) -> newMetaTypeNoCheck maybeParent gamma reason
    (AnTokenTerm, _) -> newMetaTypeNoCheck maybeParent gamma reason
    (AnTokenDeclaration tokenRHS, decl) -> do
      newMetaClassif4astNoCheck maybeParent gamma (_decl'content decl) extraT reason
    (AnTokenTelescoped tokenRHS, _) -> return U1
    (AnTokenValRHS, _) -> return U1
    (AnTokenModuleRHS, _) -> return U1
    (AnTokenEntry, _) -> return U1
    (AnTokenU1, _) -> return U1
    (AnTokenPair1 tokenF tokenG, fv :*: gv) ->
      (:*:) <$> newMetaClassif4astNoCheck maybeParent gamma fv (fst1 extraT) reason
            <*> newMetaClassif4astNoCheck maybeParent gamma gv (snd1 extraT) reason
    (AnTokenSys sysToken, _) -> newMetaClassif4sysASTNoCheck sysToken maybeParent gamma t extraT reason
    --_ -> _newMetaClassifNoCheck
