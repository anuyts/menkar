module Menkar.System.Scoper where

import Menkar.Fine
import Menkar.Monad
import qualified Menkar.Raw as Raw
import Menkar.Analyzer
import qualified Menkar.System.PrettyPrint.Raw as Raw

import Data.Functor.Functor1

import Data.Void
import GHC.Generics

class (SysSyntax (Term sys) sys, Raw.SysRawPretty sys) => SysScoper sys where
  rawRootAnnots :: [Raw.Annotation sys]
  scopeAnnotation :: (MonadScoper sys sc, DeBruijnLevel v) => Ctx Type sys v -> 
    String -> Maybe (Raw.ExprC sys) -> sc (Annotation sys v)
  scopeSysExprC :: (MonadScoper sys sc, DeBruijnLevel v) => Ctx Type sys v ->
    Raw.SysExprC sys -> sc (Term sys v)
  newMetaModeNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Ctx Type sys v -> String -> sc (Mode sys v)
  newMetaModtyNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Ctx Type sys v -> String -> sc (Modality sys v)
  newMetaClassif4sysASTNoCheck :: forall sc t v .
    (MonadScoper sys sc, DeBruijnLevel v, SysAnalyzer sys, Analyzable sys t) =>
    SysAnalyzableToken sys t ->
    Ctx Type sys v ->
    t v ->
    ClassifExtraInput t v ->
    String ->
    sc (Classif t v)

newMetaModedModalityNoCheck :: (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  String ->
  sc (ModedModality sys v)
newMetaModedModalityNoCheck = newMetaModtyNoCheck
{-newMetaModedModalityNoCheck gamma reason = do
  dom <- newMetaModeNoCheck gamma reason
  cod <- newMetaModeNoCheck gamma reason
  mu <- newMetaModtyNoCheck gamma reason
  return $ ModedModality dom cod mu-}

newMetaClassif4astNoCheck :: forall sys sc t v .
  (MonadScoper sys sc, DeBruijnLevel v, SysScoper sys, SysAnalyzer sys, Analyzable sys t) =>
  --AnalyzableToken sys t ->
  Ctx Type sys v ->
  t v ->
  ClassifExtraInput t v ->
  String ->
  sc (Classif t v)
newMetaClassif4astNoCheck gamma t extraT reason = do
  case (analyzableToken :: AnalyzableToken sys t, t) of
    (AnTokenModalityTo, _) -> do
      cod <- newMetaModeNoCheck gamma reason
      return $ cod
    (AnTokenBinding tokenRHS, Binding seg rhs) -> do
      crhs <- newMetaClassif4astNoCheck (gamma :.. seg) rhs U1 reason
      return $ U1 :*: (NamedBinding (getDeclNameSegment . _decl'name $ seg) $ Const1 $ crhs)
                    --ClassifBinding seg crhs
{-    (AnTokenClassifBinding tokenRHS, ClassifBinding seg rhs) -> do
      let Comp1 extraRHS = extraT
      crhs <- newMetaClassif4astNoCheck maybeParent (gamma :.. seg) rhs extraRHS reason
      return $ ClassifBinding seg crhs-}
    (AnTokenNamedBinding tokenRHS, NamedBinding maybeName (rhs :: rhs sys (VarExt v))) -> do
      --let seg = fst1 extraT
      --let extraRHS = unComp1 $ snd1 extraT
      let seg :*: Comp1 extraRHS = extraT
      crhs <- newMetaClassif4astNoCheck @sys @sc @(rhs sys) @(VarExt v)
        (gamma :.. seg) rhs extraRHS reason
      return $ NamedBinding (getDeclNameSegment . _decl'name $ seg) $ Const1 $ crhs
             --ClassifBinding seg crhs
    (AnTokenModalBox tokenContent, ModalBox (content :: content sys v)) -> do
      let dmu :*: extraContent = extraT
      cContent <- newMetaClassif4astNoCheck @sys @sc @(content sys) @v
        (dmu :\\ gamma) content extraContent reason
      return $ ModalBox $ Const1 $ cContent
    (AnTokenUniHSConstructor, _) -> ModalBox . Const1 <$> newMetaModeNoCheck gamma reason
    (AnTokenConstructorTerm, _) -> newMetaTypeNoCheck gamma reason
    (AnTokenType, _) -> return U1
    (AnTokenDependentEliminator, _) -> return U1
    (AnTokenEliminator, _) -> newMetaTypeNoCheck gamma reason
    (AnTokenTermNV, _) -> newMetaTypeNoCheck gamma reason
    (AnTokenTerm, _) -> newMetaTypeNoCheck gamma reason
    (AnTokenDeclaration tokenRHS, decl) -> do
      newMetaClassif4astNoCheck gamma (_decl'content decl) extraT reason
    (AnTokenTelescoped tokenRHS, _) -> return U1
    (AnTokenValRHS, _) -> return U1
    (AnTokenModuleRHS, _) -> return U1
    (AnTokenEntry, _) -> return U1
    (AnTokenU1, _) -> return U1
    (AnTokenPair1 tokenF tokenG, fv :*: gv) ->
      (:*:) <$> newMetaClassif4astNoCheck gamma fv (fst1 extraT) reason
            <*> newMetaClassif4astNoCheck gamma gv (snd1 extraT) reason
    (AnTokenConst1 token, Const1 t) -> newMetaClassif4astNoCheck gamma t extraT reason
    (AnTokenSys sysToken, _) -> newMetaClassif4sysASTNoCheck sysToken gamma t extraT reason
    (AnTokenMultimode AnTokenMode, _) -> return U1
    (AnTokenMultimode AnTokenModality, _) -> do
      dom <- newMetaModeNoCheck gamma reason
      cod <- newMetaModeNoCheck gamma reason
      return $ dom :*: cod
    (AnTokenMultimode AnTokenDegree, _) -> newMetaModeNoCheck gamma reason
    (AnTokenSysTerm, _) -> newMetaTypeNoCheck gamma reason
    (AnTokenSysUniHSConstructor, _) -> ModalBox . Const1 <$> newMetaModeNoCheck gamma reason
    --_ -> _newMetaClassifNoCheck
