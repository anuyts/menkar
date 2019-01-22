{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper.Scoper where

import Prelude hiding (pi)

import Menkar.TC.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Fine.Syntax
--import Menkar.Fine.Judgement
import Menkar.Basic.Context
--import Menkar.Scoper.Context
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Control.Exception.AssertFalse
import Menkar.Fine.Multimode
import Menkar.PrettyPrint.Raw.Syntax

import Control.Monad.State.Lazy
import Control.Monad.List
import Data.Functor.Compose
import Data.Void
import Data.HashMap.Lazy
import Data.Functor.Identity
import Data.Coerce
import Control.Lens
import Data.Number.Nat

---------------------------

{- SEARCH FOR TODOS -}

{-| @'eliminator' gamma rawElim@ scopes @rawElim@ to a fine smart eliminator. -}
eliminator ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma (Raw.ElimDots) = return SmartElimDots
--eliminator gamma (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma (Raw.ElimArg argSpec rawExpr) = do
  fineExpr <- expr gamma rawExpr
  return $ SmartElimArg argSpec fineExpr
eliminator gamma (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

natLiteral ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Nat -> sc (Term mode modty v)
natLiteral n
  | n == 0 = return $ Expr3 $ TermCons $ ConsZero
  | otherwise = Expr3 . TermCons . ConsSuc <$> natLiteral (n - 1)

qname ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.QName ->
  sc (Term mode modty v)
qname gamma rawQName =
  let maybeLdivTelescopedVal = lookupQName gamma rawQName
  in case maybeLdivTelescopedVal of
       LookupResultNothing -> scopeFail $ "Not in scope: " ++ Raw.unparse rawQName
       LookupResultVar v -> return $ Var3 (unVarFromCtx v)
       LookupResultVal ldivTelescopedVal -> return $ Expr3 $ TermQName rawQName $ unVarFromCtx <$> ldivTelescopedVal
  
{-| @'expr3' gamma rawExpr@ scopes @rawExpr@ to a term. -}
expr3 :: (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma (Raw.ExprQName rawQName) = qname gamma rawQName
expr3 gamma (Raw.ExprParens rawExpr) = expr gamma rawExpr
expr3 gamma (Raw.ExprNatLiteral n) = natLiteral n
expr3 gamma (Raw.ExprImplicit) = newMetaTermNoCheck Nothing eqDeg gamma True "Infer explicitly omitted value."
expr3 gamma (Raw.ExprGoal str) = do
  result <- newMetaTermNoCheck Nothing eqDeg gamma True "Infer goal's value."
  return $ Expr3 $ TermGoal str result

{-| @'elimination' gamma rawElim@ scopes @rawElim@ to a term. -}
elimination ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Elimination ->
  sc (Term mode modty v)
elimination gamma (Raw.Elimination rawEliminee rawElims) = do
  fineEliminee <- expr3 gamma rawEliminee -- CMOD: Fix context
  --fineTy <- type4newImplicit gamma
  fineElims <- sequenceA (eliminator gamma <$> rawElims) -- CMOD: Fix modalities
  case fineElims of
    [] -> return fineEliminee
    _  -> do
      fineResult <- newMetaTermNoCheck Nothing eqDeg gamma True "Infer result of smart elimination."
      return . Expr3 $ TermSmartElim fineEliminee (Compose fineElims) fineResult
  --theMode <- mode4newImplicit gamma
  {-pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma fineEliminee fineTy fineElims fineResult,
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }-}
  --return fineResult

{-| @'expr2' gamma rawExpr@ scopes @rawExpr@ to a term. -}
expr2 ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Expr2 ->
  sc (Term mode modty v)
expr2 gamma (Raw.ExprElimination rawElim) = elimination gamma rawElim

--------------------------------------------------

{-| @'simpleLambda' gamma rawArg rawBody@ scopes the Menkar lambda-expression @<rawArg> > <rawBody>@ to a term. -}
simpleLambda ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Expr2 ->
  Raw.Expr ->
  sc (Term mode modty v)
simpleLambda gamma rawArg@(Raw.ExprElimination (Raw.Elimination boundArg [])) rawBody =
  do
    dmu <- newMetaModedModality Nothing (irrModedModality :\\ gamma) "Infer domain mode/modality."
    fineTy <- Type <$> newMetaTermNoCheck Nothing eqDeg (VarFromCtx <$> dmu :\\ gamma) False "Infer domain."
    maybeName <- case boundArg of
      Raw.ExprQName (Raw.Qualified [] name) -> return $ Just name
      Raw.ExprImplicit -> return $ Nothing
      _ -> scopeFail $
           "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg
    let fineSeg = Declaration {
          _decl'name = DeclNameSegment maybeName,
          _decl'modty = dmu,
          _decl'plicity = Explicit,
          _decl'content = fineTy
        }
    fineBody <- expr (gamma :.. (VarFromCtx <$> fineSeg)) rawBody
    return . Expr3 . TermCons . Lam $ Binding fineSeg fineBody
simpleLambda gamma rawArg rawBody =
  scopeFail $
  "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg

{-| @'buildPi' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> -> <fineCod>@ to a term. -}
buildPi ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildPi gamma fineSeg fineCod = do
  --fineLvl <- term4newImplicit gamma
  --fineMode <- mode4newImplicit gamma
  return $ Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding fineSeg fineCod

{-| @'buildSigma' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> >< <fineCod>@ to a term. -}
buildSigma ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildSigma gamma fineSeg fineCod = do
  --fineLvl <- term4newImplicit gamma
  --fineMode <- mode4newImplicit gamma
  return $ Expr3 $ TermCons $ ConsUniHS $ Sigma $ Binding fineSeg fineCod
  
{-| @'buildLambda' gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> > <fineBody>@ to a term. -}
buildLambda ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildLambda gamma fineSeg fineCod =
  return $ Expr3 $ TermCons $ Lam $ Binding fineSeg fineCod

{-| @'binder2' build gamma fineSegs rawArgs rawBody@ scopes the Menkar expression
    @<fineSegs> **> <rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder2 ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  ( forall w .
    DeBruijnLevel w =>
    Ctx Type mode modty w Void ->
    Segment Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v Void ->
  Telescoped Type Unit3 mode modty v ->
      {-^ remainder of the already-scoped part of the telescope on the left of the operator -}
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder2 build gamma (Telescoped Unit3) rawArgs rawBody = binder build gamma rawArgs rawBody
binder2 build gamma (fineSeg :|- fineSegs) rawArgs rawBody =
  build gamma fineSeg =<< binder2 build (gamma :.. (VarFromCtx <$> fineSeg)) fineSegs rawArgs rawBody
binder2 build gamma (mu :** fineSegs) rawArgs rawBody = unreachable

{-| @'binder' build gamma rawArgs rawBody@ scopes the Menkar expression
    @<rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  ( forall w .
    DeBruijnLevel w =>
    Ctx Type mode modty w Void ->
    Segment Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v Void ->
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder build gamma [] rawBody = expr gamma rawBody
binder build gamma (rawArg:rawArgs) rawBody = do
  fineArgTelescoped <- segment gamma rawArg
  binder2 build gamma fineArgTelescoped rawArgs rawBody

{-| @'telescopeOperation' gamma rawTheta rawOp maybeRawExprR@ scopes the Menkar expression
    @<rawTheta> <rawOp> <maybeRawExprR>@ to a term. -}
telescopeOperation ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Telescope -> {-^ telescope on the left of the operator -}
  Raw.Elimination -> {-^ the operator -}
  Maybe (Raw.Expr) -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
telescopeOperation gamma rawTheta
    rawOp@(Raw.Elimination _ (_ : _)) maybeRawExprR =
  scopeFail $ "Smart eliminations used on a binding operator: " ++ Raw.unparse rawOp
telescopeOperation gamma rawTheta
    rawOp@(Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op opString))) []) maybeRawExprR =
  case (opString, maybeRawExprR) of
    (">", Just rawBody) -> binder buildLambda gamma (Raw.untelescope rawTheta) rawBody
    ("><", Just rawCod) -> binder buildSigma gamma (Raw.untelescope rawTheta) rawCod
    ("->", Just rawCod) -> binder buildPi gamma (Raw.untelescope rawTheta) rawCod
                           -- rawCod does not refer to an unbaked fish.
    (_, Nothing) -> scopeFail $ "Binder body/codomain is missing: " ++ Raw.unparse
      (Raw.ExprOps (Raw.OperandTelescope rawTheta) $ Just (rawOp, maybeRawExprR))
    _    -> scopeFail $ "Illegal operator name '" ++ opString ++ "': " ++ Raw.unparse
      (Raw.ExprOps (Raw.OperandTelescope rawTheta) $ Just (rawOp, maybeRawExprR))
telescopeOperation gamma theta rawOp maybeRawExprR =
  scopeFail $ "Binding operator is not an unqualified name: " ++ Raw.unparse rawOp

{-
type Fixity = Double
data Associativity = AssocLeft | AssocRight | AssocAlone
data OpTree mode modty v =
  OpLeaf (Term mode modty v) |
  OpNode {
    nodeOp :: (Term mode modty v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeLOperand :: (OpTree mode modty v),
    nodeROperand :: (OpTree mode modty v)
    } |
  OpTelescoped {
    nodeOp :: (Term mode modty v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeTelescope :: (OpTree mode modty v),
    nodeROperand :: (OpTree mode modty v)
    }
  deriving (Functor, Foldable, Traversable, Generic1)

exprToTree :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr ->
  sc (OpTree mode modty v)
exprToTree gamma _ = _exprToTree
-}

{- YOU NEED TO RESOLVE FIXITY HERE -}
{-| @'expr' gamma rawExpr@ scopes @rawExpr@ to a term.
    For now, every operator is right associative with equal precedence. -}
expr ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Expr ->
  sc (Term mode modty v)
-- Operator-free expression (e.g. @5@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExpr) Nothing) = expr2 gamma rawExpr
-- Simple lambda (e.g. @x > f x@)
expr gamma fullRawExpr@
             (Raw.ExprOps
               (Raw.OperandExpr boundArg)
               (Just (Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op ">"))) rawElims, maybeRawBody))
             ) = case (rawElims, maybeRawBody) of
                   ([], Just rawBody) -> simpleLambda gamma boundArg rawBody
                   (_:_, _) -> scopeFail $ "Smart eliminations used on '>': " ++ Raw.unparse fullRawExpr
                   (_, Nothing) -> scopeFail $ "Body of lambda missing: " ++ Raw.unparse fullRawExpr
-- Unary operator expression (e.g. @5 ! .{arg = 3}@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Nothing))) = do
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr2to1 rawExprL)])
-- Binary operator expression (e.g. @a == .{A} b@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Just rawExprR))) = do
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr2to1 rawExprL),
                                              Raw.ElimArg Raw.ArgSpecExplicit rawExprR])
-- Naked telescope
expr gamma fullRawExpr@(Raw.ExprOps (Raw.OperandTelescope _) Nothing) =
  scopeFail $ "Naked telescope appears as expression: " ++ Raw.unparse fullRawExpr
-- Operation on telescope
expr gamma (Raw.ExprOps (Raw.OperandTelescope rawTheta) (Just (rawOp, maybeRawExprR))) =
  telescopeOperation gamma rawTheta rawOp maybeRawExprR

------------------------------------------------

{-| @'annotation' gamma rawAnnot@ scopes @rawAnnot@ to an annotation. -}
annotation ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Annotation ->
  sc (Annotation mode modty v)
annotation gamma (Raw.Annotation (Raw.Qualified [] "~") Nothing) = return AnnotImplicit
annotation gamma (Raw.Annotation qstring maybeRawArg) = do
  maybeFineArg <- sequenceA $ expr gamma <$> maybeRawArg
  annot4annot gamma qstring maybeFineArg

type family ScopeDeclSort (rawDeclSort :: Raw.DeclSort) :: DeclSort
type instance ScopeDeclSort Raw.DeclSortVal = DeclSortVal
type instance ScopeDeclSort (Raw.DeclSortModule False) = DeclSortModule
type instance ScopeDeclSort Raw.DeclSortSegment = DeclSortSegment

{- | @'buildDeclaration' gamma generateContent partDecl@ builds a list of telescoped declarations out of @partDecl@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildDeclaration ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v,
   ScopeDeclSort rawDeclSort ~ fineDeclSort, Functor (Type mode modty)) =>
  Ctx Type mode modty v Void ->
  {-| How to generate content if absent in the partial telescoped declaration. -}
  (forall w . DeBruijnLevel w => Ctx Type mode modty w Void -> sc (content mode modty w)) ->
  TelescopedPartialDeclaration rawDeclSort Type content mode modty v ->
  sc [Declaration fineDeclSort (Telescoped Type content) mode modty v]
buildDeclaration gamma generateContent partDecl = do
        -- allocate all implicits BEFORE name fork
        d <- case _pdecl'mode partDecl of
          Compose (Just d') -> return d'
          Compose Nothing -> newMetaMode Nothing (irrModedModality :\\ gamma) "Infer mode."
        mu <- case _pdecl'modty partDecl of
          Compose (Just mu') -> return mu'
          Compose Nothing -> newMetaModty Nothing (irrModedModality :\\ gamma) "Infer modality."
        let plic = case _pdecl'plicity partDecl of
              Compose (Just plic') -> plic'
              Compose Nothing -> Explicit
        telescopedContent <- mapTelescopedDB (
            \ wkn gammadelta (Maybe3 content) -> case content of
              Compose (Just content') -> return content'
              Compose (Nothing) -> generateContent gammadelta
          ) gamma $ _pdecl'content partDecl
          {-case _pdecl'content partDecl of
          Compose (Just ty') -> return ty'
          Compose Nothing -> lift $ generateContent-}
            --type4newImplicit gammadelta {- TODO adapt this for general telescoped declarations. -}
        names <- case _pdecl'names partDecl of
          Nothing -> assertFalse $ "Nameless partial declaration!"
          Just (Raw.DeclNamesSegment maybeNames) -> return $ DeclNameSegment <$> maybeNames
          Just (Raw.DeclNamesToplevelModule qname) -> assertFalse $ "Didn't expect a toplevel module here."
          Just (Raw.DeclNamesModule string) -> return $ [DeclNameModule string]
          Just (Raw.DeclNamesVal name) -> return $ [DeclNameVal name]
            --ListT . nameHandler $ _pdecl'names partDecl
        return $ names <&> \ name -> Declaration {
          _decl'name = name,
          _decl'modty = ModedModality d mu,
          _decl'plicity = plic,
          _decl'content = telescopedContent
          }

{-
{- | @'buildTelescopedDeclaration' gamma generateContent partTDecl@ builds a list of telescoped declarations out of @partTDecl@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildTelescopedDeclaration :: (MonadScoper mode modty rel sc, ScopeDeclSort rawDeclSort ~ fineDeclSort) =>
  Ctx Type mode modty v Void ->
  {-| How to generate content if absent in the partial telescoped declaration. -}
  (forall w . Ctx Type mode modty w Void -> sc (content mode modty w)) ->
  TelescopedPartialDeclaration rawDeclSort Type content mode modty v ->
  sc [TelescopedDeclaration fineDeclSort Type content mode modty v]
buildTelescopedDeclaration gamma generateContent partTDecl = runListT $ mapTelescopedDBSc (
    \ wkn gammadelta partDecl -> ListT $ buildDeclaration gammadelta (generateContent gammadelta) partDecl
  ) gamma partTDecl
-}

{- | @'buildSegment' gamma partSeg@ builds a list of segments out of @partSeg@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildSegment :: 
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  PartialSegment Type mode modty v ->
  sc [Segment Type mode modty v]
buildSegment gamma partSeg = runListT $ do
  teleSeg <- let gen gamma = Type <$> newMetaTermNoCheck Nothing eqDeg gamma False "Infer type."
             in  ListT $ buildDeclaration gamma gen partSeg
  return $ flip (over decl'content) teleSeg $ \ case
    Telescoped seg -> seg
    (seg' :|- seg) -> unreachable
    (mu :** seg) -> unreachable
    
{-| @'partialTelescopedDeclaration' gamma rawDecl@ scopes @rawDecl@ to a partial telescoped declaration. -}
partialTelescopedDeclaration ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Declaration rawDeclSort ->
  sc (TelescopedPartialDeclaration rawDeclSort Type Type mode modty v)
partialTelescopedDeclaration gamma rawDecl = (flip execStateT newPartialDeclaration) $ do
  --telescope
  fineDelta <- telescope gamma $ Raw.decl'telescope rawDecl
  --names
  pdecl'names .= (Just $ Raw.decl'names rawDecl)
  --type
  fineContent <- mapTelescopedDB (
      \wkn gammadelta Unit3 -> case Raw.decl'content rawDecl of
        Raw.DeclContentEmpty -> return $ Maybe3 $ Compose $ Nothing
        Raw.DeclContent rawTy -> Maybe3 . Compose . Just <$> do
          --fineLvl <- term4newImplicit gammadelta
          Type <$> expr gammadelta rawTy
    ) gamma fineDelta
  pdecl'content .= fineContent
  --annotations
  fineAnnots <- sequenceA $ annotation gamma <$> Raw.decl'annotations rawDecl
  forM_ fineAnnots $
            \ fineAnnot ->
              case fineAnnot of
                AnnotMode fineMode -> do
                  -- _Wrapped' is a lens for Compose
                  maybeOldFineMode <- use $ pdecl'mode._Wrapped'
                  case maybeOldFineMode of
                    Just oldFineMode -> scopeFail $ "Encountered multiple mode annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'mode._Wrapped' .= Just fineMode
                AnnotModality fineModty -> do
                  maybeOldFineModty <- use $ pdecl'modty._Wrapped'
                  case maybeOldFineModty of
                    Just oldFineModty -> scopeFail $ "Encountered multiple modality annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'modty._Wrapped' .= Just fineModty
                AnnotImplicit -> do
                  maybeOldFinePlicity <- use $ pdecl'plicity._Wrapped'
                  case maybeOldFinePlicity of
                    Just oldFinePlicity -> scopeFail $ "Encountered multiple visibility annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'plicity._Wrapped' .= Just Implicit
  return ()

{-| @'partialSegment' gamma rawSeg@ scopes @rawSeg@ to a partial segment. -}
partialSegment ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Declaration Raw.DeclSortSegment ->
  --sc [Segment Type mode modty v]
  sc (PartialSegment Type mode modty v)
partialSegment gamma rawSeg = do
  telescopedPartSeg <- partialTelescopedDeclaration gamma rawSeg
  case _pdecl'content telescopedPartSeg of
    Telescoped (Maybe3 ty) -> flip pdecl'content telescopedPartSeg $ \_ -> return $ Telescoped $ Maybe3 ty
    _ -> unreachable -- nested segments encountered

{-
  case telescopedPartSeg of
    Telescoped partSeg -> return partSeg
    _ -> unreachable -- nested segments encountered
-}

{-| Chain a list of fine segments to a fine telescope; while avoiding shadowing. -}
segments2telescoped :: --MonadScoper mode modty rel sc =>
  (MonadScoper mode modty rel sc, Functor mode, Functor modty) =>
  Ctx Type mode modty v Void ->
  [Segment Type mode modty v] ->
  sc (Telescoped Type Unit3 mode modty v)
segments2telescoped gamma [] =
  return $ Telescoped Unit3
segments2telescoped gamma (fineSeg:fineSegs) = do
  let DeclNameSegment maybeNewName = _decl'name fineSeg
  case maybeNewName of
    Nothing -> return ()
    Just newName -> case lookupQName gamma (Raw.Qualified [] newName) of
      LookupResultNothing -> return ()
      _ -> scopeFail $ "Shadowing is not allowed in variable names; already in scope: " ++ unparse newName
  (fineSeg :|-) <$> segments2telescoped (gamma :.. (VarFromCtx <$> fineSeg)) (fmap VarWkn <$> fineSegs)

segment ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Segment ->
  sc (Telescoped Type Unit3 mode modty v)
segment gamma (Raw.Segment rawDecl) = do
  partialSeg <- partialSegment gamma rawDecl
  segments2telescoped gamma =<< buildSegment gamma partialSeg

{-| scope a partly fine, partly raw telescope to a fine telescope. -}
telescope2 ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Telescoped Type Unit3 mode modty v ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope2 gamma (Telescoped Unit3) rawTele = telescope gamma rawTele
telescope2 gamma (fineSeg :|- fineSegs) rawTele =
  (fineSeg :|-) <$> telescope2 (gamma :.. (VarFromCtx <$> fineSeg)) fineSegs rawTele
telescope2 gamma (mu :** fineSegs) rawTele = unreachable

telescope ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope gamma (Raw.Telescope []) = return $ Telescoped Unit3
telescope gamma (Raw.Telescope (rawSeg : rawSegs)) = do
  fineFrontSegs <- segment gamma rawSeg
  telescope2 gamma fineFrontSegs (Raw.Telescope rawSegs)

----------------------------------------------------------

{-| Scope a raw LHS and a raw value RHS to a value, or fail. -}
val ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Declaration Raw.DeclSortVal ->
  Raw.RHS Raw.DeclSortVal ->
  sc (Val mode modty v)
val gamma rawLHS (Raw.RHSVal rawExpr) = do
  partialLHS <- partialTelescopedDeclaration gamma rawLHS
  [fineLHS] <- let gen gamma = Type <$> newMetaTermNoCheck Nothing eqDeg gamma False "Infer type."
               in  buildDeclaration gamma gen partialLHS
  val <- flip decl'content fineLHS $ mapTelescopedDB (
      \wkn gammadelta fineTy -> do
        fineTm <- expr gammadelta rawExpr
        return $ ValRHS fineTm fineTy
    ) gamma
  case lookupQName gamma (Raw.Qualified [] $ _val'name val) of
    LookupResultNothing -> return val
    _ -> scopeFail $ "Shadowing is not allowed in value names; already in scope: " ++ unparse (_val'name val)

{-| @'entryInModule' gamma fineModule rawEntry@ scopes the entry @rawEntry@ as part of the module @fineModule@ -}
entryInModule ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.AnyEntry ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entryInModule gamma rawEntry fineModule = do
  let gammaModule = gamma :<...> VarFromCtx <$> fineModule
        {-(Left <$> ModuleInScope {
          moduleContramod = ModedContramodality d _confused,
          moduleContents = modul
        })-}
  fineEntry <- anyEntry gammaModule rawEntry
  return $ addToModule fineEntry fineModule

{-| @'entriesInModule' gamma fineModule rawEntry@ scopes @rawEntries@ as part of the module @fineModule@ -}
entriesInModule ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  [Raw.AnyEntry] ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entriesInModule gamma rawEntries fineModule = foldl (>>=) (return fineModule) (entryInModule gamma <$> rawEntries)

{-| @'modul' gamma rawLHS rawRHS@ scopes the module @<rawLHS> <rawRHS>@ (not the top-level module). -}
modul ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Declaration (Raw.DeclSortModule False) ->
  Raw.RHS (Raw.DeclSortModule False) ->
  sc (Module mode modty v)
modul gamma rawLHS rawRHS@(Raw.RHSModule rawEntries) = do
  partialLHS <- partialTelescopedDeclaration gamma rawLHS
  partialLHSUntyped <- flip pdecl'content partialLHS $ mapTelescopedDB (
      \wkn gammadelta (Maybe3 maybeFineTy) -> case maybeFineTy of
        Compose Nothing -> return $ Maybe3 $ Compose Nothing
        Compose (Just fineTy) -> scopeFail $ "Modules do not have a type: " ++ Raw.unparse rawLHS
    ) gamma
  [fineLHS] <- buildDeclaration gamma (\gammadelta -> return Unit3) partialLHSUntyped
  flip decl'content fineLHS $ mapTelescopedDB (
      \wkn gammadelta Unit3 -> entriesInModule gammadelta rawEntries newModule
    ) gamma
--modul gamma rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

entry ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.Entry rawDeclSort ->
  sc (Entry mode modty v)
entry gamma (Raw.EntryLR Raw.HeaderVal rawLHS rawRHS) = EntryVal <$> val gamma rawLHS rawRHS
entry gamma (Raw.EntryLR Raw.HeaderModule rawLHS rawRHS) = EntryModule <$> modul gamma rawLHS rawRHS
entry gamma rawEntry = scopeFail $ "Nonsensical or unsupported entry: " ++ Raw.unparse rawEntry

anyEntry ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.AnyEntry ->
  sc (Entry mode modty v)
anyEntry gamma (Raw.AnyEntry rawEntry) = entry gamma rawEntry

file ::
  (MonadScoper mode modty rel sc, DeBruijnLevel v) =>
  Ctx Type mode modty v Void ->
  Raw.File ->
  sc (Entry mode modty v)
file gamma rawFile = entry gamma (Raw.file2nestedModules rawFile)
