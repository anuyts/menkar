module Menkar.TC.SmartElim where

import Menkar.System
import Menkar.System.TC
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import Menkar.Analyzer
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.WHN

import Data.Functor.Functor1

import GHC.Generics
import Data.Void
import Control.Lens
import Data.Functor.Compose
import Data.Functor.Constant
import Control.Monad
import Control.Monad.Writer.Lazy
import Control.Monad.Trans.Maybe

{- Checking of modalities proceeds as follows:
   -------------------------------------------
   - Naively, for every JudSmartElim we could check the next modality. However this is awkward:
     - There may not be a next modality,
     - It's confusing when popping (though the current approach is also confusing): you'd have to check the
       poppee upon popping.
     - We still have to equate modes at some point.
   - Instead, we always check the modality of a dumb elimination when we apply it.
     - Immediately after that, we relate it to the modality expected by the type and the elimination.
     - That means we can check the modality against the expected domain and codomain right away.
   - When popping, we check the split modality, because afterwards it's never seen again.
     - Immediately after that, we relate it to the composite of the poppee and the remainder.
     - That means we can check the modality against the poppee's domain and the remainder's codomain right away.
-}

-------

{-| Handles a smartelim-judgement with 0 eliminations.
-}
checkSmartElimDone :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  Maybe (Modality sys v) ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElimDone gamma eliminee tyEliminee maybeMuElim result tyResult = do
      let dgamma' = ctx'mode gamma
      let dgamma = unVarFromCtx <$> dgamma'
      case maybeMuElim of
        Nothing -> return ()
        Just muElim -> do
          {-addNewConstraint
            (JudRel analyzableToken (Eta True) U1
              (crispModalityTo dgamma' :\\ duplicateCtx gamma)
              (Twice1 (_modality'dom muElim) (_modality'cod muElim))
              (Twice1 U1 U1)
              (ClassifWillBe $ Twice1 U1 U1)
            )
            "End of elimination: checking if modes match."-}
          addNewConstraint
            (Jud analyzableToken
              (crispModalityTo dgamma' :\\ gamma)
              (muElim)
              U1
              (ClassifMustBe $ dgamma :*: dgamma)
            )
            "End of elimination: Checking elimination modality."
          addNewConstraint
            (JudRel analyzableToken (Eta True) (Const ModEq)
              (crispModalityTo dgamma' :\\ duplicateCtx gamma)
              (Twice1 muElim (idMod dgamma))
              (Twice1 U1 U1)
              (ClassifWillBe $ Twice1 (dgamma :*: dgamma) (dgamma :*: dgamma))
            )
            "End of elimination: Checking whether actual elimination modality equals expected modality (namely identity)."
      addNewConstraint
        (JudTypeRel
          (modedEqDeg dgamma)
          (duplicateCtx gamma)
          (Twice2 tyEliminee tyResult)
        )
        "End of elimination: checking if types match."
      addNewConstraint
        (JudTermRel
          (Eta True)
          (modedEqDeg dgamma)
          (duplicateCtx gamma)
          (Twice2 eliminee result)
          (Twice2 tyEliminee tyResult)
        )
        "End of elimination: checking if results match"

discard :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  ModedModality sys v {-^ The modality by which we need to unbox (likely to be inferred.) -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including unbox). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
discard gamma eliminee tyEliminee dmuInfer eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dImmedResult = elimineeMode gamma eliminators
  addNewConstraint
    (Jud analyzableToken
      (crispModalityTo dgamma' :\\ gamma)
      dmuInfer
      U1
      (ClassifMustBe $ dImmedResult :*: dImmedResult)
    )
    "Doing nothing: Checking elimination modality."
  addNewConstraint
    (JudRel analyzableToken (Eta True) (Const ModEq)
      (crispModalityTo dgamma' :\\ duplicateCtx gamma)
      (Twice1
        (idMod dImmedResult)
        dmuInfer
      )
      (Twice1 U1 U1)
      (ClassifMustBe $ (\x -> Twice1 x x) $ dImmedResult :*: dImmedResult)
    )
    "Doing nothing: Checking whether actual elimination modality equals expected modality (namely identity)."
  addNewConstraint
    (JudSmartElim
      gamma
      eliminee
      tyEliminee
      eliminators
      result
      tyResult
    )
    "Doing nothing."

unbox :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Segment Type sys v ->
  ModedModality sys v {-^ The modality by which we need to unbox (likely to be inferred.) -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including unbox). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
unbox gamma eliminee boxSeg dmuInfer eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmuBox = _modalityTo'mod $ _segment'modty boxSeg
  let dmuUnbox = modedApproxLeftAdjointProj dmuBox
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dImmedResult = elimineeMode gamma eliminators
  addNewConstraint
    (Jud analyzableToken
      (crispModalityTo dgamma' :\\ gamma)
      dmuInfer
      U1
      (ClassifMustBe $ _modality'dom dmuUnbox :*: dImmedResult)
    )
    "Unboxing: Checking elimination modality."
  addNewConstraint
    (JudRel analyzableToken (Eta True) (Const ModEq)
      (crispModalityTo dgamma' :\\ duplicateCtx gamma)
      (Twice1
        dmuUnbox
        dmuInfer
      )
      (Twice1 U1 U1)
      (ClassifMustBe $ (\x -> Twice1 x x) $ _modality'dom dmuUnbox :*: dImmedResult)
    )
    "Unboxing: Checking whether actual elimination modality equals expected modality."
  addNewConstraint
    (JudSmartElim
      gamma
      (Expr2 $ TermElim
        (withDom dmuUnbox)
        eliminee
        (BoxType boxSeg)
        Unbox
      )
      (_segment'content boxSeg)
      eliminators
      result
      tyResult
    )
    "Unboxing."

projFst :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Type sys v ->
  ModedModality sys v {-^ The modality by which we need to project (likely to be inferred.) -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including fst). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
projFst gamma eliminee sigmaBinding dmuInfer eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmuSigma = _modalityTo'mod $ _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = modedApproxLeftAdjointProj dmuSigma
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dImmedResult = elimineeMode gamma eliminators
  addNewConstraint
    (Jud analyzableToken
      (crispModalityTo dgamma' :\\ gamma)
      dmuInfer
      U1
      (ClassifMustBe $ _modality'dom dmuProjFst :*: dImmedResult)
    )
    "First projection: Checking elimination modality."
  addNewConstraint
    (JudRel analyzableToken (Eta True) (Const ModEq)
      (crispModalityTo dgamma' :\\ duplicateCtx gamma)
      (Twice1 dmuProjFst dmuInfer)
      (Twice1 U1 U1)
      (ClassifMustBe $ (\x -> Twice1 x x) $ _modality'dom dmuProjFst :*: dImmedResult)
    )
    "First projection: Checking whether actual elimination modality equals expected modality."
  addNewConstraint
    (JudSmartElim
      gamma
      (Expr2 $ TermElim
        (withDom dmuProjFst)
        eliminee
        (Sigma sigmaBinding)
        Fst
      )
      (_segment'content $ binding'segment sigmaBinding)
      eliminators
      result
      tyResult
    )
    "First projection."

projSnd :: forall sys tc v . 
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Type sys v ->
  ModedModality sys v {-^ The modality by which we need to project (likely to be inferred.) -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including snd). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
projSnd gamma eliminee sigmaBinding dmuInfer eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmuSigma = _modalityTo'mod $ _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = modedApproxLeftAdjointProj dmuSigma
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dImmedResult = elimineeMode gamma eliminators
  let tmFst = (Expr2 $ TermElim
                (withDom dmuProjFst)
                eliminee
                (Sigma sigmaBinding)
                Fst
              )
  let tmSnd = (Expr2 $ TermElim
                (idModalityTo $ unVarFromCtx <$> ctx'mode gamma)
                eliminee
                (Sigma sigmaBinding)
                Snd
              )
  addNewConstraint
    (Jud analyzableToken
      (crispModalityTo dgamma' :\\ gamma)
      dmuInfer
      U1
      (ClassifMustBe $ dImmedResult :*: dImmedResult)
    )
    "Second projection: Checking elimination modality."
  addNewConstraint
    (JudRel analyzableToken (Eta True) (Const ModEq)
      (crispModalityTo dgamma' :\\ duplicateCtx gamma)
      (Twice1
        (idMod $ _modality'dom dmuElimTotal)
        (dmuInfer)
      )
      (Twice1 U1 U1)
      (ClassifWillBe $ Twice1
        (dImmedResult :*: dImmedResult)
        (dImmedResult :*: dImmedResult)
      )
    )
    "Second projection: Checking whether actual elimination modality equals expected modality (namely identity)."
  addNewConstraint
    (JudSmartElim
      gamma
      tmSnd
      (substLast2 tmFst $ binding'body sigmaBinding)
      eliminators
      result
      tyResult
    )
    "Second projection."

apply :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Type sys v ->
  Maybe (ModedModality sys v)
    {-^ The modality by which the application depends on the function (likely to be inferred.) -} ->
  Term sys v ->
  ModedModality sys v ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including app). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
apply gamma eliminee piBinding maybeDmuArg arg dmuInfer eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dImmedResult = elimineeMode gamma eliminators
  let dmuPi = _modalityTo'mod $ _segment'modty $ binding'segment $ piBinding
  dmuArg <- case maybeDmuArg of
    Nothing -> return $ _modalityTo'mod $ _segment'modty $ binding'segment $ piBinding
    Just dmuArg -> dmuArg <$ do
      addNewConstraint
        (Jud analyzableToken
          (crispModalityTo dgamma' :\\ gamma)
          dmuArg
          U1
          (ClassifMustBe $ _modality'dom dmuPi :*: _modality'cod dmuPi)
        )
        "Applying function: Checking modality annotation on argument."
      addNewConstraint
        (JudRel analyzableToken (Eta True) (Const ModEq)
          (crispModalityTo dgamma' :\\ duplicateCtx gamma)
          (Twice1
            dmuArg
            dmuPi
          )
          (Twice1 U1 U1)
          (ClassifWillBe $ (\x -> Twice1 x x) $ _modality'dom dmuPi :*: _modality'cod dmuPi)
        )
        "Applying function: Checking whether modality annotation on argument matches the one from the type."
  -- dmuInfer should be the identity.
  addNewConstraint
    (Jud analyzableToken
      (crispModalityTo dgamma' :\\ gamma)
      dmuInfer
      U1
      (ClassifMustBe $ dImmedResult :*: dImmedResult)
    )
    "Applying function: Checking elimination modality."
  addNewConstraint
    (JudRel analyzableToken (Eta True) (Const ModEq)
      (crispModalityTo dgamma' :\\ duplicateCtx gamma)
      (Twice1
        (idModedModality $ dImmedResult)
        (dmuInfer)
      )
      (Twice1 U1 U1)
      (ClassifWillBe $ Twice1
        (dImmedResult :*: dImmedResult)
        (dImmedResult :*: dImmedResult)
      )
    )
    "Applying function: Checking whether actual elimination modality equals expected modality (namely identity)."
  {- The argument will be checked when checking the result of the smart elimination.
     However, the argument determines the type of the application, which in turn determines the
     elaboration of the smart elimination. Hence, to avoid deadlock, we need to check it now as well.
  -}
  let tyArg = _decl'content $ binding'segment $ piBinding
  let argChecked = Expr2 $ TermAlreadyChecked arg tyArg
  addNewConstraint
    (JudTerm
      (VarFromCtx <$> withDom dmuArg :\\ VarFromCtx <$> withDom dmuElimTotal :\\ gamma)
      arg
      (_decl'content $ binding'segment $ piBinding)
    )
    "Applying function: checking argument."
  addNewConstraint
    (JudSmartElim
      gamma
      (Expr2 $ TermElim
        (idModalityTo $ unVarFromCtx <$> ctx'mode gamma)
        eliminee
        (Pi piBinding)
        (App argChecked)
      )
      (substLast2 arg $ binding'body piBinding)
      eliminators
      result
      tyResult
    )
    "Applying function: checking further elimination."

insertImplicitArgument :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Type sys v ->
  ModedModality sys v {-^ The modality by which the application depends on the function (likely to be inferred.) -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] {-^ The remaining eliminators (not including app). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
insertImplicitArgument gamma eliminee piBinding dmuInfer eliminators result tyResult = do
  let dgamma :: Mode sys v = unVarFromCtx <$> ctx'mode gamma
  let dmuArg = _segment'modty $ binding'segment $ piBinding
  let dmuElimTotal = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let tyArg = _segment'content $ binding'segment $ piBinding
  arg <- newMetaTermNoCheck (VarFromCtx <$> dmuArg :\\ VarFromCtx <$> withDom dmuElimTotal :\\ gamma)
           {-tyArg-} MetaBlocked Nothing "Inferring implicit argument."
  apply gamma eliminee piBinding Nothing arg dmuInfer eliminators result tyResult

elimineeMode ::
  (SysTC sys, Multimode sys, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  [(ModedModality sys :*: SmartEliminator sys) v] ->
  Mode sys v
elimineeMode gamma eliminators = case eliminators of
            [] -> unVarFromCtx <$> ctx'mode gamma
            ((:*:) dmu2 _ : _) -> _modality'dom dmu2

popModality :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  [(ModedModality sys :*: SmartEliminator sys) v] ->
  Term sys v ->
  Type sys v ->
  tc (ModedModality sys v, [(ModedModality sys :*: SmartEliminator sys) v])
popModality gamma eliminee tyEliminee eliminators result tyResult =
  case eliminators of
    [] -> unreachable
    ((:*:) dmuSplittee elim1 : eliminators') -> do
      let dgamma' = ctx'mode gamma
      let ModedModality domSplittee codSplittee muSplittee = dmuSplittee
      --let domElimTail = elimineeMode gamma eliminators'
      {-midSplittee <- newMetaModeNoCheck (crispModalityTo dgamma' :\\ gamma)
               "Inferring output mode of next implicit elimination."-}
      muPoppee <- newMetaModtyNoCheck (crispModalityTo dgamma' :\\ gamma)
                "Inferring modality of next implicit elimination."
      muRemaining <- newMetaModtyNoCheck (crispModalityTo dgamma' :\\ gamma) $
        "Inferring composite of the modalities of all eliminations as of (not including) the next implicit one, " ++
        "until (and including) the next explicit one."
      let dmuPoppee = muPoppee --ModedModality domSplittee midSplittee muPoppee
      let dmuRemaining = muRemaining --ModedModality midSplittee codSplittee muLeft
      addNewConstraint
        (Jud (analyzableToken)
          (crispModalityTo dgamma' :\\ gamma)
          dmuSplittee
          U1
          (ClassifMustBe $ _modality'dom dmuPoppee :*: _modality'cod dmuRemaining)
        )
        "Type-checking modality of next smart elimination, which I will need to split."
      addNewConstraint
        (JudRel (analyzableToken @sys @(Modality sys)) (Eta True) (Const ModEq)
          (crispModalityTo dgamma' :\\ duplicateCtx gamma)
          (Twice1
            (_modality'mod $ compModedModality dmuRemaining dmuPoppee)
            (muSplittee)
          )
          (Twice1 U1 U1)
          (ClassifMustBe $ (\x -> Twice1 x x) $ _modality'dom dmuPoppee :*: _modality'cod dmuRemaining)
        )
        "Splitting modality."
      return (dmuPoppee, (dmuRemaining :*: elim1) : eliminators')

{-| Tries to apply an implicit elimination to the eliminee.
    If successful, creates a new constraint with the once eliminated eliminee and the same eliminators.
    If unsuccesful, calls the alternative if present, or throws a @'tcFail'@.
-}
autoEliminate ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  [(ModedModality sys :*: SmartEliminator sys) v] ->
  Term sys v ->
  Type sys v ->
  Maybe (tc ()) ->
  tc ()
autoEliminate gamma eliminee tyEliminee eliminators result tyResult maybeAlternative = do
  let alternative = case maybeAlternative of
           Nothing -> tcFail $ "Cannot auto-eliminate."
           Just alternative' -> alternative'
  case tyEliminee of
    Type (Expr2 (TermCons (ConsUniHS (Pi piBinding)))) ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> alternative
        Implicit -> do
          (dmuInfer, eliminators') <- popModality gamma eliminee tyEliminee eliminators result tyResult
          insertImplicitArgument gamma eliminee piBinding dmuInfer eliminators' result tyResult
        Resolves _ -> todo
    Type (Expr2 (TermCons (ConsUniHS (BoxType boxSeg)))) -> do
      (dmuInfer, eliminators') <- popModality gamma eliminee tyEliminee eliminators result tyResult
      unbox gamma eliminee boxSeg dmuInfer eliminators' result tyResult
    _ -> alternative

checkSmartElimForNormalType ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  [(ModedModality sys :*: SmartEliminator sys) v] ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElimForNormalType gamma eliminee tyEliminee eliminators result tyResult = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  case (tyEliminee, eliminators) of
    -- No eliminators: Check that it's done. (Previously claimed to be unreachable, but I don't see why.)
    (_, []) ->
      --unreachable
      checkSmartElimDone gamma eliminee tyEliminee Nothing result tyResult
    -- Silently eliminate further: `t ...` (Auto-eliminate, if not possible, assert that it's done.)
    (_, (:*:) muElim SmartElimDots : []) ->
      autoEliminate gamma eliminee tyEliminee eliminators result tyResult $
      Just $ checkSmartElimDone gamma eliminee tyEliminee (Just muElim) result tyResult
    -- Bogus: `t ... e` (Throw error.)
    (_, (:*:) _ SmartElimDots : _) -> tcFail $ "Bogus elimination: `...` is not the last eliminator."
    -- Explicit application of a function: `f arg` (Apply if explicit, auto-eliminate otherwise.)
    (TypeHS (Pi piBinding),
     (:*:) dmuInfer (SmartElimArg Raw.ArgSpecExplicit dmuArg arg) : eliminators') ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> apply gamma eliminee piBinding (Just dmuArg) arg dmuInfer eliminators' result tyResult
        _ -> autoEliminate gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Immediate application of a function: `f .{arg}` (Apply.)
    (TypeHS (Pi piBinding),
     (:*:) dmuInfer (SmartElimArg Raw.ArgSpecNext dmuArg arg) : eliminators') ->
      apply gamma eliminee piBinding (Just dmuArg) arg dmuInfer eliminators' result tyResult
    -- Named application of a function: `f .{a = arg}` (Apply if the name matches, auto-eliminate otherwise.)
    (TypeHS (Pi piBinding),
     (:*:) dmuInfer (SmartElimArg (Raw.ArgSpecNamed name) dmuArg arg) : eliminators') ->
      if Just name == (_segment'name $ binding'segment $ piBinding)
      then apply gamma eliminee piBinding (Just dmuArg) arg dmuInfer eliminators' result tyResult
      else autoEliminate gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Application of a non-function: `t arg`, `t .{arg}`, `t .{a = arg}` (Auto-eliminate.)
    (_, (:*:) _ (SmartElimArg _ _ _) : eliminators') ->
      autoEliminate gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Named projection of a pair: `pair .componentName`
    (TypeHS (Sigma sigmaBinding),
     (:*:) dmuInfer (SmartElimProj (Raw.ProjSpecNamed name)) : eliminators') ->
      -- if the given name is the name of the first component
      if Just name == (_segment'name $ binding'segment $ sigmaBinding)
      -- then project out the first component and continue
      then projFst gamma eliminee sigmaBinding dmuInfer eliminators' result tyResult
      -- else project out the second component and try again
      else
        let d = elimineeMode gamma eliminators
        in  projSnd gamma eliminee sigmaBinding (idModedModality d) eliminators result tyResult
    -- Numbered projection of a pair: `pair .i`
    (TypeHS (Sigma sigmaBinding),
     (:*:) dmuInfer (SmartElimProj (Raw.ProjSpecNumbered i)) : eliminators') ->
      if i == 1
      -- then project out the first component and continue
      then projFst gamma eliminee sigmaBinding dmuInfer eliminators' result tyResult
      -- else project out the second component and decrement
      else let decEliminators = (:*:) dmuInfer (SmartElimProj (Raw.ProjSpecNumbered $ i - 1)) : eliminators'
               d = _modality'dom dmuInfer
           in  projSnd gamma eliminee sigmaBinding (idModedModality d) decEliminators result tyResult
    -- Numbered tail projection of a pair: `pair ..i`
    (TypeHS (Sigma sigmaBinding),
     (:*:) dmuInfer (SmartElimProj (Raw.ProjSpecTail i)) : eliminators') ->
      if i == 1
      -- then do nothing
      then discard gamma eliminee tyEliminee dmuInfer eliminators' result tyResult
      -- else project out the second component and decrement
      else let decEliminators = (:*:) dmuInfer (SmartElimProj (Raw.ProjSpecTail $ i - 1)) : eliminators'
               d = _modality'dom dmuInfer
           in  projSnd gamma eliminee sigmaBinding (idModedModality d) decEliminators result tyResult
    -- Projection of a non-pair: auto-eliminate.
    (_, ((:*:) _ (SmartElimProj _)) : _) ->
      autoEliminate gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Unboxing of a boxed value: `boxed .{}`
    (TypeHS (BoxType boxSeg),
     (:*:) dmuInfer SmartElimUnbox : eliminators') ->
      unbox gamma eliminee boxSeg dmuInfer eliminators' result tyResult
    -- Unboxing of a non-box: auto-eliminate.
    (_, (:*:) _ SmartElimUnbox : _) ->
      autoEliminate gamma eliminee tyEliminee eliminators result tyResult Nothing

checkSmartElim :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
  [(ModedModality sys :*: SmartEliminator sys) v] ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElim gamma eliminee tyEliminee [] result tyResult =
  checkSmartElimDone gamma eliminee tyEliminee Nothing result tyResult
checkSmartElim gamma eliminee tyEliminee eliminators result tyResult = do
  let dgamma :: Mode sys v = unVarFromCtx <$> ctx'mode gamma
  let dmuElimTotal :: ModedModality sys v = concatModedModalityDiagrammatically (fst1 <$> eliminators) dgamma
  let dEliminee = _modality'dom dmuElimTotal
  (whnTyEliminee, metasTyEliminee) <-
    runWriterT $ whnormalizeType
      (VarFromCtx <$> withDom dmuElimTotal :\\ gamma)
      tyEliminee
      "Weak-head-normalizing type of eliminee."
  case metasTyEliminee of
    -- the type weak-head-normalizes
    [] -> do
      parent' <- defConstraint
                   (JudSmartElim gamma eliminee whnTyEliminee eliminators result tyResult)
                   "Weak-head-normalize type of eliminee."
      withParent parent' $ checkSmartElimForNormalType gamma eliminee whnTyEliminee eliminators result tyResult
    -- the type does not weak-head-normalize
    _ -> tcBlock "Need to know type in order to make sense of smart-elimination."

