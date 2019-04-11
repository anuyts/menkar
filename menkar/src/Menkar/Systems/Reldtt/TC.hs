module Menkar.Systems.Reldtt.TC where

import Menkar.Basic
import Menkar.WHN
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Scoper
import Menkar.Systems.Reldtt.WHN
import Menkar.TC.Solve

import Control.Exception.AssertFalse

import Data.Void
import Data.Functor.Compose
import Control.Lens
import GHC.Generics
import Control.Monad.Writer.Lazy

{-| Returns the codomain and domain IN THAT ORDER.
-}
checkKnownModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  KnownModty v ->
  tc (Term Reldtt v, Term Reldtt v)
checkKnownModty parent gamma kmu@(KnownModty snout tail) = do
  case tail of
    TailEmpty -> return ()
    TailDisc dcod -> do
      addNewConstraint
        (JudTerm gamma dcod (BareSysType SysTypeMode))
        (Just parent)
        "Checking codomain of modality tail."
    TailForget ddom -> do
      addNewConstraint
        (JudTerm gamma ddom (BareSysType SysTypeMode))
        (Just parent)
        "Checking domain of modality tail."
    TailDiscForget ddom dcod -> do
      addNewConstraint
        (JudTerm gamma ddom (BareSysType SysTypeMode))
        (Just parent)
        "Checking domain of modality tail."
      addNewConstraint
        (JudTerm gamma dcod (BareSysType SysTypeMode))
        (Just parent)
        "Checking codomain of modality tail."
    TailCont d ->
      addNewConstraint
        (JudTerm gamma d (BareSysType SysTypeMode))
        (Just parent)
        "Checking (co)domain of modality tail."
    TailProblem -> tcFail parent "Erroneous tail."
  return (_knownModty'cod kmu, _knownModty'dom kmu)

{-| Returns the codomain and domain IN THAT ORDER.
-}
checkChainModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ChainModty v ->
  tc (Term Reldtt v, Term Reldtt v)
checkChainModty parent gamma chainMu@(ChainModtyKnown kmu) =
  checkKnownModty parent gamma kmu
checkChainModty parent gamma chainMu@(ChainModtyLink kmu termNu chainRho) = do
  (dcod, d2) <- checkKnownModty parent gamma kmu
  (d1, ddom) <- checkChainModty parent gamma chainRho
  addNewConstraint
    (JudTerm gamma termNu (BareSysType $ SysTypeModty d1 d2))
    (Just parent)
    "Type-checking a constituent modality"
  return (dcod, ddom)
checkChainModty parent gamma chainMu@(ChainModtyMeta ddom dcod meta depcies) = do
  maybeSolution <- awaitMeta parent "I want to know what I'm supposed to type-check." meta $ getCompose depcies
  chainMu <- case maybeSolution of
    Nothing -> tcBlock parent "I want to know what I'm supposed to type-check."
    Just solution -> case solution of
      Expr2 (TermSys (SysTermChainModtyInDisguise chainMu')) -> return chainMu'
      _ -> unreachable
  childConstraint <- defConstraint
    (JudModality gamma chainMu ddom dcod)
    (Just parent)
    "Look up meta."
  checkChainModtyAgainstModes childConstraint gamma chainMu ddom dcod
  return (dcod, ddom)
-- TODO ADD/USE A JUDGEMENT

checkChainModtyAgainstModes :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ChainModty v ->
  Term Reldtt v ->
  Term Reldtt v ->
  tc ()
checkChainModtyAgainstModes parent gamma chainMu ddomExp dcodExp = do
  (dcodAct, ddomAct) <- checkChainModty parent gamma chainMu
  addNewConstraint
    (JudTermRel (Eta True) eqDeg
      (duplicateCtx gamma)
      (Twice2 ddomAct ddomExp)
      (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
    )
    (Just parent)
    "Checking whether actual domain equals expected domain."
  addNewConstraint
    (JudTermRel (Eta True) eqDeg
      (duplicateCtx gamma)
      (Twice2 dcodAct dcodExp)
      (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
    )
    (Just parent)
    "Checking whether actual codomain equals expected codomain."

{-
newRelatedChainModty :: forall tc v vOrig .
    (MonadTC Reldtt tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Constraint Reldtt ->
    Ctx Type Reldtt vOrig Void ->
    Ctx (Twice2 Type) Reldtt v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    ChainModty v ->
    (String -> tc ()) ->
    tc (Maybe (ChainModty vOrig))
newRelatedChainModty parent gammaOrig gamma subst partialInv chainMu2 alternative = _
-}

------------------------------------------------

checkKnownModtyRel :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  ModRel ->
  Ctx (Twice2 Type) Reldtt v Void ->
  KnownModty v ->
  KnownModty v ->
  tc ()
checkKnownModtyRel parent rel gamma kmu1 kmu2 = do
  addNewConstraint
    (JudTermRel (Eta True) eqDeg
      gamma
      (Twice2 (_knownModty'dom kmu1) (_knownModty'dom kmu2))
      (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
    )
    (Just parent)
    "Relating domains."
  addNewConstraint
    (JudTermRel (Eta True) eqDeg
      gamma
      (Twice2 (_knownModty'cod kmu1) (_knownModty'cod kmu2))
      (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
    )
    (Just parent)
    "Relating codomains."
  let maybeResult = relKnownModty rel kmu1 kmu2
  case maybeResult of
    Nothing -> tcFail parent "I need to relate modalities that are not of the same modes."
    Just False -> tcFail parent "False."
    Just True -> return ()

checkWHNChainModtyRel :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  ModRel ->
  Ctx (Twice2 Type) Reldtt v Void ->
  ChainModty v ->
  ChainModty v ->
  tc ()
checkWHNChainModtyRel parent rel gamma chmu1 chmu2 = do
  case (chmu1, chmu2) of
    (ChainModtyKnown kmu1,
     ChainModtyKnown kmu2) -> checkKnownModtyRel parent rel gamma kmu1 kmu2
      
    (ChainModtyKnown kmu1, _) -> tcFail parent "False."
    
    (ChainModtyLink knu1 termRho1 chainSigma1,
     ChainModtyLink knu2 termRho2 chainSigma2) -> do
      checkKnownModtyRel parent rel gamma knu1 knu2
      addNewConstraint
        (JudTermRel (Eta True)
          eqDeg -- Neutral modalities can only be comparable if they are equal.
          gamma
          (Twice2 termRho1 termRho2)
          (Twice2
            (BareSysType $ SysTypeModty (_chainModty'cod chainSigma1) (_knownModty'dom knu1))
            (BareSysType $ SysTypeModty (_chainModty'cod chainSigma2) (_knownModty'dom knu2))
          )
        )
        (Just parent)
        "Relating first neutral components."
      addNewConstraint
        (JudModalityRel rel
          gamma
          chainSigma1 chainSigma2
          (_chainModty'dom chainSigma1)
          (_chainModty'cod chainSigma1)
        )
        (Just parent)
        "Relating part after first neutral components."
      
    (ChainModtyLink knu1 termRho1 chainSigma1, _) -> tcFail parent "False."

    (ChainModtyMeta _ _ _ _, _) -> unreachable

tryToSolveChainModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  ModRel ->
  Ctx (Twice2 Type) Reldtt v Void ->
  ChainModty v {-^ Blocked -} ->
  ChainModty v ->
  tc ()
tryToSolveChainModty parent rel gamma chmu1 chmu2 = do
  case rel of
    ModLeq -> tcFail parent "Cannot solve inequality: one side is blocked on a meta-variable."
    ModEq -> return ()
  _tryToSolveChainModty

checkChainModtyRel :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  ModRel ->
  Ctx (Twice2 Type) Reldtt v Void ->
  ChainModty v ->
  ChainModty v ->
  tc ()
checkChainModtyRel parent rel gamma chmu1 chmu2 = do
  (chmu1, metasMu1) <- runWriterT $ whnormalizeChainModty parent (fstCtx gamma) chmu1 "Weak-head-normalizing first modality."
  (chmu2, metasMu2) <- runWriterT $ whnormalizeChainModty parent (sndCtx gamma) chmu2 "Weak-head-normalizing second modality."
  case (metasMu1, metasMu2) of
    ([], []) -> checkWHNChainModtyRel parent rel gamma chmu1 chmu2
    (_ , []) -> tryToSolveChainModty parent rel          gamma  chmu1 chmu2
    ([], _ ) -> tryToSolveChainModty parent rel (flipCtx gamma) chmu2 chmu1
    (_ , _ ) -> tcBlock parent "Cannot solve relation: both sides are blocked on a meta-variable."

------------------------------------------------

instance SysTC Reldtt where

  ---------------------------------------------------------
  
  checkTermSys parent gamma t ty = case t of
    
    SysTermMode d -> do
      addNewConstraint
        (JudTypeRel
          eqDeg
          (duplicateCtx gamma)
          (Twice2 (BareSysType SysTypeMode) ty)
        )
        (Just parent)
        "Checking that actual type equals expected type."
      case d of
        ModeTermZero -> return ()
        ModeTermSuc d -> do
          addNewConstraint
            (JudTerm gamma d (BareSysType SysTypeMode))
            (Just parent)
            "Checking argument."
        ModeTermOmega -> return ()
      
    SysTermModty mu -> do
      -- check contents and extract (co)domain
      (dcod, ddom) <- case mu of
        ModtyTermChain chmu -> do
          childConstraint <- defConstraint
            (JudModality gamma chmu (Expr2 TermWildcard) (Expr2 TermWildcard))
            (Just parent)
            "Checking underlying modality."
          checkChainModty childConstraint gamma chmu
        ModtyTermDiv rho nu -> unreachable -- only for prettyprinting
        ModtyTermApproxLeftAdjointProj ddom dcod nu -> do
          addNewConstraint
            (JudTerm gamma ddom (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking domain."
          addNewConstraint
            (JudTerm gamma dcod (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking codomain."
          addNewConstraint
            (JudTerm gamma nu (BareSysType $ SysTypeModty dcod ddom))
            (Just parent)
            "Checking argument modality."
          return (dcod, ddom)
        ModtyTermUnavailable ddom dcod -> unreachable -- only for prettyprinting
          {-do
          addNewConstraint
            (JudTerm gamma ddom (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking domain."
          addNewConstraint
            (JudTerm gamma dcod (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking codomain."
          return (ddom, dcod)-}
      addNewConstraint
        (JudTypeRel
          eqDeg
          (duplicateCtx gamma)
          (Twice2 (BareSysType $ SysTypeModty ddom dcod) ty)
        )
        (Just parent)
        "Checking that actual type equals expected type."

    SysTermChainModtyInDisguise _ -> unreachable

  ---------------------------------------------------------

  -- NO ETA --
  newRelatedSysTerm parent ddeg gammaOrig gamma subst partialInv t2 ty1 ty2 alternative = do

    case t2 of

      SysTermMode d2 -> do
        case d2 of
          ModeTermZero -> return $ Just $ BareMode $ ModeTermZero
          ModeTermSuc dpred2 -> do
            dpred1orig <- newRelatedMetaTerm parent (Eta True) ddeg gammaOrig gamma subst partialInv dpred2
                            (BareSysType SysTypeMode) (BareSysType SysTypeMode) MetaBlocked "Inferring predecessor."
            return $ Just $ BareMode $ ModeTermSuc dpred1orig
          ModeTermOmega -> return $ Just $ BareMode $ ModeTermOmega

      SysTermModty mu2 -> do
        case mu2 of
          ModtyTermChain chmu2 -> do
              chmu1orig <- newMetaModtyNoCheck (Just parent) gammaOrig "Inferring underlying modality."
              let chmu1 = subst <$> chmu1orig
              let dom1 = _chainModty'dom chmu1
              let cod1 = _chainModty'cod chmu1
              addNewConstraint
                (JudModalityRel ModEq gamma chmu1 chmu2 dom1 cod1)
                (Just parent)
                "Inferring underlying modality."
              return $ Just $ BareChainModty chmu1orig
          ModtyTermDiv rho2 nu2 -> unreachable
          ModtyTermApproxLeftAdjointProj ddom2 dcod2 nu2 -> do
            ddom1orig <- newRelatedMetaTerm parent (Eta True) ddeg gammaOrig gamma subst partialInv ddom2
                           (BareSysType SysTypeMode) (BareSysType SysTypeMode) MetaBlocked
                           "Inferring domain of left adjoint."
            let ddom1 = subst <$> ddom1orig
            dcod1orig <- newRelatedMetaTerm parent (Eta True) ddeg gammaOrig gamma subst partialInv dcod2
                           (BareSysType SysTypeMode) (BareSysType SysTypeMode) MetaBlocked
                           "Inferring codomain of left adjoint."
            let dcod1 = subst <$> dcod1orig
            nu1orig <- newRelatedMetaTerm parent (Eta True) ddeg gammaOrig gamma subst partialInv nu2
                           (BareSysType $ SysTypeModty dcod1 ddom1) (BareSysType $ SysTypeModty dcod2 ddom2) MetaBlocked
                           "Inferring original modality."
            return $ Just $ BareModty $ ModtyTermApproxLeftAdjointProj ddom1orig dcod1orig nu1orig
          ModtyTermUnavailable ddom2 dcod2 -> unreachable
          

      SysTermChainModtyInDisguise _ -> unreachable

  ---------------------------------------------------------

  checkTermRelSysTermWHNTermNoEta parent ddeg gamma syst1 t2 ty1 ty2 metasTy1 metasTy2 = do

    syst2 <- case t2 of
      (Expr2 (TermSys syst2)) -> return syst2
      _ -> tcFail parent "False."

    case (syst1, syst2) of

      (SysTermMode d1, SysTermMode d2) -> case (d1, d2) of
        (ModeTermZero, ModeTermZero) -> return ()
        (ModeTermSuc dpred1, ModeTermSuc dpred2) ->
          addNewConstraint
            (JudTermRel (Eta True) eqDeg
              gamma
              (Twice2 dpred1 dpred2)
              (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
            )
            (Just parent)
            "Relating predecessors"
        (ModeTermOmega, ModeTermOmega) -> return ()
        (_, _) -> tcFail parent "False."
        
      (SysTermMode d1, _) -> tcFail parent "False."

      (SysTermModty mu1, SysTermModty mu2) -> case (mu1, mu2) of
        
        (ModtyTermChain chmu1,
         ModtyTermChain chmu2) -> do
          parent <- defConstraint
            (JudModalityRel ModEq gamma chmu1 chmu2 (Expr2 TermWildcard) (Expr2 TermWildcard))
            (Just parent)
            "Relating underlying modalities."
          checkChainModtyRel parent ModEq gamma chmu1 chmu2
          
        (ModtyTermChain chmu1, _) -> tcFail parent "False."
        
        (ModtyTermDiv _ _, _) -> unreachable -- only for prettyprinting
        
        (ModtyTermApproxLeftAdjointProj ddom1 dcod1 nu1,
         ModtyTermApproxLeftAdjointProj ddom2 dcod2 nu2) -> do
          addNewConstraint
            (JudTermRel (Eta True) eqDeg
              gamma
              (Twice2 ddom1 ddom2)
              (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
            )
            (Just parent)
            "Relating domains."
          addNewConstraint
            (JudTermRel (Eta True) eqDeg
              gamma
              (Twice2 dcod1 dcod2)
              (Twice2 (BareSysType SysTypeMode) (BareSysType SysTypeMode))
            )
            (Just parent)
            "Relating codomains."
          addNewConstraint
            (JudTermRel (Eta True) eqDeg
              gamma
              (Twice2 nu1 nu2)
              (Twice2 (BareSysType $ SysTypeModty ddom1 dcod1) (BareSysType $ SysTypeModty ddom2 dcod2))
            )
            (Just parent)
            "Relating argument modalitiies."
          
        (ModtyTermApproxLeftAdjointProj ddom1 dcod1 nu1, _) -> tcFail parent "False."

        (ModtyTermUnavailable ddom1 dcod1, _) -> unreachable -- only for prettyprinting
        
      (SysTermModty mu1, _) -> tcFail parent "False."

      (SysTermChainModtyInDisguise _, _) -> unreachable

  ---------------------------------------------------------
