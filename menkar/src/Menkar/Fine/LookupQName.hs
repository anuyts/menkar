module Menkar.Fine.LookupQName where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.System.Fine
import qualified Menkar.Raw.Syntax as Raw

import Data.Bifunctor
import Data.Maybe
import Control.Lens
import Data.Functor.Identity
import Control.Exception.AssertFalse
import Data.Void
import Data.Kind hiding (Type)

-- TODOMOD means todo for modalities

----------------------------

telescoped2lambda :: Telescoped Type ValRHS sys v -> Term sys v
telescoped2lambda (Telescoped valRHS) = _val'term valRHS
telescoped2lambda (seg :|- telescopedValRHS) = Expr2 $ TermCons $ Lam $ Binding seg (telescoped2lambda telescopedValRHS)
telescoped2lambda (dmu :** telescopedValRHS) = Expr2 $ TermCons $ ConsBox
  (Declaration (DeclNameSegment Nothing) dmu Explicit (Type $ telescoped2pi telescopedValRHS))
  (telescoped2lambda telescopedValRHS)

telescoped2pi :: Telescoped Type ValRHS sys v -> Term sys v
telescoped2pi (Telescoped valRHS) = case _val'type valRHS of Type ty -> ty
telescoped2pi (seg :|- telescopedValRHS) = Expr2 $ TermCons $ ConsUniHS $ Pi $ Binding seg (telescoped2pi telescopedValRHS)
telescoped2pi (dmu :** telescopedValRHS) = Expr2 $ TermCons $ ConsUniHS $ BoxType $
  Declaration (DeclNameSegment Nothing) dmu Explicit (Type $ telescoped2pi telescopedValRHS)

telescoped2quantified :: (SysTrav sys) =>
  Telescoped Type ValRHS sys v -> ValRHS sys v
telescoped2quantified telescopedVal = ValRHS
  (telescoped2lambda $ telescopedVal)
  (Type $ telescoped2pi $ telescopedVal)

telescoped2modalQuantified :: (Multimode sys) =>
  Mode sys v {-^ Mode of the telescope -} -> Telescoped Type ValRHS sys v -> ModApplied ValRHS sys v
telescoped2modalQuantified d1 (d2mu@(ModedModality d2 mu) :** telescopedVal) =
  let ModApplied d3mu' val = telescoped2modalQuantified d2 telescopedVal
  in  ModApplied (compModedModality d2mu d3mu') val
telescoped2modalQuantified d telescopedVal = ModApplied (idModedModality d) (telescoped2quantified telescopedVal)

----------------------------

{-
lookupQNameEntryList :: (Functor mode, Functor modty) =>
  [Entry sys v] -> Raw.QName -> Maybe (Term sys v, Type sys v, ModedModality sys v)
lookupQNameEntryList [] qname = Nothing
lookupQNameEntryList (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ runIdentity $
                                                mapTelescopedSimple (
                                                  \ wkn valRHS -> Identity $
                                                                  (telescoped2lambda $ _val'term $ _decl'content valRHS,
                                                                   Type $ telescoped2pi $ _val'type $ _decl'content valRHS,
                                                                   _decl'modty valRHS)
                                                ) val
  | otherwise = lookupQNameEntryList entries qname
lookupQNameEntryList (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryList entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then telescoped2lambda <$> mapTelescopedSimple (
        \ wkn declModule -> lookupQNameModule (_decl'content declModule) (Raw.Qualified qual name))
      modul
    else lookupQNameEntryList entries qname
-}

----------------------------

{-
lookupQNameEntryListTerm :: (Functor mode, Functor modty) =>
  [Entry sys v] -> Raw.QName -> Maybe (Term sys v)
lookupQNameEntryListTerm [] qname = Nothing
lookupQNameEntryListTerm (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ telescoped2lambda $ runIdentity $
                                                mapTelescopedSimple (
                                                  \ wkn -> Identity . _val'term . _decl'content
                                                ) val
  | otherwise = lookupQNameEntryListTerm entries qname
lookupQNameEntryListTerm (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryListTerm entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then telescoped2lambda <$> mapTelescopedSimple (
        \ wkn declModule -> lookupQNameModuleTerm (_decl'content declModule) (Raw.Qualified qual name))
      modul
    else lookupQNameEntryListTerm entries qname

lookupQNameModuleTerm :: (Functor mode, Functor modty) =>
  ModuleRHS sys v -> Raw.QName -> Maybe (Term sys v)
lookupQNameModuleTerm modul qname =
  lookupQNameEntryListTerm (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQNameTerm :: (Functor mode, Functor modty, Functor (ty sys)) =>
  Ctx ty sys v w -> Raw.QName -> Maybe (Term sys (VarOpenCtx v w))
lookupQNameTerm CtxEmpty qname = Nothing
lookupQNameTerm (gamma :.. seg) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQNameTerm gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ Var3 $ VarFromCtx VarLast
                                else wkn $ lookupQNameTerm gamma qname
    _ -> wkn $ lookupQNameTerm gamma qname
  where wkn = fmap (fmap (bimap VarWkn id))
lookupQNameTerm (seg :^^ gamma) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQNameTerm gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ Var3 $ VarFromCtx VarFirst
                                else wkn $ lookupQNameTerm gamma qname
    _ -> wkn $ lookupQNameTerm gamma qname
  where wkn = fmap (fmap wkn')
        wkn' u = case u of
           VarBeforeCtx (VarWkn w) -> VarBeforeCtx w
           VarBeforeCtx VarLast -> VarFromCtx $ VarFirst
           VarFromCtx v -> VarFromCtx $ VarLeftWkn v
           _ -> unreachable
lookupQNameTerm (gamma :<...> modul) qname = case lookupQNameModuleTerm modul qname of
  Just t -> wkn $ Just t
  Nothing -> wkn $ lookupQNameTerm gamma qname
  where wkn = fmap (fmap (bimap VarInModule id))
lookupQNameTerm (dkappa :\\ gamma) qname = lookupQNameTerm gamma qname
-}

---------------------------------

{-
lookupQNameEntryListType :: (Functor mode, Functor modty) =>
  [Entry sys v] -> Raw.QName -> Maybe (Type sys v)
lookupQNameEntryListType [] qname = Nothing
lookupQNameEntryListType (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ Type . telescoped2pi $ runIdentity $
                                                mapTelescopedSimple (
                                                  \ wkn -> Identity . _val'type . _decl'content
                                                ) val
  | otherwise = lookupQNameEntryListType entries qname
lookupQNameEntryListType (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryListType entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then Type . telescoped2pi <$> mapTelescopedSimple (
        \ wkn declModule -> lookupQNameModuleType (_decl'content declModule) (Raw.Qualified qual name))
      modul
    else lookupQNameEntryListType entries qname

lookupQNameModuleType :: (Functor mode, Functor modty) =>
  ModuleRHS sys v -> Raw.QName -> Maybe (Type sys v)
lookupQNameModuleType modul qname =
  lookupQNameEntryListType (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQNameType :: (Functor mode, Functor modty) =>
  Ctx Type sys v w -> Raw.QName -> Maybe (Type sys (VarOpenCtx v w))
lookupQNameType CtxEmpty qname = Nothing
lookupQNameType (gamma :.. seg) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQNameType gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then wkn $ Just $ _segment'content seg
                                else wkn $ lookupQNameType gamma qname
    _ -> wkn $ lookupQNameType gamma qname
  where wkn = fmap (fmap (bimap VarWkn id))
lookupQNameType (seg :^^ gamma) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQNameType gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ VarBeforeCtx <$> _segment'content seg
                                else wkn $ lookupQNameType gamma qname
    _ -> wkn $ lookupQNameType gamma qname
  where wkn = fmap (fmap wkn')
        wkn' u = case u of
           VarBeforeCtx (VarWkn w) -> VarBeforeCtx w
           VarBeforeCtx VarLast -> VarFromCtx $ VarFirst
           VarFromCtx v -> VarFromCtx $ VarLeftWkn v
           _ -> unreachable
lookupQNameType (gamma :<...> modul) qname = case lookupQNameModuleType modul qname of
  Just t -> wkn $ Just t
  Nothing -> wkn $ lookupQNameType gamma qname
  where wkn = fmap (fmap (bimap VarInModule id))
lookupQNameType (dkappa :\\ gamma) qname = lookupQNameType gamma qname
-}

----------------------------

lookupQNameEntryList :: (SysTrav sys) =>
  [Entry sys v] -> Raw.QName -> Maybe (Telescoped Type ValRHS sys v)
lookupQNameEntryList [] qname = Nothing
lookupQNameEntryList (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ _decl'modty val :** _decl'content val
  | otherwise = lookupQNameEntryList entries qname
lookupQNameEntryList (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryList entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then fmap ((_decl'modty modul :**) . joinTelescoped) $ mapTelescopedSimple (
        \ wkn moduleRHS -> lookupQNameModule moduleRHS qname
      ) $ _decl'content modul
    else lookupQNameEntryList entries qname
    
lookupQNameModule :: (SysTrav sys) =>
  ModuleRHS sys v -> Raw.QName -> Maybe (Telescoped Type ValRHS sys v)
lookupQNameModule modul qname =
  lookupQNameEntryList (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQName :: (Multimode sys) =>
  Ctx Type sys v w -> Raw.QName -> LookupResult sys (VarOpenCtx v w)
lookupQName (CtxEmpty _) qname = LookupResultNothing
lookupQName (gamma :.. seg) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then LookupResultVar (VarFromCtx VarLast)
                                     {-Just $ LeftDivided d (ModedModality d (idMod d)) $
                                     (wkn $ _segment'modty seg)
                                     :** Telescoped (ValRHS (Var3 $ VarFromCtx $ VarLast) (wkn $ _segment'content seg))-}
                                else wkn $ lookupQName gamma qname
    _ -> wkn $ lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' w') -> f (VarOpenCtx (VarExt v') w')
        wkn = fmap (bimap VarWkn id)
        d = ctx'mode $ gamma :.. seg
lookupQName (seg :^^ gamma) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then LookupResultVar (VarFromCtx VarFirst)
                                     {-Just $ LeftDivided d (ModedModality d (idMod d)) $
                                     (VarBeforeCtx <$> _segment'modty seg)
                                     :** Telescoped
                                       (ValRHS (Var3 $ VarFromCtx $ VarFirst) (VarBeforeCtx <$> _segment'content seg))
                                     -}
                                else wkn $ lookupQName gamma qname
    _ -> wkn $ lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' (VarExt w')) -> f (VarOpenCtx (VarLeftExt v') w')
        wkn = fmap varLeftEat
        d = ctx'mode $ seg :^^ gamma
lookupQName (gamma :<...> modul) qname = case lookupQNameModule modul qname of
  Just t -> LookupResultVal $ LeftDivided
                     d (ModedModality d (idMod d))
                     (wkn t)
  Nothing -> wkn $ lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' w) -> f (VarOpenCtx (VarInModule v') w)
        wkn = fmap (bimap VarInModule id)
        d = ctx'mode $ gamma :<...> modul
lookupQName (dmu :\\ gamma) qname = case lookupQName gamma qname of
  LookupResultVar v -> LookupResultVar v
  LookupResultNothing -> LookupResultNothing
  LookupResultVal (LeftDivided dOrig dmu' seg) ->
    let d = modality'dom dmu
        mu = modality'mod dmu
        d' = modality'dom dmu'
        mu' = modality'mod dmu'
    in LookupResultVal $ LeftDivided dOrig (ModedModality d (compMod mu' d' mu)) seg

------------------------

{-
lookupQNameTerm :: (Multimode sys, Functor (Type sys)) =>
  Ctx Type sys v w -> Raw.QName -> Maybe (LeftDivided (Telescoped Type Term) sys (VarOpenCtx v w))
lookupQNameTerm gamma qname =
  over leftDivided'content
    (runIdentity . mapTelescopedSimple (\wkn val -> Identity $ _val'term val))
  <$> lookupQName gamma qname
-}
  --over leftDivided'content (_val'term . _modApplied'content . telescoped2modalQuantified) <$> lookupQName gamma qname

------------------------

{-
-- TODOMOD: you need to change output type to @LeftDivided Type sys (VarOpenCtx v w)@
lookupVarType :: (Functor mode, Functor modty) =>
  Ctx Type sys v w -> v -> Type sys (VarOpenCtx v w)
lookupVarType (CtxEmpty _) v = absurd v
lookupVarType (gamma :.. seg) (VarLast) = bimap VarWkn id <$> _segment'content seg
lookupVarType (gamma :.. seg) (VarWkn v) = bimap VarWkn id <$> lookupVarType gamma v
lookupVarType (gamma :.. seg) _ = unreachable
lookupVarType (seg :^^ gamma) (VarFirst) = VarBeforeCtx <$> _segment'content seg
lookupVarType (seg :^^ gamma) (VarLeftWkn v) = wkn <$> lookupVarType gamma v
  where wkn (VarFromCtx v) = VarFromCtx (VarLeftWkn v)
        wkn (VarBeforeCtx (VarWkn v)) = VarBeforeCtx v
        wkn (VarBeforeCtx VarLast) = VarFromCtx VarFirst
        wkn _ = unreachable
lookupVarType (gamma :<...> modul) (VarInModule v) = bimap VarInModule id <$> lookupVarType gamma v
lookupVarType (dkappa :\\ gamma) v = lookupVarType gamma v
lookupVarType gamma v = unreachable
-}

lookupVar :: (Multimode sys) =>
  Ctx Type sys v w -> v -> LeftDivided (Segment Type) sys (VarOpenCtx v w)
lookupVar (CtxEmpty d) v = absurd v
lookupVar (gamma :.. seg) (VarLast) = LeftDivided d (ModedModality d (idMod d)) $ bimap VarWkn id <$> seg
  where d = ctx'mode (gamma :.. seg)
lookupVar (gamma :.. seg) (VarWkn v) = bimap VarWkn id <$> lookupVar gamma v
lookupVar (seg :^^ gamma) (VarFirst) = LeftDivided d (ModedModality d (idMod d)) $ VarBeforeCtx <$> seg
  where d = ctx'mode (seg :^^ gamma)
lookupVar (seg :^^ gamma) (VarLeftWkn v) = varLeftEat <$> lookupVar gamma v
lookupVar (gamma :<...> modul) (VarInModule v) = bimap VarInModule id <$> lookupVar gamma v
lookupVar (dmu :\\ gamma) v = LeftDivided dOrig (ModedModality d (compMod mu' d' mu)) seg
  where LeftDivided dOrig dmu' seg = lookupVar gamma v
        d = modality'dom dmu
        mu = modality'mod dmu
        d' = modality'dom dmu'
        mu' = modality'mod dmu'
