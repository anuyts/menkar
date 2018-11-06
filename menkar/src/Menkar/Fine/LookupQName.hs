module Menkar.Fine.LookupQName where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import Control.Lens
import Data.Functor.Identity
import Control.Exception.AssertFalse
import Data.Void

-- TODOMOD means todo for modalities

----------------------------

telescoped2lambda :: Telescoped Type ValRHS mode modty v -> Term mode modty v
telescoped2lambda (Telescoped valRHS) = _val'term valRHS
telescoped2lambda (seg :|- telescopedValRHS) = Expr3 $ TermCons $ Lam $ Binding seg (telescoped2lambda telescopedValRHS)
telescoped2lambda (dmu :** telescopedValRHS) = Expr3 $ TermCons $ ConsBox
  (Declaration (DeclNameSegment Nothing) dmu Explicit (Type $ telescoped2pi telescopedValRHS))
  (telescoped2lambda telescopedValRHS)

telescoped2pi :: Telescoped Type ValRHS mode modty v -> Term mode modty v
telescoped2pi (Telescoped valRHS) = case _val'type valRHS of Type ty -> ty
telescoped2pi (seg :|- telescopedValRHS) = Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding seg (telescoped2pi telescopedValRHS)
telescoped2pi (dmu :** telescopedValRHS) = Expr3 $ TermCons $ ConsUniHS $ BoxType $
  Declaration (DeclNameSegment Nothing) dmu Explicit (Type $ telescoped2pi telescopedValRHS)

telescoped2quantified :: (Functor mode, Functor modty) =>
  Telescoped Type ValRHS mode modty v -> ValRHS mode modty v
telescoped2quantified telescopedVal = ValRHS
  (telescoped2lambda $ telescopedVal)
  (Type $ telescoped2pi $ telescopedVal)

----------------------------

{-
lookupQNameEntryList :: (Functor mode, Functor modty) =>
  [Entry mode modty v] -> Raw.QName -> Maybe (Term mode modty v, Type mode modty v, ModedModality mode modty v)
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
  [Entry mode modty v] -> Raw.QName -> Maybe (Term mode modty v)
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
  ModuleRHS mode modty v -> Raw.QName -> Maybe (Term mode modty v)
lookupQNameModuleTerm modul qname =
  lookupQNameEntryListTerm (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQNameTerm :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Ctx ty mode modty v w -> Raw.QName -> Maybe (Term mode modty (VarOpenCtx v w))
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
  [Entry mode modty v] -> Raw.QName -> Maybe (Type mode modty v)
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
  ModuleRHS mode modty v -> Raw.QName -> Maybe (Type mode modty v)
lookupQNameModuleType modul qname =
  lookupQNameEntryListType (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQNameType :: (Functor mode, Functor modty) =>
  Ctx Type mode modty v w -> Raw.QName -> Maybe (Type mode modty (VarOpenCtx v w))
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

lookupQNameEntryList :: (Functor mode, Functor modty) =>
  [Entry mode modty v] -> Raw.QName -> Maybe (ValRHS mode modty v)
lookupQNameEntryList [] qname = Nothing
lookupQNameEntryList (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ telescoped2quantified $ _decl'modty val :** _decl'content val
  | otherwise = lookupQNameEntryList entries qname
lookupQNameEntryList (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryList entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then fmap (telescoped2quantified . (_decl'modty modul :**)) $ mapTelescopedSimple (
        \ wkn moduleRHS -> lookupQNameModule moduleRHS qname
      ) $ _decl'content modul
    else lookupQNameEntryList entries qname
lookupQNameModule :: (Functor mode, Functor modty) =>
  ModuleRHS mode modty v -> Raw.QName -> Maybe (ValRHS mode modty v)
lookupQNameModule modul qname =
  lookupQNameEntryList (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQName :: (Multimode mode modty) =>
  Ctx Type mode modty v w -> Raw.QName -> Maybe (LeftDivided ValRHS mode modty (VarOpenCtx v w))
lookupQName (CtxEmpty _) qname = Nothing
lookupQName (gamma :.. seg) qname = case _segment'name seg of
  Nothing -> wkn <$> lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ LeftDivided
                                     d (ModedModality d (idMod d))
                                     (ValRHS (Var3 $ VarFromCtx $ VarLast) (wkn $ _segment'content seg))
                                else wkn <$> lookupQName gamma qname
    _ -> wkn <$> lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' w') -> f (VarOpenCtx (VarExt v') w')
        wkn = fmap (bimap VarWkn id)
        d = ctx'mode $ gamma :.. seg
lookupQName (seg :^^ gamma) qname = case _segment'name seg of
  Nothing -> wkn <$> lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ LeftDivided
                                     d (ModedModality d (idMod d))
                                     (ValRHS (Var3 $ VarFromCtx $ VarFirst) (VarBeforeCtx <$> _segment'content seg))
                                else wkn <$> lookupQName gamma qname
    _ -> wkn <$> lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' (VarExt w')) -> f (VarOpenCtx (VarLeftExt v') w')
        wkn = fmap varLeftEat
        d = ctx'mode $ seg :^^ gamma
lookupQName (gamma :<...> modul) qname = case lookupQNameModule modul qname of
  Just t -> Just $ LeftDivided
                     d (ModedModality d (idMod d))
                     (wkn t)
  Nothing -> wkn <$> lookupQName gamma qname
  where wkn :: (Functor f) => f (VarOpenCtx v' w) -> f (VarOpenCtx (VarInModule v') w)
        wkn = fmap (bimap VarInModule id)
        d = ctx'mode $ gamma :<...> modul
lookupQName (dmu :\\ gamma) qname = case lookupQName gamma qname of
  Nothing -> Nothing
  Just (LeftDivided dOrig dmu' seg) ->
    let d = modality'dom dmu
        mu = modality'mod dmu
        d' = modality'dom dmu'
        mu' = modality'mod dmu'
    in Just $ LeftDivided dOrig (ModedModality d (compMod mu' d' mu)) seg

------------------------

lookupQNameTerm :: (Multimode mode modty, Functor (Type mode modty)) =>
  Ctx Type mode modty v w -> Raw.QName -> Maybe (LeftDivided Term mode modty (VarOpenCtx v w))
lookupQNameTerm gamma qname = over leftDivided'content _val'term <$> lookupQName gamma qname

------------------------

{-
-- TODOMOD: you need to change output type to @LeftDivided Type mode modty (VarOpenCtx v w)@
lookupVarType :: (Functor mode, Functor modty) =>
  Ctx Type mode modty v w -> v -> Type mode modty (VarOpenCtx v w)
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

lookupVar :: (Multimode mode modty) =>
  Ctx Type mode modty v w -> v -> LeftDivided (Segment Type) mode modty (VarOpenCtx v w)
lookupVar (CtxEmpty d) v = absurd v
lookupVar (gamma :.. seg) (VarLast) = LeftDivided d (ModedModality d (idMod d)) $ bimap VarWkn id <$> seg
  where d = ctx'mode (gamma :.. seg)
lookupVar (gamma :.. seg) (VarWkn v) = bimap VarWkn id <$> lookupVar gamma v
lookupVar (gamma :.. seg) _ = unreachable
lookupVar (seg :^^ gamma) (VarFirst) = LeftDivided d (ModedModality d (idMod d)) $ VarBeforeCtx <$> seg
  where d = ctx'mode (seg :^^ gamma)
lookupVar (seg :^^ gamma) (VarLeftWkn v) = varLeftEat <$> lookupVar gamma v
lookupVar (seg :^^ gamma) _ = unreachable
lookupVar (gamma :<...> modul) (VarInModule v) = bimap VarInModule id <$> lookupVar gamma v
lookupVar (dmu :\\ gamma) v = LeftDivided dOrig (ModedModality d (compMod mu' d' mu)) seg
  where LeftDivided dOrig dmu' seg = lookupVar gamma v
        d = modality'dom dmu
        mu = modality'mod dmu
        d' = modality'dom dmu'
        mu' = modality'mod dmu'