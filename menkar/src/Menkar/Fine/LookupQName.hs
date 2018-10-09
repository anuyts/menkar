module Menkar.Fine.LookupQName where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import Control.Lens
import Data.Functor.Identity

----------------------------

telescoped2lambda :: Telescoped Type Term mode modty v -> Term mode modty v
telescoped2lambda (Telescoped t) = t
telescoped2lambda (seg :|- telescopedTerm) = Expr3 $ TermCons $ Lam $ Binding seg (telescoped2lambda telescopedTerm)

----------------------------

lookupQNameEntryList :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Ctx ty mode modty v w -> [Entry mode modty (VarOpenCtx v w)] -> Raw.QName -> Maybe (Term mode modty (VarOpenCtx v w))
lookupQNameEntryList gamma [] qname = Nothing
lookupQNameEntryList gamma (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ telescoped2lambda $ runIdentity $
                                                mapTelescopedSimple (
                                                  \ wkn -> Identity . _val'term . _decl'content
                                                ) val
  | otherwise = lookupQNameEntryList gamma entries qname
lookupQNameEntryList gamma (EntryModule modul : entries) qname = case qname of
  Raw.Qualified [] _ -> lookupQNameEntryList gamma entries qname
  Raw.Qualified (moduleStr : qual) name ->
    if moduleStr == _module'name modul
    then Just $ telescoped2lambda $ runIdentity $ _modul -- mapTelescoped _modul gamma modul
    else lookupQNameEntryList gamma entries qname

lookupQNameModule :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Ctx ty mode modty v w -> ModuleRHS mode modty (VarOpenCtx v w) -> Raw.QName -> Maybe (Term mode modty (VarOpenCtx v w))
lookupQNameModule gamma modul qname =
  lookupQNameEntryList gamma (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

lookupQName :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Ctx ty mode modty v w -> Raw.QName -> Maybe (Term mode modty (VarOpenCtx v w))
lookupQName CtxEmpty qname = Nothing
lookupQName (gamma :.. seg) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ Var3 $ VarFromCtx VarLast
                                else wkn $ lookupQName gamma qname
    _ -> wkn $ lookupQName gamma qname
  where wkn = fmap (fmap (bimap VarWkn id))
lookupQName (seg :^^ gamma) qname = case _segment'name seg of
  Nothing -> wkn $ lookupQName gamma qname
  Just varname -> case qname of
    Raw.Qualified [] name -> if name == varname
                                then Just $ Var3 $ VarFromCtx VarFirst
                                else wkn $ lookupQName gamma qname
    _ -> wkn $ lookupQName gamma qname
  where wkn = fmap (fmap wkn')
        wkn' u = case u of
           VarBeforeCtx (VarWkn w) -> VarBeforeCtx w
           VarBeforeCtx VarLast -> VarFromCtx $ VarFirst
           VarFromCtx v -> VarFromCtx $ VarLeftWkn v
lookupQName (gamma :<...> modul) qname = case lookupQNameModule gamma modul qname of
  Just t -> wkn $ Just t
  Nothing -> wkn $ lookupQName gamma qname
  where wkn = fmap (fmap (bimap VarInModule id))
lookupQName (dkappa :\\ gamma) qname = wkn $ lookupQName gamma qname
  where wkn = fmap (fmap (bimap VarDiv id))
