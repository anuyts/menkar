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
import Control.Exception.AssertFalse

----------------------------

telescoped2lambda :: Telescoped Type Term mode modty v -> Term mode modty v
telescoped2lambda (Telescoped t) = t
telescoped2lambda (seg :|- telescopedTerm) = Expr3 $ TermCons $ Lam $ Binding seg (telescoped2lambda telescopedTerm)

----------------------------

lookupQNameEntryList :: (Functor mode, Functor modty) =>
  [Entry mode modty v] -> Raw.QName -> Maybe (Term mode modty v)
lookupQNameEntryList [] qname = Nothing
lookupQNameEntryList (EntryVal val : entries) qname
  | qname == Raw.Qualified [] (_val'name val) = Just $ telescoped2lambda $ runIdentity $
                                                mapTelescopedSimple (
                                                  \ wkn -> Identity . _val'term . _decl'content
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

lookupQNameModule :: (Functor mode, Functor modty) =>
  ModuleRHS mode modty v -> Raw.QName -> Maybe (Term mode modty v)
lookupQNameModule modul qname =
  lookupQNameEntryList (fmap (fmap (\ (VarInModule v) -> v)) $ view moduleRHS'entries modul) qname

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
           _ -> unreachable
lookupQName (gamma :<...> modul) qname = case lookupQNameModule modul qname of
  Just t -> wkn $ Just t
  Nothing -> wkn $ lookupQName gamma qname
  where wkn = fmap (fmap (bimap VarInModule id))
lookupQName (dkappa :\\ gamma) qname = lookupQName gamma qname
