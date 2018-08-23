{-# LANGUAGE FlexibleInstances #-}

module Menkar.Raw.PrettyPrint where

import Control.Exception.AssertFalse
import Menkar.Raw.Base
import Text.PrettyPrint.Tree

class Unparsable x where
  unparse' :: x -> PrettyTree String
  parserName :: x -> String
  unparse :: x -> String
  unparse x = render (RenderState 100 "  " "  ") $ unparse' x
  showUnparsable :: x -> String
  showUnparsable x = "(quickParse (manySpace *> " ++ parserName x ++ " <* eof) \"\n" ++ unparse x ++ "\n\")"

------------------------------------------

instance Unparsable Name where
  unparse' (Name NonOp name) = ribbon name
  unparse' (Name Op name) = ribbon $ '_' : name
  parserName _ = "unqName"
--instance Show Name where
--  show = showUnparsable

instance Unparsable a => Unparsable (Qualified a) where
  unparse' (Qualified modules name) = (foldr (\modul qname -> modul ++ '.' : qname) "" modules) ++| unparse' name
  parserName (Qualified _ name) = "qualified " ++ parserName name

instance Unparsable Eliminator where
  unparse' (ElimEnd ArgSpecNext) = ribbon "..."
  unparse' (ElimEnd ArgSpecVisible) = ribbon "...<AT_NEXT_VISIBLE>"
  unparse' (ElimEnd (ArgSpecNamed name)) = ribbon $ ".{" ++ name ++ " = ...}"
  unparse' (ElimArg ArgSpecNext expr) = ".{" ++| unparse' expr |++ "}"
  unparse' (ElimArg ArgSpecVisible expr) = "(" ++| unparse' expr |++ ")"
  unparse' (ElimArg (ArgSpecNamed name) expr) = ".{" ++ name ++ " = " ++| unparse' expr |++ "}"
  unparse' (ElimProj (ProjSpecNamed name)) = ribbon $ '.' : name
  unparse' (ElimProj (ProjSpecNumbered n)) = ribbon $ '.' : show n
  unparse' (ElimProj (ProjSpecTail n)) = ribbon $ ".." ++ show n
  parserName (ElimEnd _) = "eliminatorEnd"
  parserName (ElimArg _ _) = "eliminator"
  parserName (ElimProj _) = "eliminator"

instance Unparsable Expr3 where
  unparse' (ExprQName qname) = unparse' qname
  unparse' (ExprParens expr) = "(" ++| unparse' expr |++ ")"
  unparse' (ExprNatLiteral n) = ribbon $ show n
  unparse' ExprImplicit = ribbon "_"
  parserName _ = "expr3"

--instance Unparsable Elimination where
  

instance Unparsable Expr where
  unparse' = todo
  parserName = todo
