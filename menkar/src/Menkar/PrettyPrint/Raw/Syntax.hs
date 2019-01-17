{-# LANGUAGE FlexibleInstances #-}

module Menkar.PrettyPrint.Raw.Syntax where

import Control.Exception.AssertFalse
import Menkar.Raw.Syntax
import Text.PrettyPrint.Tree
import Data.Maybe

--showshowdoc :: Doc -> String
--showshowdoc doc = replace "\\n" "\t\t\\n\\\n\\" $ show $ displayS (renderPretty 1.0 100 doc) ""

class Unparsable x where
  unparse' :: x -> PrettyTree String
  parserName :: x -> String
  unparse :: x -> String
  unparse x = render (RenderState 100 "  " "    ") $ unparse' x
  showUnparsable :: x -> String
  showUnparsable x = "(quickParse (manySpace *> " ++ parserName x ++ " <* eof) \"\n" ++ unparse x ++ "\n\")"

------------------------------------------

instance Unparsable String where
  unparse' s = ribbon s
  parserName s = "unqWord"
  unparse s = s

------------------------------------------

instance Unparsable Name where
  unparse' (Name NonOp name) = ribbon name
  unparse' (Name Op name) = ribbon $ "(" ++ name ++ ")"
  parserName _ = "unqName"

unparseQualified :: Unparsable a => Qualified a -> PrettyTree String
unparseQualified (Qualified modules name) = (foldr (\modul qname -> modul ++ '.' : qname) "" modules) ++| unparse' name
{-
instance Unparsable a => Unparsable (Qualified a) where
  unparse' (Qualified modules name) = (foldr (\modul qname -> modul ++ '.' : qname) "" modules) ++| unparse' name
  parserName (Qualified _ name) = "qualified " ++ parserName name
-}

instance Unparsable (Qualified String) where
  unparse' qs = unparseQualified qs
  parserName _ = "qWord"
instance Unparsable (Qualified Name) where
  unparse' qs@(Qualified modules (Name NonOp name)) = unparseQualified qs
  unparse' qs@(Qualified modules (Name Op name)) = "(" ++| unparseQualified qs |++ ")"
  parserName _ = "qName"

instance Unparsable Eliminator where
  --unparse' (ElimEnd ArgSpecNext) = ribbon "..."
  --unparse' (ElimEnd ArgSpecExplicit) = ribbon "...<AT_NEXT_EXPLICIT>"
  --unparse' (ElimEnd (ArgSpecNamed name)) = ".{" ++| unparse' name |++ " = ...}"
  unparse' (ElimDots) = ribbon "..."
  unparse' (ElimArg ArgSpecNext expr) = ".{" ++| unparse' expr |++ "}"
  unparse' (ElimArg ArgSpecExplicit (ExprOps (OperandExpr (ExprElimination (Elimination expr3 []))) Nothing))
    -- special clause for expression that happens to be an expr3
    = unparse' expr3
  unparse' (ElimArg ArgSpecExplicit expr) = "(" ++| unparse' expr |++ ")"
  unparse' (ElimArg (ArgSpecNamed name) expr) = ".{" ++| unparse' name |++ " = " |+| unparse' expr |++ "}"
  unparse' (ElimProj (ProjSpecNamed name)) = "." ++| unparse' name
  unparse' (ElimProj (ProjSpecNumbered n)) = ribbon $ '.' : show n
  unparse' (ElimProj (ProjSpecTail n)) = ribbon $ ".." ++ show n
  parserName (ElimDots) = "eliminatorEnd"
  --parserName (ElimEnd _) = "eliminatorEnd"
  parserName (ElimArg _ _) = "eliminator"
  parserName (ElimProj _) = "eliminator"

instance Unparsable Expr3 where
  unparse' (ExprQName qname) = unparse' qname
  unparse' (ExprParens expr) = "(" ++| unparse' expr |++ ")"
  unparse' (ExprNatLiteral n) = ribbon $ show n
  unparse' ExprImplicit = ribbon "_"
  unparse' (ExprGoal str) = ribbon $ '?' : str
  parserName _ = "expr3"

unparseOpElimination :: Elimination -> PrettyTree String
unparseOpElimination (Elimination (ExprQName (Qualified [] (Name Op opname))) eliminators)
  = ribbon opname \\\ (" " ++|) . unparse' <$> eliminators
unparseOpElimination (Elimination expr3 eliminators) = "`" ++| unparse' expr3 \\\ (" " ++|) . unparse' <$> eliminators
instance Unparsable Elimination where
  unparse' (Elimination expr3 eliminators) = unparse' expr3 \\\ (" " ++|) . unparse' <$> eliminators
  parserName _ = "elimination"

instance Unparsable Expr2 where
  unparse' (ExprElimination elim) = unparse' elim
  parserName _ = "expr2"

instance Unparsable Operand where
  unparse' (OperandTelescope telescope) = unparse' telescope
  unparse' (OperandExpr expr2) = unparse' expr2
  parserName _ = "operand"

unparseExprRHS :: (Elimination, Maybe Expr) -> [PrettyTree String]
unparseExprRHS (elim, Nothing) = [" " ++| unparseOpElimination elim]
unparseExprRHS (elim, Just expr) =
  let (operandPretty, restPretty) = unparseExpr expr
  in  (" " ++| unparseOpElimination elim |++ " " |+| operandPretty) : restPretty
unparseExpr :: Expr -> (PrettyTree String, [PrettyTree String])
unparseExpr (ExprOps operand x) = (unparse' operand, fromMaybe [] (unparseExprRHS <$> x))

instance Unparsable Expr where
  unparse' expr = 
    let (operandPretty, restPretty) = unparseExpr expr
    in  operandPretty \\\ restPretty
  parserName _ = "expr"

instance Unparsable Annotation where
  unparse' (Annotation qstr Nothing) = unparse' qstr |++ " | "
  unparse' (Annotation qstr (Just arg)) = (unparse' qstr \\\ [unparse' arg]) |++ " | "
  {-
  unparse' (Annotation qname []) = unparse' qname
  unparse' (Annotation qname elims) = "[" ++| unparse' qname
                                            \\\ ((" " ++|) . unparse' <$> elims)
                                            /// ribbon "]"
  -}
  parserName _ = "annotation"

unparseAnnotationClause :: [Annotation] -> PrettyTree String
unparseAnnotationClause annots = ribbonEmpty \\\ unparse' <$> annots

unparseEntryAnnotations :: [Annotation] -> PrettyTree String
unparseEntryAnnotations annots = "[" ++| unparseAnnotationClause annots |++ "]"

instance Unparsable Segment where
  unparse' (Segment decl) = "{" ++| content |++ "} "
    where content = case (decl'names decl, decl'content decl) of
            (DeclNamesSegment names, DeclContent typ) ->
              unparseAnnotationClause (decl'annotations decl)
              |+| unparse' (decl'names decl)
              |+| unparse' (decl'telescope decl)
              \\\ [": " ++| unparse' typ]
            (DeclNamesSegment names, DeclContentEmpty) ->
              unparseAnnotationClause (decl'annotations decl)
              |+| unparse' (decl'names decl)
              |+| unparse' (decl'telescope decl)
  parserName _ = "segment"

instance Unparsable Telescope where
  unparse' (Telescope segments) = treeGroup $ unparse' <$> segments
  parserName _ = "telescopeMany"

instance Unparsable (DeclNames declSort) where
  unparse' (DeclNamesSegment names) = (treeGroup $ (|++ " ") . fromMaybe (ribbon "_") . fmap unparse' <$> names)
  unparse' (DeclNamesToplevelModule qstring) = unparse' qstring
  unparse' (DeclNamesModule string) = unparse' string
  unparse' (DeclNamesVal name) = unparse' name
  parserName (DeclNamesSegment _) = "(Raw.DeclNamesSegment <$> some ((Just <$> unqName) <|> (Nothing <$ loneUnderscore)))"
  parserName (DeclNamesToplevelModule _) = "(Raw.DeclNamesToplevelModule <$> qName)"
  parserName (DeclNamesModule _) = "(Raw.DeclNamesModule <$> unqName)"
  parserName (DeclNamesVal _) = "(Raw.DeclNamesVal <$> unqName)"

unparseLHSUntyped :: Declaration declSort -> PrettyTree String
unparseLHSUntyped decl =
    unparseEntryAnnotations (decl'annotations decl)
    |+| unparse' (decl'names decl) |++ " "
    |+| unparse' (decl'telescope decl)
    ||| ribbonEmpty -- as a guard against \+\
instance Unparsable (Declaration declSort) where
  unparse' lhs = case decl'content lhs of
    DeclContentEmpty -> unparseLHSUntyped lhs
    DeclContent typ -> 
      unparseLHSUntyped lhs
      \\\ [": " ++| unparse' typ]
  parserName _ = "lhs"
  {-
  unparse' lhs@(LHS annots lhsNames context Nothing) = unparseLHSUntyped lhs
  unparse' lhs@(LHS annots lhsNames context (Just typ)) =
    unparseLHSUntyped lhs
    \\\ [": " ++| unparse' typ]
  parserName _ = "lhs"
  -}
  
instance Unparsable (RHS declSort) where
  unparse' (RHSModule entries) = ribbon " where {"
                                 \\\ (entries >>= (\ entry -> [unparse' entry, ribbon "        "]))
                                 /// ribbon "}"
  unparse' (RHSVal expr) = " = " ++| unparse' expr
  --unparse' (RHSResolution) = ribbonEmpty
  parserName (RHSModule _) = "moduleRHS"
  parserName (RHSVal _) = "valRHS"
  --parserName (RHSResolution) = "return Raw.RHSResolution"

{-
instance Unparsable LREntry where
  unparse' (LREntry header lhs rhs) = headerKeyword header ++ " " ++| unparse' lhs \+\ [unparse' rhs]
  parserName _ = "lrEntry"
-}

instance Unparsable (Entry declSort) where
  unparse' (EntryLR header lhs rhs) = headerKeyword header ++ " " ++| unparse' lhs \+\ [unparse' rhs]
  parserName _ = "entry"

instance Unparsable AnyEntry where
  unparse' (AnyEntry entry) = unparse' entry
  parserName _ = "Raw.AnyEntry <$> entry"

instance Unparsable File where
  unparse' (File entry) = unparse' entry
  parserName _ = "file"
  showUnparsable x = "(quickParse file \"\n" ++ unparse x ++ "\n\")"

------------------------------------------

instance Show Name where
  show = showUnparsable
instance Show (Qualified String) where
  show = showUnparsable
instance Show (Qualified Name) where
  show = showUnparsable
instance Show Eliminator where
  show = showUnparsable
instance Show Expr3 where
  show = showUnparsable
instance Show Elimination where
  show = showUnparsable
instance Show Expr2 where
  show = showUnparsable
instance Show Operand where
  show = showUnparsable
instance Show Expr where
  show = showUnparsable
instance Show Annotation where
  show = showUnparsable
instance Show Segment where
  show = showUnparsable
instance Show Telescope where
  show = showUnparsable
instance Show (DeclNames declSort) where
  show = showUnparsable
instance Show (Declaration declSort) where
  show = showUnparsable
instance Show (RHS declSort) where
  show = showUnparsable
instance Show (Entry declSort) where
  show = showUnparsable
instance Show AnyEntry where
  show = showUnparsable
instance Show File where
  show = showUnparsable
