{-# LANGUAGE FlexibleInstances #-}

module Menkar.Raw.PrettyPrint where

import Control.Exception.AssertFalse
import Menkar.Raw.Base
import Text.PrettyPrint.Tree
import Data.Maybe

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
  unparse' (ElimArg ArgSpecVisible (ExprOps (OperandExpr (ExprElimination (Elimination expr3 []))) Nothing))
    -- special clause for expression that happens to be an expr3
    = unparse' expr3
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
  unparse' (Annotation qname Nothing) = unparse' qname
  unparse' (Annotation qname (Just expr)) = "[" ++| unparse' qname |++ " "
                                            \\\ [unparse' expr]
                                            /// ribbon "]"
  parserName _ = "annotation"
  
unparseAnnotationBrackets :: Annotation -> PrettyTree String
unparseAnnotationBrackets (Annotation qname Nothing) = "[" ++| unparse' qname |++ "]"
unparseAnnotationBrackets annot@(Annotation qname (Just expr)) = unparse' annot

unparseAnnotationClause :: [Annotation] -> PrettyTree String
unparseAnnotationClause [] = ribbonEmpty
unparseAnnotationClause annots = ribbonEmpty
                                 \\\ (|++ " ") . unparse' <$> annots
                                 /// ribbon "| "

unparseEntryAnnotations :: [Annotation] -> PrettyTree String
unparseEntryAnnotations annots = treeGroup $ (|++ " ") . unparseAnnotationBrackets <$> annots

instance Unparsable Segment where
  unparse' (Segment lhs@(LHS annots lhsNames context typMaybe)) = "{" ++| content |++ "} "
    where content = case (lhsNames, typMaybe) of
            (NoNameForConstraint, Just typ) ->
              unparseAnnotationClause annots
              |+| unparse' context
              ||| "-: " ++| unparse' typ
            (SomeNamesForTelescope names, Just typ) ->
              unparseAnnotationClause annots
              |+| unparse' lhsNames
              |+| unparse' context
              ||| ": " ++| unparse' typ
            (SomeNamesForTelescope names, Nothing) ->
              unparseAnnotationClause annots
              |+| unparse' lhsNames
              |+| unparse' context
            _ -> "<ERRONEOUS_SEGMENT>: " ++| unparse' lhs
  parserName _ = "segment"

instance Unparsable Telescope where
  unparse' (Telescope segments) = treeGroup $ unparse' <$> segments
  parserName _ = "telescopeMany"

instance Unparsable LHSNames where
  unparse' (SomeNamesForTelescope names) = (treeGroup $ (|++ " ") . fromMaybe (ribbon "_") . fmap unparse' <$> names)
  unparse' (QNameForEntry qname) = unparse' qname
  unparse' NoNameForConstraint = ribbon "/*NoNameForConstraint*/"
  parserName (SomeNamesForTelescope _) =
    "(Raw.SomeNamesForTelescope <$> some ((Just <$> unqName) <|> (Nothing <$ loneUnderscore)))"
  parserName (QNameForEntry _) = "(Raw.QNameForEntry <$> qName)"
  parserName NoNameForConstraint = "return Raw.NoNameForConstraint"

unparseLHSUntyped :: LHS -> PrettyTree String
unparseLHSUntyped (LHS annots lhsNames context _) =
    unparseEntryAnnotations annots
    |+| unparse' lhsNames |++ " "
    |+| unparse' context
instance Unparsable LHS where
  unparse' lhs@(LHS annots lhsNames context Nothing) = unparseLHSUntyped lhs
  unparse' lhs@(LHS annots lhsNames context (Just typ)) =
    unparseLHSUntyped lhs
    ||| ": " ++| unparse' typ
  parserName _ = "lhs"

instance Unparsable RHS where
  unparse' (RHSModule entries) = ribbon " where {"
                                 \\\ (entries >>= (\ entry -> [unparse' entry, ribbon "        "]))
                                 /// ribbon "}"
  unparse' (RHSVal expr) = " = " ++| unparse' expr
  unparse' (RHSResolution) = ribbonEmpty
  parserName (RHSModule _) = "moduleRHS"
  parserName (RHSVal _) = "valRHS"
  parserName (RHSResolution) = "return Raw.RHSResolution"

instance Unparsable LREntry where
  unparse' (LREntry header lhs rhs) = headerKeyword header ++ " " ++| unparse' lhs ||| unparse' rhs
  parserName _ = "lrEntry"

instance Unparsable Entry where
  unparse' (EntryLR lrEntry) = unparse' lrEntry
  parserName _ = "entry"

instance Unparsable File where
  unparse' (File lrEntry) = unparse' lrEntry
  parserName _ = "file"
  showUnparsable x = "(quickParse file \"\n" ++ unparse x ++ "\n\")"
  
