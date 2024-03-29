{-# LANGUAGE FlexibleInstances #-}

module Menkar.PrettyPrint.Raw.Syntax where

import Menkar.Raw.Syntax
import Menkar.PrettyPrint.Raw.Class
import Menkar.System.PrettyPrint.Raw

import Control.Exception.AssertFalse
import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Maybe
import Data.Either
import Control.Lens

--showshowdoc :: Doc -> String
--showshowdoc doc = replace "\\n" "\t\t\\n\\\n\\" $ show $ displayS (renderPretty 1.0 100 doc) ""

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

instance Unparsable ProjSpec where
  unparse' (ProjSpecNamed name) = "." ++| unparse' name
  unparse' (ProjSpecNumbered n) = ribbon $ '.' : show n
  unparse' (ProjSpecTail n) = ribbon $ ".." ++ show n
  parserName (ProjSpecNamed _) = "projectorNamed"
  parserName (ProjSpecNumbered _) = "projectorNumbered"
  parserName (ProjSpecTail _) = "projectorTail"

instance SysRawPretty sys => Unparsable (Eliminator sys) where
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
  unparse' (ElimProj p) = unparse' p
  unparse' (ElimUnbox) = ribbon ".{}"
  parserName (ElimDots) = "eliminatorEnd"
  parserName _ = "eliminator"

instance SysRawPretty sys => Unparsable (ExprC sys) where
  unparse' (ExprQName qname) = unparse' qname
  unparse' (ExprParens expr) = "(" ++| unparse' expr |++ ")"
  unparse' (ExprNatLiteral n) = ribbon $ show n
  unparse' ExprImplicit = ribbon "_"
  unparse' (ExprGoal str) = ribbon $ '?' : str
  unparse' (ExprSys sysExprC) = unparse' sysExprC
  parserName _ = "exprC"

unparseOpElimination :: SysRawPretty sys => Elimination sys -> PrettyTree String
unparseOpElimination (Elimination (ExprQName (Qualified [] (Name Op opname))) eliminators)
  = ribbon opname \\\ (" " ++|) . unparse' <$> eliminators
unparseOpElimination (Elimination expr3 eliminators) = "`" ++| unparse' expr3 \\\ (" " ++|) . unparse' <$> eliminators
instance SysRawPretty sys => Unparsable (Elimination sys) where
  unparse' (Elimination expr3 eliminators) = unparse' expr3 \\\ (" " ++|) . unparse' <$> eliminators
  parserName _ = "elimination"

instance SysRawPretty sys => Unparsable (ExprB sys) where
  unparse' (ExprElimination elim) = unparse' elim
  parserName _ = "exprB"

instance SysRawPretty sys => Unparsable (Operand sys) where
  unparse' (OperandTelescope telescope) = unparse' telescope
  unparse' (OperandExpr expr2) = unparse' expr2
  parserName _ = "operand"

unparseExprRHS :: SysRawPretty sys => (Elimination sys, Maybe (Expr sys)) -> [PrettyTree String]
unparseExprRHS (elim, Nothing) = [" " ++| unparseOpElimination elim]
unparseExprRHS (elim, Just expr) =
  let (operandPretty, restPretty) = unparseExpr expr
  in  (" " ++| unparseOpElimination elim |++ " " |+| operandPretty) : restPretty
unparseExpr :: SysRawPretty sys => Expr sys -> (PrettyTree String, [PrettyTree String])
unparseExpr (ExprOps operand x) = (unparse' operand, fromMaybe [] (unparseExprRHS <$> x))

instance SysRawPretty sys => Unparsable (Expr sys) where
  unparse' expr = 
    let (operandPretty, restPretty) = unparseExpr expr
    in  operandPretty \\\ restPretty
  parserName _ = "expr"

instance SysRawPretty sys => Unparsable (Annotation sys) where
  unparse' (Annotation annotName Nothing) = ribbon annotName
  unparse' (Annotation annotName (Just arg)) = (ribbon annotName \\\ [unparse' arg])
  {-
  unparse' (Annotation qname []) = unparse' qname
  unparse' (Annotation qname elims) = "[" ++| unparse' qname
                                            \\\ ((" " ++|) . unparse' <$> elims)
                                            /// ribbon "]"
  -}
  parserName _ = "annotation"

unparseAnnotationClause :: SysRawPretty sys => [Annotation sys] -> PrettyTree String
unparseAnnotationClause annots = ribbonEmpty \\\ unparse' <$> annots

unparseEntryAnnotations :: SysRawPretty sys => [Annotation sys] -> PrettyTree String
unparseEntryAnnotations annots = "[" ++| unparseAnnotationClause annots |++ "]"

instance SysRawPretty sys => Unparsable (Segment sys) where
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

instance SysRawPretty sys => Unparsable (ModalLock sys) where
  unparse' (ModalLock annots) = "{" ++| unparseEntryAnnotations annots |++ "}"
  parserName _ = "modalLock"

instance SysRawPretty sys => Unparsable (Telescope sys) where
  unparse' (Telescope segments) = treeGroup $ segments <&> \case
    Left modalLock -> unparse' modalLock
    Right segment -> unparse' segment
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

unparseLHSUntyped :: SysRawPretty sys => Declaration sys declSort -> PrettyTree String
unparseLHSUntyped decl =
    unparseEntryAnnotations (decl'annotations decl)
    |+| unparse' (decl'names decl) |++ " "
    |+| unparse' (decl'telescope decl)
    ||| ribbonEmpty -- as a guard against \+\
instance SysRawPretty sys => Unparsable (Declaration sys declSort) where
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
  
instance SysRawPretty sys => Unparsable (RHS sys declSort) where
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

instance SysRawPretty sys => Unparsable (Entry sys declSort) where
  unparse' (EntryLR header lhs rhs) = headerKeyword header ++ " " ++| unparse' lhs \+\ [unparse' rhs]
  parserName _ = "entry"

instance SysRawPretty sys => Unparsable (AnyEntry sys) where
  unparse' (AnyEntry entry) = unparse' entry
  parserName _ = "Raw.AnyEntry <$> entry"

instance SysRawPretty sys => Unparsable (File sys) where
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
instance SysRawPretty sys => Show (Eliminator sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (ExprC sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Elimination sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (ExprB sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Operand sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Expr sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Annotation sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Segment sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (Telescope sys) where
  show = showUnparsable
instance Show (DeclNames declSort) where
  show = showUnparsable
instance SysRawPretty sys => Show (Declaration sys declSort) where
  show = showUnparsable
instance SysRawPretty sys => Show (RHS sys declSort) where
  show = showUnparsable
instance SysRawPretty sys => Show (Entry sys declSort) where
  show = showUnparsable
instance SysRawPretty sys => Show (AnyEntry sys) where
  show = showUnparsable
instance SysRawPretty sys => Show (File sys) where
  show = showUnparsable
