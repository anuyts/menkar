{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo #-}

module Menkar.Parser.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
--import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Parser.Class
import Menkar.System.Parser

import qualified Text.Megaparsec.Char.Lexer as MPL

import Control.Monad.Identity
import Control.Applicative
import Data.Char
import Data.Maybe
import Data.Void
--import Data.Ord

-- Testing -------------------------------------------------

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

testparse :: (SysParser sys) => String -> IO (Either (MP.ParseErrorBundle String ParseError) (Raw.File sys))
testparse filename = do
  let path = "Menkar/code-examples/" ++ filename
  code <- readFile path
  return $ MP.parse file path code

quickParse :: MP.Parsec ParseError String a -> String -> a
quickParse parser code = case MP.parse parser "quick" code of
  Left e -> error $ show e
  Right a -> a

parse :: MP.Parsec ParseError String a -> String -> String -> Either (MP.ParseErrorBundle String ParseError) a
parse parser path code = MP.parse parser path code

-- expression subparsers -----------------------------------

exprC :: forall sys m .
  (SysParser sys, CanParse m) => m (Raw.ExprC sys)
exprC = MP.label "atomic expression" $
  (Raw.ExprParens <$> parens expr) <|>
  (Raw.ExprImplicit <$ loneUnderscore) <?|>
  (Raw.ExprQName <$> qName) <?|>
  (Raw.ExprNatLiteral <$> natLiteralNonSticky) <?|>
  (Raw.ExprGoal <$> goal) <?|>
  (Raw.ExprSys <$> sysExprC @sys)

argNext :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
argNext = Raw.ElimArg Raw.ArgSpecNext <$> (dotPrecise *> accols expr)
argExplicit :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
argExplicit = Raw.ElimArg Raw.ArgSpecExplicit . Raw.exprCtoAsmart <$> exprC
argNamed :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
argNamed = (dotPrecise *>) $ accols $ do
  aName <- unqName
  keyword "="
  aValue <- expr
  return $ Raw.ElimArg (Raw.ArgSpecNamed aName) aValue

unbox :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
unbox = Raw.ElimUnbox <$ (dotPrecise *> accols manySpace)

projectorNamed :: CanParse m => m Raw.ProjSpec
projectorNamed = Raw.ProjSpecNamed <$> (dotPrecise *> unqName)
projectorNumbered :: CanParse m => m Raw.ProjSpec
projectorNumbered = Raw.ProjSpecNumbered <$> (dotPrecise *> natLiteralNonSticky)
projectorTail :: CanParse m => m Raw.ProjSpec
projectorTail = Raw.ProjSpecTail <$> (dotPrecise *> dotPrecise *> natLiteralNonSticky)

eliminator :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
eliminator = MP.label "eliminator" $
  argExplicit <|> argNext <?|> argNamed <?|> unbox <?|>
  (Raw.ElimProj <$> (projectorNamed <?|> projectorNumbered <?|> projectorTail))
opEliminator :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
opEliminator = MP.label "operator eliminator" $ argNext <?|> argNamed
--annotEliminator :: (SysParser sys, CanParse m) => m (Raw.Eliminator sys)
--annotEliminator = MP.label "annotation eliminator" $ argExplicit <|> argNext <?|> argNamed

{-
argEndNext :: CanParse m => m Raw.Eliminator
argEndNext = Raw.ElimEnd Raw.ArgSpecNext <$ loneDots
argEndNamed :: CanParse m => m Raw.Eliminator
argEndNamed = (dotPrecise *>) $ accols $ do
  aName <- unqName
  keyword "="
  loneDots
  return $ Raw.ElimEnd $ Raw.ArgSpecNamed aName
-}
eliminatorEnd :: CanParse m => m (Raw.Eliminator sys)
eliminatorEnd = Raw.ElimDots <$ loneDots
--eliminatorEnd = MP.label "end-of-elimination marker" $ argEndNext <?|> argEndNamed

eliminators :: (SysParser sys, CanParse m) => m [Raw.Eliminator sys]
eliminators = MP.label "eliminators" $
  (++) <$> manyTry eliminator <*> (fromMaybe [] <$> optionalTry ((: []) <$> eliminatorEnd))
opEliminators :: (SysParser sys, CanParse m) => m [Raw.Eliminator sys]
opEliminators = MP.label "operator eliminators" $ manyTry opEliminator
--annotEliminators :: (SysParser sys, CanParse m) => m [Raw.Eliminator sys]
--annotEliminators = MP.label "annotation eliminators" $ manyTry annotEliminator

elimination :: (SysParser sys, CanParse m) => m (Raw.Elimination sys)
elimination = Raw.Elimination <$> exprC <*> eliminators

exprB :: (SysParser sys, CanParse m) => m (Raw.ExprB sys)
exprB = MP.label "operator-free expression" $ Raw.ExprElimination <$> elimination

operand :: (SysParser sys, CanParse m) => m (Raw.Operand sys)
operand = (Raw.OperandTelescope <$> telescopeSome) <?|> (Raw.OperandExpr <$> exprB)

operatorHead :: (SysParser sys, CanParse m) => m (Raw.ExprC sys)
operatorHead = (ticks $ Raw.ExprParens <$> expr) <|> (Raw.ExprQName <$> qOp)
operator :: (SysParser sys, CanParse m) => m (Raw.Elimination sys)
operator = MP.label "operator with eliminations" $ Raw.Elimination <$> operatorHead <*> opEliminators

expr :: forall sys m . (SysParser sys, CanParse m) => m (Raw.Expr sys)
expr = MP.label "expression" $ do
  anOperand <- operand
  rest <- optional $ do
    anOperator <- operator
    maybeExpr <- optional expr
    return (anOperator, maybeExpr)
  return $ Raw.ExprOps anOperand rest

{-
atom :: CanParse m => m Raw.Atom
atom = (Raw.AtomQName <$> qIdentifier)
  <|> (Raw.AtomParens <$> parens expr)
  <|> (Raw.AtomDot <$ dot)
  <|> (Raw.AtomSegment <$> segment)
  <|> (Raw.AtomNatLiteral <$> natLiteral)

expr :: CanParse m => m Raw.Expr
expr = Raw.Expr <$> some atom
-}

-- high-level subparsers -----------------------------------

-- annotations - v1

{-
atomicAnnotation :: CanParse m => m Raw.Annotation
atomicAnnotation = (\qword -> Raw.Annotation qword []) <$> qWord

compoundAnnotation :: CanParse m => m Raw.Annotation
compoundAnnotation = brackets $ do
  qword <- qWord
  content <- annotEliminators
  return $ Raw.Annotation qword content

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> compoundAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

entryAnnotation :: CanParse m => m Raw.Annotation
entryAnnotation = compoundAnnotation
-}

-- annotations - v2

{-
annotation :: (SysParser sys, CanParse m) => m (Raw.Annotation sys)
annotation = MP.label "annotation" $ do
  annotName <- qWord
  annotArg <- optional expr
  return $ Raw.Annotation annotName annotArg

segmentAnnotations :: (SysParser sys, CanParse m) => m [Raw.Annotation sys]
segmentAnnotations = manyTry $ annotation <* pipe

entryAnnotations :: (SysParser sys, CanParse m) => m [Raw.Annotation sys]
entryAnnotations = (brackets $ someSep pipe annotation) <|> return []
-}

-- annotations - v3

annotation :: (SysParser sys, CanParse m) => m (Raw.Annotation sys)
annotation = MP.label "annotation" $ do
  annotName <- some opChar <* MP.notFollowedBy opChar
  annotArg <- (Just <$> exprC) <?|> (Nothing <$ someSpace)
  return $ Raw.Annotation annotName annotArg

segmentAnnotations :: (SysParser sys, CanParse m) => m [Raw.Annotation sys]
segmentAnnotations = manyTry $ annotation

entryAnnotations :: (SysParser sys, CanParse m) => m [Raw.Annotation sys]
entryAnnotations = manyTry $ annotation

-- telescopes

modalLock :: (SysParser sys, CanParse m) => m (Raw.ModalLock sys)
modalLock = MP.label "telescope modal-lock segment" $ accols $ Raw.ModalLock <$> segmentAnnotations

segment :: (SysParser sys, CanParse m) => m (Raw.Segment sys)
segment = MP.label "telescope segment" $ accols $ do
      annots <- segmentAnnotations --fromMaybe [] <$> optionalTry annotationClause
      names <- Raw.DeclNamesSegment <$> some ((Just <$> unqName) <|> (Nothing <$ loneUnderscore))
      --context <- telescopeMany
      maybeType <- optional $ keyword ":" *> expr
      return $ Raw.Segment $ Raw.Declaration {
        Raw.decl'annotations = annots,
        Raw.decl'names = names,
        Raw.decl'telescope = Raw.Telescope [],
        Raw.decl'content = fromMaybe Raw.DeclContentEmpty $ Raw.DeclContent <$> maybeType
      }

segmentOrLock :: (SysParser sys, CanParse m) => m (Either (Raw.ModalLock sys) (Raw.Segment sys))
segmentOrLock = Right <$> segment <?|> Left <$> modalLock

telescopeMany :: (SysParser sys, CanParse m) => m (Raw.Telescope sys)
telescopeMany = MP.label "telescope (possibly empty)" $ Raw.Telescope <$> many segmentOrLock

telescopeSome :: (SysParser sys, CanParse m) => m (Raw.Telescope sys)
telescopeSome = MP.label "telescope (non-empty)" $ Raw.Telescope <$> some segmentOrLock

lhs :: forall sys m declSort .
  (SysParser sys, CanParse m) =>
  Raw.EntryHeader declSort ->
  m (Raw.Declaration sys declSort)
lhs header = MP.label "LHS" $ do
  annots <- entryAnnotations --many entryAnnotation
  name <- case header of
    Raw.HeaderToplevelModule -> do
      qname <- qName
      qstring <- sequenceA $ (<$> qname) $ \ name -> case name of
        Raw.Name Raw.NonOp str' -> return str'
        _ -> fail $ "Expected non-operator name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesToplevelModule qstring
    Raw.HeaderModule -> do
      qname <- qName
      str <- case qname of
        Raw.Qualified [] (Raw.Name Raw.NonOp str') -> return str'
        _ -> fail $ "Expected unqualified non-operator name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesModule str
    Raw.HeaderVal -> do
      qname <- qName
      name <- case qname of
        Raw.Qualified [] name' -> return name'
        _ -> fail $ "Expected unqualified name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesVal name
    header -> fail $ "Not supported yet: " ++ Raw.headerKeyword header
  context <- telescopeMany
  maybeType <- optional $ do
    keyword ":"
    expr @sys
  declContentType <- case maybeType of
    Nothing -> return $ Raw.DeclContentEmpty
    Just ty -> case header of
      Raw.HeaderModule -> fail $ "Did not expect a type here: " ++ Raw.unparse ty
      Raw.HeaderToplevelModule -> fail $ "Did not expect a type here: " ++ Raw.unparse ty
      Raw.HeaderVal -> return $ Raw.DeclContent ty
      _ -> fail $ "Not supported yet: " ++ Raw.headerKeyword header
  return $ Raw.Declaration {
    Raw.decl'annotations = annots,
    Raw.decl'names = name,
    Raw.decl'telescope = context,
    Raw.decl'content = declContentType
    }

moduleRHS :: (SysParser sys, CanParse m) => m (Raw.RHS sys (Raw.DeclSortModule b))
moduleRHS = MP.label "module RHS" $
  Raw.RHSModule <$> (keyword "where" *> (accols $ many entry))
  {-do
  keyword "module"
  entries <- accols $ many entry
  return $ Raw.RHSModule entries-}

valRHS :: (SysParser sys, CanParse m) => m (Raw.RHS sys Raw.DeclSortVal)
valRHS = Raw.RHSVal <$> (keyword "=" *> expr) 

rhs :: (SysParser sys, CanParse m) => Raw.EntryHeader declSort -> m (Raw.RHS sys declSort)
rhs Raw.HeaderToplevelModule = moduleRHS
rhs Raw.HeaderModule = moduleRHS
rhs Raw.HeaderVal = valRHS
rhs Raw.HeaderData = fail "Not supported yet: data"
rhs Raw.HeaderCodata = fail "Not supported yet : codata"
rhs Raw.HeaderResolution = fail "Not supported yet : resolution" --return Raw.RHSResolution

entryHeader :: (CanParse m) => m Raw.AnyEntryHeader
entryHeader =
    (Raw.AnyEntryHeader Raw.HeaderModule <$ keyword "module")
    <|> (Raw.AnyEntryHeader Raw.HeaderVal <$ keyword "val")
    <|> (Raw.AnyEntryHeader Raw.HeaderData <$ keyword "data")
    <|> (Raw.AnyEntryHeader Raw.HeaderCodata <$ keyword "codata")
    <|> (Raw.AnyEntryHeader Raw.HeaderResolution <$ keyword "resolution")

{-
modul :: CanParse m => m Raw.Module
modul = do
  anEntry <- entry
  case anEntry of
    Raw.EntryModule aModule -> return aModule
    _ -> fail "Expected a module" -- TODO
-}

entry :: (SysParser sys, CanParse m) => m (Raw.AnyEntry sys)
entry = MP.label "entry" $ do
  Raw.AnyEntryHeader header <- entryHeader
  anLHS <- lhs header
  anRHS <- rhs header
  return $ Raw.AnyEntry $ Raw.EntryLR header anLHS anRHS

toplevelEntry :: forall sys m .
  (SysParser sys, CanParse m) =>
  m (Raw.AnyEntry sys)
toplevelEntry = MP.label "entry" $ do
  keyword "module"
  anLHS <- lhs Raw.HeaderToplevelModule
  anRHS <- rhs Raw.HeaderToplevelModule
  return $ Raw.AnyEntry $ Raw.EntryLR Raw.HeaderToplevelModule anLHS anRHS

file :: forall sys m . (SysParser sys, CanParse m) => m (Raw.File sys)
file = MP.between manySpace MP.eof $ do
  Raw.AnyEntry themodule <- toplevelEntry @sys
  case Raw.entry'header themodule of
    Raw.HeaderToplevelModule -> return $ Raw.File themodule
    _ -> fail $ "Top level entry should be a module : " ++ Raw.unparse themodule

bulk :: (SysParser sys, CanParse m) => m [Raw.AnyEntry sys]
bulk = MP.between manySpace MP.eof $ many entry
