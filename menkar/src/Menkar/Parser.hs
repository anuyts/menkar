{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Menkar.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Identity
import Control.Applicative
import Data.Char
import Data.Number.Nat
import Data.Maybe
--import Data.Ord

-- Testing -------------------------------------------------

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

testparse :: String -> IO (Either (MP.ParseError Char ParseError) Raw.File)
testparse filename = do
  let path = "Menkar/code-examples/" ++ filename
  code <- readFile path
  return $ MP.parse file path code

quickParse :: MP.Parsec ParseError String a -> String -> a
quickParse parser code = case MP.parse parser "quick" code of
  Left e -> error $ show e
  Right a -> a

-- ParseError ----------------------------------------------

data ParseError
instance Eq ParseError where
  e == e' = True
instance Ord ParseError where
  compare e e' = EQ
instance Show ParseError where
  show e = "ERROR"

-- CanParse ------------------------------------------------

class (MP.MonadParsec ParseError String m) => CanParse m

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | LooseChar | MiscChar | OpenChar | CloseChar
  deriving (Show, Eq)

describeCharType :: CharType -> String
describeCharType ct = case ct of
  SpaceChar -> "whitespace character (unicode)"
  LetterChar -> "letter character (unicode)"
  DigitChar -> "digit"
  LooseChar -> "one of '|' and '.'"
  MiscChar -> "miscellaneous unicode character"
  OpenChar -> "opening delimiter (unicode)"
  CloseChar -> "closing delimiter (unicode)"

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | c == '.' = LooseChar
  | c == '|' = LooseChar
  | otherwise = case generalCategory c of
      OpenPunctuation -> OpenChar
      ClosePunctuation -> CloseChar
      _ -> MiscChar

{-
isFirstNameChar :: Char -> Bool
isFirstNameChar c = case charType c of
  LetterChar -> True
  OpChar -> True
  _ -> Falsec
-}
{-
isNameChar :: Char -> Bool
isNameChar c = case charType c of
  LetterChar -> True
  DigitChar -> True
  MiscChar -> True
  _ -> False
-}

-- keywords ------------------------------------------------

keywords :: [String]
keywords = [ ":"     -- typing
           , "-:"    -- typing propositions
           , "="     -- assignment
           --, "->"    -- function type
           --, "><"    -- sigma type
           --, "Uni"   -- universe
           --, "?"     -- for Glue etc.
           , ">>"    -- mapsto
           , "module"
           , "val"
           , "data"
           , "codata"
           , "import"
           , "open"
           , "resolution"
           , "where"
           ]

-- basic subparsers ----------------------------------------

{-| Consumes zero or more whitespace characters, line or block comments -}
manySpace :: CanParse m => m ()
manySpace = MPL.space MP.space1 lineCmnt blockCmnt
  where
    lineCmnt  = MPL.skipLineComment "//"
    blockCmnt = MPL.skipBlockCommentNested "/*" "*/"

{-| 'lexeme p' consumes 'p', then 'manySpace'. -}
lexeme :: CanParse m => m a -> m a
lexeme = MPL.lexeme manySpace

{-| Cconsumes and returns the specified string.
    DO NOT USE THIS FOR KEYWORDS, lest "ifbla" will be parsed as "if bla".
    Use for "|", ",". -}
symbol :: CanParse m => String -> m String
symbol = MPL.symbol manySpace

pipe :: CanParse m => m ()
pipe = void $ symbol "|"
--comma :: CanParse m => m ()
--comma = void $ symbol ","
dot :: CanParse m => m ()
dot = void $ lexeme $ MP.char '.' <* MP.notFollowedBy nameStickyChar

parens :: CanParse m => m a -> m a
parens = MP.between (symbol "(") (symbol ")")

accols :: CanParse m => m a -> m a
accols = MP.between (symbol "{") (symbol "}")

brackets :: CanParse m => m a -> m a
brackets = MP.between (symbol "[") (symbol "]")

charByType :: CanParse m => CharType -> m Char
charByType ct = MP.label (describeCharType ct) $ MP.satisfy (\ c -> charType c == ct)

nameChar :: CanParse m => m Char
nameChar = charByType LetterChar <|> charByType DigitChar <|> charByType MiscChar

nameStickyChar :: CanParse m => m Char
nameStickyChar = nameChar <|> MP.char '.'

natLiteral :: CanParse m => m Nat
natLiteral = do
  --string <- some $ charByType DigitChar
  string <- (lexeme . MP.try) ((some $ charByType DigitChar) <* MP.notFollowedBy nameChar)
  return $ (read string :: Nat)

keyword :: CanParse m => String -> m ()
keyword w = (lexeme . MP.try) (MP.string w *> MP.notFollowedBy nameStickyChar)

identifierString :: CanParse m => m String
identifierString = MP.label "identifier" $ MP.try $ do
  string <- some nameChar
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string

unqIdentifier :: CanParse m => m String
unqIdentifier = MP.label "unqualified identifier" $
  lexeme $ identifierString <* (MP.notFollowedBy nameStickyChar <|> fail msg)
  where
    msg = "You have either neglected to leave a space after this identifier, or you have used a" ++
      " qualified identifier where an unqualified one was expected."

qIdentifier :: CanParse m => m Raw.QName
qIdentifier = MP.label "qualified identifier" $ lexeme $ do
  head <- identifierString
  tail <- many $ do
    MP.char '.'
    identifierString <|> fail "Another identifier is expected after '.', with no space in between."
  return $ Raw.QName (head : tail)

{-
haskellCharLiteral :: CanParse m => m String
haskellCharLiteral = MP.label "Haskell character literal" $ do
  "'" <- MP.string "'"
  content <- many $ (MP.label "any character other than (') or (\\)" $
                      return <$> MP.satisfy (\ c . not $ c `elem` ['\'', '\\']))
                    <|> MP.string "\\'"
                    <|> (MP.string "\\" <* MP.notFollowedBy (MP.String "\'"))
  "'" <- MP.string "'"
  return $ "'" ++ concat content ++ "'"
-}

{-
{-| Parses any rubbish, including what would otherwise be a comment,
    until a parenthesis closes that was never opened. Parentheses need not match.
    This parser is unaware of quotes. Don't use strings containing parentheses in Menkar
    pseudocode. -}
haskellCode :: CanParse m => m String
haskellCode = MP.label "Haskell code" $ fmap concat $ many $
  ((\ c -> [c]) <$> MP.satisfy (\ c -> not $ charType c `elem` [OpenChar, CloseChar]))
  <|> do
        openChar <- MP.satisfy (\ c -> charType c == OpenChar)
        contents <- haskellCode
        closeChar <- MP.satisfy (\ c -> charType c == CloseChar)
        return $ [openChar] ++ contents ++ [closeChar]

haskellCodeBracketed :: CanParse m => m String
haskellCodeBracketed = lexeme $
  MP.between (MP.string "[") (MP.string "]") haskellCode
-}

{-
optionalEntrySep :: CanParse m => m ()
optionalEntrySep = void (symbol ",") <|> return ()

requiredEntrySep :: CanParse m => m ()
requiredEntrySep = void $ symbol "," <|> MP.lookAhead (symbol "}")
-}

-- expression subparsers -----------------------------------

atom :: CanParse m => m Raw.Atom
atom = (Raw.AtomQName <$> qIdentifier)
  <|> (Raw.AtomParens <$> parens expr)
  <|> (Raw.AtomDot <$ dot)
  <|> (Raw.AtomTelescope <$> telescopeSome)
  <|> (Raw.AtomNatLiteral <$> natLiteral)

expr :: CanParse m => m Raw.Expr
expr = Raw.Expr <$> some atom

-- high-level subparsers -----------------------------------

-- annotations

--haskellAnnotation :: CanParse m => m Raw.Annotation
--haskellAnnotation = Raw.AnnotationHaskell <$> haskellCodeBracketed

atomicAnnotation :: CanParse m => m Raw.Annotation
atomicAnnotation = (\qname -> Raw.Annotation qname Nothing) <$> qIdentifier

compoundAnnotation :: CanParse m => m Raw.Annotation
compoundAnnotation = parens $ do
  qname <- qIdentifier
  content <- expr
  return $ Raw.Annotation qname (Just content)

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> compoundAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

entryAnnotation :: CanParse m => m Raw.Annotation
entryAnnotation = brackets $ do
  qname <- qIdentifier
  content <- optional expr
  return $ Raw.Annotation qname content

-- telescopes

segmentNamesAndColon :: CanParse m => m Raw.LHSNames
segmentNamesAndColon = Raw.SomeNamesForTelescope <$> some unqIdentifier <* keyword ":"

segmentConstraintColon :: CanParse m => m Raw.LHSNames
segmentConstraintColon = Raw.NoNameForConstraint <$ keyword "-:"

constraint :: CanParse m => m Raw.LHS
constraint = accols $ do
      annots <- fromMaybe [] <$> optional annotationClause
      keyword "-:"
      typ <- expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = Raw.NoNameForConstraint,
        Raw.contextLHS = Raw.Telescope [],
        Raw.typeLHS = Just typ
      }

argument :: CanParse m => m Raw.LHS 
argument = MP.try $ accols $ do
      annots <- fromMaybe [] <$> optional annotationClause
      --names <- segmentNamesAndColon <|> segmentConstraintColon
      names <- Raw.SomeNamesForTelescope <$> some unqIdentifier
      context <- telescopeMany
      maybeType <- optional $ keyword ":" *> expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = names,
        Raw.contextLHS = context,
        Raw.typeLHS = maybeType
      }

segment :: CanParse m => m Raw.Segment
segment = MP.label "telescope segment" $ Raw.Segment <$> (argument <|> constraint)

telescopeMany :: CanParse m => m Raw.Telescope
telescopeMany = MP.label "telescope (possibly empty)" $ Raw.Telescope <$> many segment

telescopeSome :: CanParse m => m Raw.Telescope
telescopeSome = MP.label "telescope (non-empty)" $ Raw.Telescope <$> some segment

lhs :: CanParse m => m Raw.LHS
lhs = MP.label "LHS" $ do
  annots <- many entryAnnotation
  name <- Raw.QNameForEntry <$> qIdentifier
  context <- telescopeMany
  maybeType <- optional $ do
    keyword ":"
    expr
  return $ Raw.LHS {
    Raw.annotationsLHS = annots,
    Raw.namesLHS = name,
    Raw.contextLHS = context,
    Raw.typeLHS = maybeType
    }

moduleRHS :: CanParse m => m Raw.RHS
moduleRHS = MP.label "module RHS" $
  Raw.RHSModule <$> (keyword "where" *> (accols $ many entry))
  {-do
  keyword "module"
  entries <- accols $ many entry
  return $ Raw.RHSModule entries-}

valRHS :: CanParse m => m Raw.RHS
valRHS = Raw.RHSVal <$> (keyword "=" *> expr) 

rhs :: CanParse m => Raw.EntryHeader -> m Raw.RHS
rhs Raw.HeaderModule = moduleRHS
rhs Raw.HeaderVal = valRHS
rhs Raw.HeaderData = fail "Not supported yet: data"
rhs Raw.HeaderCodata = fail "Not supported yet : codata"
rhs Raw.HeaderResolution = return Raw.RHSResolution

entryHeader :: CanParse m => m Raw.EntryHeader
entryHeader =
  (Raw.HeaderModule <$ keyword "module")
  <|> (Raw.HeaderVal <$ keyword "val")
  <|> (Raw.HeaderData <$ keyword "data")
  <|> (Raw.HeaderCodata <$ keyword "codata")
  <|> (Raw.HeaderResolution <$ keyword "resolution")

lrEntry :: CanParse m => m Raw.LREntry
lrEntry = MP.label "entry" $ do
  header <- entryHeader
  anLHS <- lhs
  anRHS <- rhs header
  return $ Raw.LREntry header anLHS anRHS

{-
modul :: CanParse m => m Raw.Module
modul = do
  anEntry <- entry
  case anEntry of
    Raw.EntryModule aModule -> return aModule
    _ -> fail "Expected a module" -- TODO
-}

entry :: CanParse m => m Raw.Entry
entry = (Raw.EntryLR <$> lrEntry)

file :: CanParse m => m Raw.File
file = MP.between manySpace MP.eof $ do
  themodule <- lrEntry
  return $ Raw.File themodule
