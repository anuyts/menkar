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

(<?>) :: CanParse m => m a -> String -> m a
(<?>) = (MP.<?>)

testparse :: String -> IO (Either (MP.ParseError Char ParseError) Raw.File)
testparse filename = do
  let path = "Menkar/code-examples/" ++ filename
  code <- readFile path
  return $ MP.parse file path code

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
  LooseChar -> "one of '|', ',' and '.'"
  MiscChar -> "miscellaneous unicode character"
  OpenChar -> "opening delimiter (unicode)"
  CloseChar -> "closing delimiter (unicode)"

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | elem c ['|', ',', '.'] = LooseChar
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
keywords = [ "_"     -- omission / implicit term
           , "__"    -- instance term
           , ":"     -- typing
           , "-:"    -- typing propositions
           , "="     -- assignment
           --, "->"    -- function type
           --, "><"    -- sigma type
           --, "Uni"   -- universe
           --, "?"     -- for Glue etc.
           , ">>"    -- mapsto
           , "module"
           , "data"
           , "codata"
           , "syntax"
           , "import"
           , "open"
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
comma :: CanParse m => m ()
comma = void $ symbol ","
dot :: CanParse m => m ()
dot = void $ lexeme $ MP.char '.' <* MP.notFollowedBy nameStickyChar

parens :: CanParse m => m a -> m a
parens = MP.between (symbol "(") (symbol ")")

accols :: CanParse m => m a -> m a
accols = MP.between (symbol "{") (symbol "}")

charByType :: CanParse m => CharType -> m Char
charByType ct = MP.satisfy (\ c -> charType c == ct) <?> describeCharType ct

nameChar :: CanParse m => m Char
nameChar = charByType LetterChar <|> charByType DigitChar <|> charByType MiscChar

nameStickyChar :: CanParse m => m Char
nameStickyChar = nameChar <|> MP.char '.'

natural :: CanParse m => m Nat
natural = do
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

qIdentifier :: CanParse m => m [String]
qIdentifier = MP.label "qualified identifier" $ lexeme $ do
  head <- identifierString
  tail <- many $ do
    MP.char '.'
    identifierString <|> fail "Another identifier is expected after '.', with no space in between."
  return $ head : tail

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

optionalEntrySep :: CanParse m => m ()
optionalEntrySep = void (symbol ",") <|> return ()

requiredEntrySep :: CanParse m => m ()
requiredEntrySep = void $ symbol "," <|> MP.lookAhead (symbol "}")

-- expression subparsers -----------------------------------

atom :: CanParse m => m Raw.Atom
atom = (Raw.AtomQName <$> qIdentifier)
  <|> (Raw.AtomParens <$> parens expr)
  <|> (Raw.AtomDot <$ dot)
  <|> (Raw.AtomTelescope <$> telescope)
  <|> (Raw.AtomPseudoArg <$> haskellCodeBracketed)

expr :: CanParse m => m Raw.Expr
expr = Raw.Expr <$> many atom

-- high-level subparsers -----------------------------------

haskellAnnotation :: CanParse m => m Raw.Annotation
haskellAnnotation = Raw.AnnotationHaskell <$> haskellCodeBracketed

atomicAnnotation :: CanParse m => m Raw.Annotation
atomicAnnotation = Raw.AnnotationAtomic <$> unqIdentifier

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> haskellAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

segment :: CanParse m => m Raw.Segment
segment = Raw.Segment <$> accols lhs
  -- or a constraint, or a pseudoLHS

telescope :: CanParse m => m Raw.Telescope
telescope = MP.label "telescope" $ Raw.Telescope <$> many segment

lhs :: CanParse m => m Raw.LHS
lhs = MP.label "LHS" $ do
  annots <- fromMaybe [] <$> optional annotationClause
  name <- unqIdentifier
  context <- telescope
  --TODO arguments!
  maybeType <- optional $ do
    keyword ":"
    expr
  return $ Raw.LHS {
    Raw.annotationsLHS = annots,
    Raw.namesLHS = (Raw.OneNameForEntry name),
    Raw.contextLHS = context,
    Raw.typeLHS = maybeType
    }

moduleRHS :: CanParse m => m Raw.RHS
moduleRHS = MP.label "module RHS" $ do
  keyword "module"
  entries <- accols $ many entry
  return $ Raw.RHSModule entries

rhs :: CanParse m => m Raw.RHS
rhs = moduleRHS

genuineEntry :: CanParse m => m Raw.GenuineEntry
genuineEntry = MP.label "module entry" $ do
  anLHS <- lhs
  keyword "="
  anRHS <- moduleRHS -- todo
  optionalEntrySep
  return $ Raw.GenuineEntry anLHS anRHS

{-
modul :: CanParse m => m Raw.Module
modul = do
  anEntry <- entry
  case anEntry of
    Raw.EntryModule aModule -> return aModule
    _ -> fail "Expected a module" -- TODO
-}

pseudoEntry :: CanParse m => m Raw.PseudoEntry
pseudoEntry = fail "Pseudos are not supported yet." --TODO

entry :: CanParse m => m Raw.Entry
entry = (Raw.EntryGenuine <$> genuineEntry) <|> (Raw.EntryPseudo <$>pseudoEntry)

file :: CanParse m => m Raw.File
file = MP.between manySpace MP.eof $ do
  pseudos <- many pseudoEntry
  themodule <- genuineEntry
  return $ Raw.File pseudos themodule
