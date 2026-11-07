module Lexer (
    Token(..),
    AlexPosn(..),
    alexScanTokens,
    prettyTok,
    prettyAlexPosn
) where

import Data.Char (isAlpha, isDigit, isSpace)

data AlexPosn = AlexPn !Int !Int !Int
    deriving (Eq, Show)

data Token = Id String AlexPosn
           | Sized AlexPosn
           | Data AlexPosn
           | CoData AlexPosn
           | Mutual AlexPosn
           | Fun AlexPosn
           | CoFun AlexPosn
           | Let AlexPosn
           | In AlexPosn
           | Set AlexPosn
           | Eval AlexPosn
           -- size type
           | Size AlexPosn
           | Infty AlexPosn
           | Succ AlexPosn
           --
           | BrOpen AlexPosn
           | BrClose AlexPosn
           | PrOpen AlexPosn
           | PrClose AlexPosn
           | Sem AlexPosn
           | Col AlexPosn
           | Dot AlexPosn
           | Arrow AlexPosn
           | Eq AlexPosn
           | Plus AlexPosn
           | Lam AlexPosn
           | NotUsed AlexPosn
             deriving (Eq, Show)

prettyTok :: Token -> String
prettyTok c = "\"" ++ tk ++ "\" at " ++ prettyAlexPosn pos where
  (tk,pos) = case c of
    Id s p    -> (show s, p)
    Sized p   -> ("sized", p)
    Data p    -> ("data", p)
    CoData p  -> ("codata", p)
    Mutual p  -> ("mutual", p)
    Fun p     -> ("fun", p)
    CoFun p   -> ("cofun", p)
    Let p     -> ("let", p)
    In p      -> ("in", p)
    Eval p    -> ("eval", p)
    Set p     -> ("Set", p)
    Size p    -> ("Size", p)
    Infty p   -> ("#", p)
    Succ p    -> ("$", p)
    BrOpen p  -> ("{", p)
    BrClose p -> ("}", p)
    PrOpen p  -> ("(", p)
    PrClose p -> (")", p)
    Sem p     -> (";", p)
    Col p     -> (":", p)
    Dot p     -> (".", p)
    Arrow p   -> ("->", p)
    Eq p      -> ("=", p)
    Plus p    -> ("+", p)
    Lam p     -> ("\\", p)
    NotUsed p -> ("not used", p)

prettyAlexPosn :: AlexPosn -> String
prettyAlexPosn (AlexPn _ line col) = "line " ++ show line ++ ", row " ++ show col

advanceChar :: AlexPosn -> Char -> AlexPosn
advanceChar (AlexPn off line col) '\n' = AlexPn (off + 1) (line + 1) 1
advanceChar (AlexPn off line col) '\t' = AlexPn (off + 1) line (((col - 1 + 8) `div` 8) * 8 + 1)
advanceChar (AlexPn off line col) _    = AlexPn (off + 1) line (col + 1)

advanceStr :: AlexPosn -> String -> AlexPosn
advanceStr = foldl advanceChar

isIdentChar :: Char -> Bool
isIdentChar c = isAlpha c || isDigit c || c == '_' || c == '\''

alexScanTokens :: String -> [Token]
alexScanTokens = go (AlexPn 0 1 1)
  where
    go _ [] = []
    go p (c:cs)
      | isSpace c = go (advanceChar p c) cs
    go p ('-':'-':cs) =
      let (lineComment, rest) = span (/= '\n') cs
      in go (advanceStr (advanceStr p "--") lineComment) rest
    go p ('{':'-':cs) =
      skipBlockComment (advanceStr p "{-") cs
    go p ('-':'>':cs) =
      Arrow p : go (advanceStr p "->") cs
    go p (c:cs) =
      case c of
        '#'  -> Infty p   : go (advanceChar p c) cs
        '$'  -> Succ p    : go (advanceChar p c) cs
        '{'  -> BrOpen p  : go (advanceChar p c) cs
        '}'  -> BrClose p : go (advanceChar p c) cs
        '('  -> PrOpen p  : go (advanceChar p c) cs
        ')'  -> PrClose p : go (advanceChar p c) cs
        ';'  -> Sem p     : go (advanceChar p c) cs
        ':'  -> Col p     : go (advanceChar p c) cs
        '.'  -> Dot p     : go (advanceChar p c) cs
        '+'  -> Plus p    : go (advanceChar p c) cs
        '='  -> Eq p      : go (advanceChar p c) cs
        '\\' -> Lam p     : go (advanceChar p c) cs
        _ | isIdentChar c ->
              let (ident, rest) = span isIdentChar (c:cs)
                  tok = classifyIdent p ident
              in tok : go (advanceStr p ident) rest
          | otherwise ->
              error ("Lexical error at " ++ prettyAlexPosn p ++ ": unexpected character " ++ show c)

    skipBlockComment p [] = error ("Unterminated block comment at " ++ prettyAlexPosn p)
    skipBlockComment p ('-':'}':cs) = go (advanceStr p "-}") cs
    skipBlockComment p (c:cs) = skipBlockComment (advanceChar p c) cs

    classifyIdent p s = case s of
      "sized"  -> Sized p
      "data"   -> Data p
      "codata" -> CoData p
      "fun"    -> Fun p
      "cofun"  -> CoFun p
      "let"    -> Let p
      "const"  -> Let p
      "in"     -> In p
      "eval"   -> Eval p
      "mutual" -> Mutual p
      "Set"    -> Set p
      "Size"   -> Size p
      _        -> Id s p
