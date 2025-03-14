{-# LANGUAGE OverloadedStrings #-}

module Frontend.Tokens (KeyWord (..), keywordToText, Token (..)) where

import Ast (VerilogInteger)
import Data.Text.Lazy (Text)

data KeyWord
  = Inside
  | Var
  | Signed
  | Unsigned
  | Expr
  deriving (Show, Enum, Bounded)

keywordToText :: KeyWord -> Text
keywordToText Inside = "inside"
keywordToText Var = "var"
keywordToText Signed = "signed"
keywordToText Unsigned = "unsigned"
keywordToText Expr = "expr"

data Token
  = Eof
  | Ident Text
  | Number VerilogInteger
  | KeyWord KeyWord
  | OpenParen
  | CloseParen
  | Plus
  | Minus
  | Asterisk
  | Slash
  | Percent
  | Ampersand
  | Pipe
  | Caret
  | DoublePlus
  | DoubleMinus
  | Tilde
  | TripleEqual
  | ExclDoubleEqual
  | DoubleEqualQuest
  | ExclEqualQuest
  | DoubleEqual
  | ExclEqual
  | Lt
  | LtEqual
  | Gt
  | GtEqual
  | DoubleAmpersand
  | DoublePipe
  | RightArrow
  | EquivArrow
  | TildeAmpersand
  | TildePipe
  | TildeCaret
  | CaretTilde
  | Excl
  | TripleLt
  | TripleGt
  | DoubleLt
  | DoubleGt
  | DoubleAsterisk
  | Equal
  | PlusEqual
  | MinusEqual
  | AstEqual
  | SlashEqual
  | PercentEqual
  | AmpersandEqual
  | PipeEqual
  | CaretEqual
  | DoubleLtEqual
  | DoubleGtEqual
  | TripleLtEqual
  | TripleGtEqual
  | Quest
  | Colon
  | OpenBrace
  | CloseBrace
  | Comma
  | SemiColon
  | DoubleColon
  deriving (Show)
