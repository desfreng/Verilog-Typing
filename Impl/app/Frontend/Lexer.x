{

module Frontend.Lexer (lexer) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Frontend.ParsingMonad
import Frontend.Tokens

}

%encoding "utf8"

@ident = [a-zA-Z_\$][a-zA-Z0-9_\$]*

$num = [0-9]
$base = [bohd]
$digit = [0-9a-fA-F]

@number = ($num*\'$base)?$digit+

tokens :-

-- Whitespace insensitive
$white+                 ;

-- One line comments
"#".*                   ;

-- Syntax

@ident                  { isKeyword }
@number                 { parseVerilogInt }

"<<<="                  { token TripleLtEqual }
">>>="                  { token TripleGtEqual }

"==="                   { token TripleEqual }
"!=="                   { token ExclDoubleEqual }
"==?"                   { token DoubleEqualQuest }
"!=?"                   { token ExclEqualQuest }
"<<<"                   { token TripleLt }
">>>"                   { token TripleGt }
"<<="                   { token DoubleLtEqual }
">>="                   { token DoubleGtEqual }
"<->"                   { token EquivArrow }

"++"                    { token DoublePlus }
"--"                    { token DoubleMinus }
"=="                    { token DoubleEqual }
"!="                    { token ExclEqual }
"<="                    { token LtEqual }
">="                    { token GtEqual }
"&&"                    { token DoubleAmpersand }
"||"                    { token DoublePipe }
"->"                    { token RightArrow }
"~&"                    { token TildeAmpersand }
"~|"                    { token TildePipe }
"~^"                    { token TildeCaret }
"^~"                    { token CaretTilde }
"<<"                    { token DoubleLt }
">>"                    { token DoubleGt }
"**"                    { token DoubleAsterisk }
"+="                    { token PlusEqual }
"-="                    { token MinusEqual }
"*="                    { token AstEqual }
"/="                    { token SlashEqual }
"%="                    { token PercentEqual }
"&="                    { token AmpersandEqual }
"|="                    { token PipeEqual }
"^="                    { token CaretEqual }
"::"                    { token DoubleColon }

"("                     { token OpenParen }
")"                     { token CloseParen }
"+"                     { token Plus }
"-"                     { token Minus }
"*"                     { token Asterisk }
"/"                     { token Slash }
"%"                     { token Percent }
"&"                     { token Ampersand }
"|"                     { token Pipe }
"^"                     { token Caret }
"~"                     { token Tilde }
"<"                     { token Lt }
">"                     { token Gt }
"!"                     { token Excl }
"="                     { token Equal }
"?"                     { token Quest }
":"                     { token Colon }
"{"                     { token OpenBrace }
"}"                     { token CloseBrace }
","                     { token Comma }

{

lexer :: (Token -> Parsing a) -> Parsing a
lexer cont = do
  alexIn <- getAlexInput
  case alexScan alexIn 0 of
    AlexEOF -> cont Eoi
    AlexError lastInput -> lexingFailure lastInput
    AlexSkip newInput _ -> setAlexInput newInput >> lexer cont
    AlexToken newInput len act ->
      let text = T.take (toEnum len) (inpStream alexIn)
       in setAlexInput newInput >> act text >>= cont

}