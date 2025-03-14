{

module Frontend.Parser (parser) where

import Ast
import Data.ByteString.Lazy (ByteString)
import Data.Foldable
import Data.Text.Lazy (Text)
import Frontend.Lexer qualified as L
import Frontend.ParsingMonad
import Frontend.Reversed
import Frontend.Tokens qualified as T

}

%expect 0 -- shift/reduce conflicts

%name parser file
%tokentype { T.Token }
%error { parseError }
%monad { Parsing } { >>= } { return }
%lexer { L.lexer } { T.Eof }

%token ident       { T.Ident $$ }
%token int         { T.Number $$ }
%token 'inside'    { T.KeyWord T.Inside }
%token 'signed'    { T.KeyWord T.Signed }
%token 'unsigned'  { T.KeyWord T.Unsigned }
%token 'var'       { T.KeyWord T.Var }
%token 'expr'      { T.KeyWord T.Expr }

%token '<<<='          { T.TripleLtEqual }
%token '>>>='          { T.TripleGtEqual }

%token '==='           { T.TripleEqual }
%token '!=='           { T.ExclDoubleEqual }
%token '==?'           { T.DoubleEqualQuest }
%token '!=?'           { T.ExclEqualQuest }
%token '<<<'           { T.TripleLt }
%token '>>>'           { T.TripleGt }
%token '<<='           { T.DoubleLtEqual }
%token '>>='           { T.DoubleGtEqual }
%token '<->'           { T.EquivArrow }

%token '++'            { T.DoublePlus }
%token '--'            { T.DoubleMinus }
%token '=='            { T.DoubleEqual }
%token '!='            { T.ExclEqual }
%token '<='            { T.LtEqual }
%token '>='            { T.GtEqual }
%token '&&'            { T.DoubleAmpersand }
%token '||'            { T.DoublePipe }
%token '->'            { T.RightArrow }
%token '~&'            { T.TildeAmpersand }
%token '~|'            { T.TildePipe }
%token '~^'            { T.TildeCaret }
%token '^~'            { T.CaretTilde }
%token '<<'            { T.DoubleLt }
%token '>>'            { T.DoubleGt }
%token '**'            { T.DoubleAsterisk }
%token '+='            { T.PlusEqual }
%token '-='            { T.MinusEqual }
%token '*='            { T.AstEqual }
%token '/='            { T.SlashEqual }
%token '%='            { T.PercentEqual }
%token '&='            { T.AmpersandEqual }
%token '|='            { T.PipeEqual }
%token '^='            { T.CaretEqual }
%token '::'            { T.DoubleColon }

%token '('             { T.OpenParen }
%token ')'             { T.CloseParen }
%token '+'             { T.Plus }
%token '-'             { T.Minus }
%token '*'             { T.Asterisk }
%token '/'             { T.Slash }
%token '%'             { T.Percent }
%token '&'             { T.Ampersand }
%token '|'             { T.Pipe }
%token '^'             { T.Caret }
%token '~'             { T.Tilde }
%token '<'             { T.Lt }
%token '>'             { T.Gt }
%token '!'             { T.Excl }
%token '='             { T.Equal }
%token '?'             { T.Quest }
%token ':'             { T.Colon }
%token '{'             { T.OpenBrace }
%token '}'             { T.CloseBrace }
%token ';'             { T.SemiColon }
%token ','             { T.Comma }


%left '=' '+=' '-=' '*=' '/=' '%=' '&=' '|=' '^=' '<<=' '<<<=' '>>=' '>>>='
%left '->' '<->'
%right '?' ':'
%left '||'
%left '&&'
%left '|'
%left '^' '~^' '^~'
%left '&'
%left '==' '!=' '===' '!==' '==?' '!=?'
%left '<' '<=' '>' '>=' 'inside'
%left '<<' '>>' '<<<' '>>>'
%left '+' '-'
%left '*' '/' '%'
%left '**'
%nonassoc UNARY '!' '~' '~&' '~|' '++' '--'

%%

file
  : decl                              { () }
  | file decl                         { () }

decl :: { () }
  : 'var' ident ':' int               {% declareOperand $2 $4 }
  | 'expr' ident ':' expr             {% declareExpr $2 $4 }

expr :: { Expr }
  : atomicExpr                        { $1 }
  | unOpExpr                          { $1 }
  | binOpExpr                         { $1 }
  | expr '?' expr ':' expr            {% inExpr $ Conditional $1 $3 $5 }
  | atomicExpr 'inside' exprRange     {% inExpr $ Inside $1 $3 }

atomicExpr :: { Expr }
  : ident                             {% parseOperand $1 }
  | int                               {% inExpr $ IntegerValue $1 }
  | '(' expr ')'                      { $2 }
  | '(' ident '::' expr ')'           {% declareTag $2 $4 }
  | exprRange                         {% inExpr $ Concat $1 }
  | '{' int exprRange '}'             {% inExpr $ ReplConcat (fromEnum $ value $2) $3 }
  | '(' ident binOpAssign expr ')'    {% parseAssign $2 $3 $4 }
  | '(' ident shiftOpAssign expr ')'  {% parseShiftAssign $2 $3 $4 }
  | 'signed' '(' expr ')'             {% inExpr $ (Cast Signed) $3 }
  | 'unsigned' '(' expr ')'           {% inExpr $ (Cast Unsigned) $3 }

unOpExpr :: { Expr }
  : '+'  atomicExpr   %prec UNARY     { $2 }
  | '-'  atomicExpr   %prec UNARY     {% inExpr $ (PreUnOp Negate) $2 }
  | '++' atomicExpr                   {% inExpr $ (PreUnOp PreIncr) $2 }
  | '--' atomicExpr                   {% inExpr $ (PreUnOp PreDecr) $2 }
  | '~'  atomicExpr                   {% inExpr $ (PreUnOp Invert) $2 }
  | '!'  atomicExpr                   {% inExpr $ LogicNot $2 }
  | atomicExpr '++'                   {% inExpr $ (PostUnOp PostIncr) $1 }
  | atomicExpr '--'                   {% inExpr $ (PostUnOp PostDecr) $1 }
  | '&'  atomicExpr   %prec UNARY     {% inExpr $ (Reduction RedAnd) $2 }
  | '~&' atomicExpr                   {% inExpr $ (Reduction RedNand) $2 }
  | '|'  atomicExpr   %prec UNARY     {% inExpr $ (Reduction RedOr) $2 }
  | '~|' atomicExpr                   {% inExpr $ (Reduction RedNor) $2 }
  | '^'  atomicExpr   %prec UNARY     {% inExpr $ (Reduction RedXor) $2 }
  | '~^' atomicExpr   %prec UNARY     {% inExpr $ (Reduction RedNxor) $2 }
  | '^~' atomicExpr   %prec UNARY     {% inExpr $ (Reduction RedNxor) $2 }


binOpExpr :: { Expr }
  : expr '+' expr                     {% inExpr $ (Arithmetic Addition) $1 $3 }
  | expr '-' expr                     {% inExpr $ (Arithmetic Subtraction) $1 $3 }
  | expr '*' expr                     {% inExpr $ (Arithmetic Multiplication) $1 $3 }
  | expr '/' expr                     {% inExpr $ (Arithmetic Division) $1 $3 }
  | expr '%' expr                     {% inExpr $ (Arithmetic Remainder) $1 $3 }
  | expr '**' expr                    {% inExpr $ Pow $1 $3 }
  | expr '&' expr                     {% inExpr $ (Arithmetic BinaryAnd) $1 $3 }
  | expr '|' expr                     {% inExpr $ (Arithmetic BinaryOr) $1 $3 }
  | expr '^' expr                     {% inExpr $ (Arithmetic BinaryXor) $1 $3 }
  | expr '~^' expr                    {% inExpr $ (Arithmetic BinaryNXor) $1 $3 }
  | expr '^~' expr                    {% inExpr $ (Arithmetic BinaryNXor) $1 $3 }
  | expr '<' expr                     {% inExpr $ (Comparison Lt) $1 $3 }
  | expr '<=' expr                    {% inExpr $ (Comparison Le) $1 $3 }
  | expr '>' expr                     {% inExpr $ (Comparison Gt) $1 $3 }
  | expr '>=' expr                    {% inExpr $ (Comparison Ge) $1 $3 }
  | expr '==' expr                    {% inExpr $ (Comparison Eq) $1 $3 }
  | expr '!=' expr                    {% inExpr $ (Comparison Neq) $1 $3 }
  | expr '==?' expr                   {% inExpr $ (Comparison WildEq) $1 $3 }
  | expr '!=?' expr                   {% inExpr $ (Comparison WildNeq) $1 $3 }
  | expr '===' expr                   {% inExpr $ (Comparison StrictEq) $1 $3 }
  | expr '!==' expr                   {% inExpr $ (Comparison StrictNeq) $1 $3 }
  | expr '&&' expr                    {% inExpr $ (Logic And) $1 $3 }
  | expr '||' expr                    {% inExpr $ (Logic Or) $1 $3 }
  | expr '->' expr                    {% inExpr $ (Logic Impl) $1 $3 }
  | expr '<->' expr                   {% inExpr $ (Logic Equiv) $1 $3 }
  | expr '>>' expr                    {% inExpr $ (Shift LogicRight) $1 $3 }
  | expr '>>>' expr                   {% inExpr $ (Shift ArithRight) $1 $3 }
  | expr '<<' expr                    {% inExpr $ (Shift LogicLeft) $1 $3 }
  | expr '<<<' expr                   {% inExpr $ (Shift ArithLeft) $1 $3 }

binOpAssign
  : '='                               { None }
  | '+='                              { AdditionAssign }
  | '-='                              { SubtractionAssign }
  | '*='                              { MultiplicationAssign }
  | '/='                              { DivisionAssign }
  | '%='                              { RemainderAssign }
  | '&='                              { LogicalAndAssign }
  | '|='                              { LogicalOrAssign }
  | '^='                              { LogicalXorAssign }

shiftOpAssign
  : '>>='                             { LogicRight }
  | '>>>='                            { ArithRight }
  | '<<='                             { LogicLeft }
  | '<<<='                            { ArithLeft }

exprRange
  : '{' '}'                           { [] }
  | '{' exprList '}'                  { toList $2 }

exprList
  : expr                              { singleton $1 }
  | exprList ',' expr                 { $1 :> $3 }


{

}