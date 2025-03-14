{-# LANGUAGE OverloadedStrings #-}

module Frontend.ParsingMonad where

import Codec.Binary.UTF8.String
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS
import Data.ByteString.Lazy (ByteString)
import Data.Functor
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.Encoding (decodeUtf8)
import Data.Word (Word8)
import Frontend.Tokens
import Internal.Ast
import Numeric
import System.Exit (ExitCode (ExitFailure), exitWith)

-- Parsing Monad

data ParsingInfo = PInfo
  { defaultIntSize :: Int
  }

data ParsingState = PState
  { exprNextId :: Int,
    declIdents :: Set Text,
    alexInput :: AlexInput,
    declOps :: Map Text Size
  }

newtype Parsing a = Parsing (ExceptT String (RWS ParsingInfo ParsingWriter ParsingState) a)
  deriving (Functor, Applicative, Monad)

instance MonadFail Parsing where
  fail :: String -> Parsing a
  fail = Parsing . throwError

-- ParsingWriter Stuff

newtype ParsingWriter = PWriter (Ast)

instance Semigroup ParsingWriter where
  (<>) :: ParsingWriter -> ParsingWriter -> ParsingWriter
  PWriter (a) <> PWriter (b) =
    PWriter $
      Ast
        { exprs = exprs a <> exprs b,
          tagToId = tagToId a <> tagToId b,
          idToExpr = idToExpr a <> idToExpr b,
          idToTopLevel = idToTopLevel a <> idToTopLevel b
        }

instance Monoid ParsingWriter where
  mempty :: ParsingWriter
  mempty = PWriter $ Ast mempty mempty mempty mempty

-- Alex Stuff

data AlexInput
  = AlexInput
  { inpLastChar :: !Char,
    inpNextBytes :: ![Word8],
    inpStream :: !Text
  }
  deriving (Eq, Show)

advanceInput :: AlexInput -> AlexInput
advanceInput = id

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte inp@AlexInput {inpNextBytes = hd : tl} = Just (hd, inp {inpNextBytes = tl})
alexGetByte AlexInput {inpNextBytes = [], inpStream} = go <$> T.uncons inpStream
  where
    go (fstChr, remText) =
      let (fstByte, remBytes) = fromJust . List.uncons $ encodeChar fstChr
          newInput = AlexInput {inpLastChar = fstChr, inpNextBytes = remBytes, inpStream = remText}
       in (fstByte, advanceInput newInput)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = inpLastChar

getAlexInput :: Parsing AlexInput
getAlexInput = Parsing $ gets alexInput

setAlexInput :: AlexInput -> Parsing ()
setAlexInput newInput = Parsing . modify $ \s -> s {alexInput = newInput}

lexingFailure :: AlexInput -> Parsing a
lexingFailure AlexInput {inpLastChar, inpStream} =
  let txt = T.cons inpLastChar inpStream
      display = if T.length txt > 25 then T.take 25 txt <> "..." else txt
   in fail $ "Lexing Failure on: '" <> T.unpack display <> "'"

-- Lexer Stuff

readMaybe :: a -> ReadS a -> Text -> a
readMaybe def p s =
  case p $ T.unpack s of
    [(x, "")] -> x
    _ -> def

readParsing :: ReadS a -> Text -> Parsing a
readParsing p s =
  let str = T.unpack s
   in case p str of
        [(x, "")] -> return x
        _ -> fail $ "Parsing error on '" <> str <> "'"

parseVerilogInt :: Text -> Parsing Token
parseVerilogInt input = do
  defIntSize <- Parsing $ asks defaultIntSize
  case T.breakOn "'" input of
    (value, "") -> Number . VInteger (Size defIntSize) <$> readParsing readDec value
    (bitWidthText, rest) ->
      let bitWidth = Size $ readMaybe defIntSize readDec bitWidthText
          baseAndValue = T.drop 1 rest
          vInt = Number . VInteger bitWidth
       in vInt <$> case T.uncons baseAndValue of
            Just ('b', val) -> readParsing readBin val
            Just ('d', val) -> readParsing readDec val
            Just ('h', val) -> readParsing readHex val
            Just ('o', val) -> readParsing readOct val
            _ -> readParsing readDec baseAndValue

keywordMap :: Map Text KeyWord
keywordMap = Map.fromList . fmap (\kw -> (keywordToText kw, kw)) $ [minBound .. maxBound]

isKeyword :: Text -> Parsing Token
isKeyword t = case Map.lookup t keywordMap of
  Just kw -> return $ KeyWord kw
  Nothing -> return $ Ident t

token :: Token -> a -> Parsing Token
token = const . return

-- Parser Stuff

parseError :: Token -> Parsing a
parseError tok = fail $ "ParseError: Unexpected token '" <> show tok <> "'."

checkIdentUsed :: Text -> Parsing ()
checkIdentUsed name = do
  declIdent <- Parsing $ gets declIdents
  if Set.member name declIdent
    then
      fail $ "The name " <> T.unpack name <> " is already used."
    else Parsing . modify $ \s -> s {declIdents = Set.insert name (declIdents s)}

declareOperand :: Text -> VerilogInteger -> Parsing ()
declareOperand name (VInteger _ val) = checkIdentUsed name >> genOperand
  where
    genOperand :: Parsing ()
    genOperand = Parsing . modify $ \s -> s {declOps = Map.insert name (toEnum $ fromEnum val) (declOps s)}

declareExpr :: Text -> Expr -> Parsing ()
declareExpr name expr = checkIdentUsed name >> genExpr
  where
    genExpr :: Parsing ()
    genExpr =
      Parsing . tell $
        PWriter $
          Ast
            { exprs = Map.singleton (EName name) expr,
              idToExpr = mempty,
              idToTopLevel = Set.singleton (idFromExpr expr),
              tagToId = mempty
            }

declareTag :: Text -> Expr -> Parsing Expr
declareTag name expr = checkIdentUsed name >> genTag $> expr
  where
    genTag :: Parsing ()
    genTag =
      Parsing . tell $
        PWriter $
          Ast
            { exprs = mempty,
              idToExpr = mempty,
              idToTopLevel = mempty,
              tagToId = Map.singleton (ETag name) (idFromExpr expr)
            }

getOperand :: Text -> Parsing Operand
getOperand t =
  do
    declIdent <- Parsing $ gets declOps
    case Map.lookup t declIdent of
      Nothing -> fail $ "The operand '" <> T.unpack t <> "' is not declared."
      Just size -> return $ Op t size

inExpr :: ExprKind -> Parsing Expr
inExpr eKind = do
  exprId <- Parsing . state $ \s -> (EId $ exprNextId s, incrState s)
  let expr = E eKind exprId
   in (Parsing . tell $ addExprId exprId expr) $> expr
  where
    incrState pState@PState {exprNextId = eId} = pState {exprNextId = eId + 1}
    addExprId eId eExpr =
      PWriter $
        Ast
          { exprs = mempty,
            idToExpr = Map.singleton eId eExpr,
            idToTopLevel = mempty,
            tagToId = mempty
          }

parseOperand :: Text -> Parsing Expr
parseOperand = getOperand >=> inExpr . Operand

parseAssign :: Text -> AssignBinaryOp -> Expr -> Parsing Expr
parseAssign t op e = do
  o <- parseOperand t
  inExpr $ BinOpAssign o op e

parseShiftAssign :: Text -> ShiftBinaryOp -> Expr -> Parsing Expr
parseShiftAssign t op e = do
  o <- parseOperand t
  inExpr $ ShiftAssign o op e

runParsing :: Int -> Parsing () -> ByteString -> IO Ast
runParsing defaultIntSize (Parsing m) content =
  let initialPInfo = PInfo {defaultIntSize}
      alexInput = AlexInput {inpLastChar = '\n', inpNextBytes = [], inpStream = decodeUtf8 content}
      initialPState = PState {exprNextId = 0, declIdents = mempty, alexInput, declOps = mempty}
   in case runRWS (runExceptT m) initialPInfo initialPState of
        (Right (), _, (PWriter ast)) -> return $ ast
        (Left errMsg, _, _) -> putStrLn errMsg >> exitWith (ExitFailure 1)
