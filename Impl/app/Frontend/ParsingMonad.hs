{-# LANGUAGE OverloadedStrings #-}

module Frontend.ParsingMonad where

import Codec.Binary.UTF8.String
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable1 (Foldable1 (toNonEmpty))
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Word (Word8)
import Expr
import Frontend.Reversed
import Frontend.Tokens
import Model
import Numeric

-- Parsing Monad

type ParsingRead = Int

data ParsingState = PS
  { alexState :: AlexInput,
    declsTags :: Map ExprTag ExprId
  }

newtype Parsing a = Parsing (ExceptT String (ReaderT ParsingRead (StateT ParsingState Model)) a)
  deriving (Functor, Applicative, Monad)

instance MonadFail Parsing where
  fail :: String -> Parsing a
  fail = Parsing . throwError

toParsing :: Model a -> Parsing a
toParsing = Parsing . lift . lift . lift

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
getAlexInput = Parsing $ gets alexState

setAlexInput :: AlexInput -> Parsing ()
setAlexInput aState = Parsing . modify $ \s -> s {alexState = aState}

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
  bSize <- Parsing $ ask
  case T.breakOn "'" input of
    (value, "") -> Number . VInteger (Size bSize) <$> readParsing readDec value
    (bitWidthText, rest) ->
      let bitWidth = Size $ readMaybe bSize readDec bitWidthText
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

declareOperand :: Text -> VerilogInteger -> Parsing ()
declareOperand name size =
  let op = Op name . Size . fromEnum $ value size
   in do
        res <- toParsing $ addOperand op
        case res of
          Error -> fail $ "This operand is already declared: '" <> show name <> "'."
          Success -> return ()

declareExpr :: Text -> Expr -> Parsing ()
declareExpr eName e = do
  tags <- Parsing $ gets declsTags
  res <- toParsing $ addNamedExpr eName e tags
  case res of
    Error -> fail $ "This expression is already declared: '" <> show eName <> "'."
    Success -> Parsing . modify $ \s -> s {declsTags = mempty}

declareTag :: Text -> Expr -> Parsing Expr
declareTag name expr = do
  tagId <- toParsing (isTagUsed name)
  case tagId of
    Nothing -> tagAlreadyDeclared
    Just t -> do
      inDeclTags <- Parsing . gets $ Map.member t . declsTags
      if inDeclTags
        then tagAlreadyDeclared
        else do
          () <- Parsing . modify $ \s -> s {declsTags = Map.insert t (exprId expr) $ declsTags s}
          return expr
  where
    tagAlreadyDeclared :: Parsing a
    tagAlreadyDeclared = fail $ "The tag '" <> show name <> "' is already declared."

getOperand :: Text -> Parsing Operand
getOperand t =
  do
    op <- toParsing $ findOperand t
    case op of
      Nothing -> fail $ "The operand '" <> T.unpack t <> "' is not declared."
      Just o -> return o

inExpr :: ExprKind -> Parsing Expr
inExpr = toParsing . buildExpr

buildLeftValue :: Expr -> Parsing LeftValue
buildLeftValue e = go $ exprKind e
  where
    go (Operand op) = toParsing . buildLValue $ LeftAtom op
    go (UnaryConcat arg) = do
      lArg <- buildLeftValue arg
      toParsing . buildLValue $ LeftConcat (NE.singleton lArg) (leftSize lArg)
    go (BinaryConcat lhs rhs) = do
      lLhs <- buildLeftValue lhs
      lRhs <- buildLeftValue rhs
      let finalSize = leftSize lLhs + leftSize lRhs
      toParsing . buildLValue $ LeftConcat (lLhs NE.:| [lRhs]) finalSize
    go _ = fail "This is not a left value."

parseOperand :: Text -> Parsing Expr
parseOperand = getOperand >=> inExpr . Operand

parseConcat :: Reversed Expr -> Parsing Expr
parseConcat = go . toNonEmpty
  where
    go (x NE.:| []) = inExpr $ UnaryConcat x
    go (x NE.:| y : l) = goBinary x y l

    goBinary x y [] = inExpr $ BinaryConcat x y
    goBinary x y (z : l) = goBinary y z l >>= inExpr . BinaryConcat x

parseRepl :: VerilogInteger -> Reversed Expr -> Parsing Expr
parseRepl v l = parseConcat l >>= inExpr . Repl (fromEnum $ value v)

parseInside :: Expr -> Reversed Expr -> Parsing Expr
parseInside arg = inExpr . Expr.Inside arg . toNonEmpty

parseAssign :: Expr -> AssignBinaryOp -> Expr -> Parsing Expr
parseAssign t op e = do
  lhs <- buildLeftValue t
  inExpr $ BinOpAssign lhs op e

parseShiftAssign :: Expr -> ShiftBinaryOp -> Expr -> Parsing Expr
parseShiftAssign t op e = do
  lhs <- buildLeftValue t
  inExpr $ ShiftAssign lhs op e

runParser :: Parsing a -> Text -> (a -> ParsingState -> Model (Maybe String)) -> Model (Maybe String)
runParser (Parsing m) content f =
  let alexInput = AlexInput {inpLastChar = '\n', inpNextBytes = [], inpStream = content}
      initS = PS {alexState = alexInput, declsTags = mempty}
      defaultIntSize = 32
   in do
        (res, s) <- runStateT (runReaderT (runExceptT m) defaultIntSize) initS
        case res of
          Left errorStr -> return $ Just errorStr
          Right x -> f x s

runExprParser :: Parsing Expr -> Text -> Model (Maybe String)
runExprParser m content = runParser m content $ \e s -> addExpr e (declsTags s) >> return Nothing

runFileParser :: Parsing () -> Text -> Model (Maybe String)
runFileParser m content = runParser m content $ \() _ -> return Nothing
