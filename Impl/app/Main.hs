{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Ast
import Context (contextToGraphs)
import Data.ByteString.Lazy qualified as B
import Data.GraphViz.Commands
import Data.GraphViz.Types (printDotGraph)
import Data.GraphViz.Types.Generalised (DotGraph)
import Data.Map.Strict qualified as Map
import Data.Text.Lazy.IO qualified as TIO
import Frontend.Parser
import Frontend.ParsingMonad (runParsing)
import Graph (exprToGraph)
import Options.Applicative

data Action = ShowAst | ShowContext

data CompilerOptions = CompilerOptions
  { compilerAction :: Action,
    inputFile :: FilePath,
    exportDot :: Maybe FilePath
  }

compilerOptionsParser :: Parser CompilerOptions
compilerOptionsParser =
  CompilerOptions
    <$> ( flag' ShowAst (long "show-ast" <> help "Show parsed expressions")
            <|> flag' ShowContext (long "show-ctx" <> help "Show contexts")
        )
    <*> argument str (metavar "FILE" <> help "Input source file to compile")
    <*> ( ( Just
              <$> strOption
                ( long "export"
                    <> metavar "DOT"
                    <> help "Export Dot file"
                )
          )
            <|> pure Nothing
        )

main :: IO ()
main = do
  options <- execParser opts
  ast <- readInputFile (inputFile options) >>= runParsing 32 parser
  case compilerAction options of
    ShowAst -> showFileAst (exportDot options) ast
    ShowContext -> showFileContext (exportDot options) ast
  where
    opts = info (compilerOptionsParser <**> helper) fullDesc

    readInputFile "-" = B.getContents
    readInputFile file = B.readFile file

runDot :: Maybe FilePath -> DotGraph ExprId -> IO ()
runDot Nothing g = runGraphvizCanvas Dot g Xlib
runDot (Just "-") g = TIO.putStrLn $ printDotGraph g
runDot (Just f) g = TIO.writeFile f $ printDotGraph g

showFileAst :: Maybe FilePath -> Ast -> IO ()
showFileAst out = Map.foldMapWithKey (\eName e -> runDot out $ exprToGraph eName e) . astExprs

showFileContext :: Maybe FilePath -> Ast -> IO ()
showFileContext out = Map.foldMapWithKey (\eName e -> runDot out $ contextToGraphs eName e) . astExprs
