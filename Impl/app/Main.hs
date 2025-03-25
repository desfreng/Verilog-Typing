{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Context.Graph
import Data.ByteString.Lazy qualified as B
import Data.GraphViz.Commands qualified as C
import Data.GraphViz.Types
import Data.GraphViz.Types.Monadic (Dot, digraph')
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Encoding qualified as TEnc
import Data.Text.Lazy.IO qualified as TIO
import Expr
import Frontend.Parser
import Frontend.ParsingMonad
import Graph (exprToGraph)
import Model
import Options.Applicative
import System.Exit (ExitCode (..), exitWith)

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
                    <> metavar "FILE"
                    <> help "Export to file"
                )
          )
            <|> pure Nothing
        )

main :: IO ()
main = do
  C.quitWithoutGraphviz "Graphviz must be installed."
  options <- execParser opts
  fileContent <- TEnc.decodeUtf8 <$> readInputFile (inputFile options)
  let model = runFileParser parseFile fileContent
  runModel $ do
    res <- model
    case res of
      Just x -> return $ putStrLn x >> exitWith (ExitFailure 1)
      Nothing -> case compilerAction options of
        ShowAst -> forEachExpr (showFileAst $ exportDot options)
        ShowContext -> forEachExpr (showFileContext $ exportDot options)
  where
    opts = info (compilerOptionsParser <**> helper) fullDesc

    readInputFile "-" = B.getContents
    readInputFile file = B.readFile file

runDot :: Maybe FilePath -> Dot Text -> IO ()
runDot Nothing g = C.runGraphvizCanvas C.Dot (digraph' g) C.Xlib
runDot (Just "-") g = TIO.putStrLn $ printDotGraph (digraph' g)
runDot (Just f) g = C.runGraphvizCommand C.Dot (digraph' g) C.Pdf f >> pure ()

showFileAst :: Maybe FilePath -> ExprName -> Expr -> IO ()
showFileAst out eName e = runDot out $ exprToGraph eName e

showFileContext :: Maybe FilePath -> ExprName -> Expr -> IO ()
showFileContext out eName e = runDot out $ contextGraphs eName e
