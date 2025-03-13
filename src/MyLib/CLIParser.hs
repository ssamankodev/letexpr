{-#LANGUAGE NoImplicitPrelude#-}
{-#LANGUAGE TypeApplications#-}

module MyLib.CLIParser (CLIParserBundle, cliParserBundle, parserResult, Switches(..), CLI(..), SwitchRebind(..)) where

  import Prelude (undefined, Show(..), (++))
  import System.IO (IO, getContents, getContents', hGetLine, stdin)
  import System.Environment (getArgs)
  import Data.Text (Text)
  import qualified Data.Text as T
  import Data.Functor
  import Data.List (singleton)
  import Options.Applicative (ParserInfo(..), ParserPrefs(..), Parser(..), InfoMod(..), defaultPrefs, execParserPure, handleParseResult, liftA2, flag, long, short, help, (<*>), switch, some, info, strArgument, fullDesc, briefDesc, noIntersperse, (<|>), pure, switch, value)
  import MyLib.LetExpr
  import Data.Bool(Bool(..), not)
  import Data.Function(($), (.))
  import Data.Semigroup
  import Data.Either
  import Control.Monad
  import HsShellScript (isatty)


  -- --------------
  -- | Data Types |
  -- --------------

  {-
  A data type that holds the entire cli parser information and a function that will execute that parser on user input. This is so that I do not have to export a lot of the internals of this module.
  -}
  newtype CLIParserBundle = CLIParserBundle (ParserInfo CLI, ParserInfo CLI -> IO CLI)

  {-
  Data type that signifies the user's whole input, which are they choice of switches via Switches and the expressions via [Text].
  -}
  data CLI = CLI
    { switches :: Switches
    , expressions :: [Text]
    }
    deriving Show

  {-
  Newtype for Bool for user's input choice of enabling rebindable let-bindings.
  -}
  newtype SwitchRebind = SwitchRebind Bool
    deriving Show

  {-
  Data type that holds user's input choice of switches in regards to rebinding.
  -}
  data Switches = Switches
    {
      rebind :: SwitchRebind
    }
    deriving Show

  -- -------------------
  -- | CLIParserBundle |
  -- -------------------

  {-
  The pre-built CLIParserBundle that is to be exported.
  -}
  cliParserBundle :: CLIParserBundle
  cliParserBundle =
    let
      customExecParser :: ParserPrefs -> ParserInfo a -> IO a
      customExecParser pprefs pinfo = do
        --Reference: https://stackoverflow.com/questions/2564503/how-do-i-check-if-my-program-has-data-piped-into-it
        --Checks if the standard input handle is a tty or not
        pipedInput <- isatty stdin
        args <- getArgs
        --If it is a tty, then that means that the user is not piping in input and there is no content to get via getContents
        --If it is not a tty, then that means that the user is piping in input and I need to read it via getContents

        --Performance/Logic: I am reading input lazily via getContents instead of strictly via getContents' to enable more use-cases (e.g., extremely large files).
        if pipedInput
          then handleParseResult $ execParserPure pprefs pinfo args
          else getContents >>= handleParseResult . execParserPure pprefs pinfo . (args ++) . singleton

      {-
      The pre-built CLIParserBundle parser executor to be embedded into the pre-built CLIParserBundle.
      -}
      execParser :: ParserInfo a -> IO a
      execParser = customExecParser defaultPrefs
    in
    CLIParserBundle (cliProgramPI, execParser @CLI)

  {-
  The pre-built ParserInfo CLI value.
  -}
  cliProgramPI :: ParserInfo CLI
  cliProgramPI =
    let
      --Parser that trivially composes subparsers to parse a value of type 'CLI'.
      cliP :: Parser CLI
      cliP = CLI
        <$> switchesP
        <*> expressionsArgumentsP

      --Trivial implementation of InfoMod to satisfy ParserInfo requirements.
      --
      --NOTE: This is the description of 'noIntersperse' from optparse-applicative.
      ----Disable parsing of regular options after arguments. After a positional argument is parsed, all remaining options and arguments will be treated as a positional arguments. Not recommended in general as users often expect to be able to freely intersperse regular options and flags within command line options.
      cliParserInfo :: InfoMod a
      cliParserInfo = fullDesc
        <> briefDesc
        <> noIntersperse
    in
    info cliP cliParserInfo

  parserResult :: CLIParserBundle -> IO CLI
  parserResult (CLIParserBundle (a, b)) = b a

  -- --------------------
  -- | Switches Parsers |
  -- --------------------

  {-
  Parser that trivially composes subparsers to parse a value of type 'Switches'.
  -}
  switchesP :: Parser Switches
  switchesP = Switches
    <$> rebindSwitchP

  {-
  This is a Parser that parses only one of 'reference' flags: none ("--no-reference").
  -}
  referenceSwitchP :: Parser Bool
  referenceSwitchP =
    let
      switchNone = switch $
           long "no-reference"
        <> help "Let expressions cannot reference each other and can only be referenced by the final expression"
    in switchNone

  rebindSwitchP :: Parser SwitchRebind
  rebindSwitchP = fmap SwitchRebind . switch $
       long "rebind"
    <> help "Enable variable shadowing of let binding variables"

  -- ---------------------
  -- | Expression Parser |
  -- ---------------------

  expressionsArgumentsP :: Parser [Text]
  expressionsArgumentsP = some (strArgument (help "Expression to beta reduce with the preceding let bindings"))
