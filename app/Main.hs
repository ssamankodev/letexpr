{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

  import Data.Foldable (traverse_)
  import Data.Bifunctor
  import Data.Text
  import qualified Data.Text.IO as T
  import System.Exit
  import Data.List.NonEmpty (NonEmpty)
  import qualified Data.List.NonEmpty as NE
  import MyLib

  main :: IO ()
  main = do
    result <- parserResult cliParserBundle
    let
      vRebind = case result of
        (CLI (Switches (SwitchRebind reb)) _) -> reb
      vExprs = case result of
        (CLI _ exprs) -> exprs
    if vRebind
    then case linearReferenceLetExprParse vExprs of
      Just validSyntax -> case linearUnfoldIndexValuesTrie validSyntax of
        Left value -> case validateRecursionLetBindingTypesContainer . mapLetBindings (eitherLetBindingToLetBindingEither . first identifyVariablesContainer . letBindingEitherToEitherLetBinding) $ first (\(a, b) -> first (\(x, y) -> (x, y, b)) a) value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Implement printing of invalid recursive LetBindingTypes
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let
                getMostRecentFirstOfPair :: Bifunctor b => b (Either (x, y) (NonEmpty (x, y))) c -> b x c
                getMostRecentFirstOfPair = first (fst . eitherValue . second NE.head)
            let simplifiedFinalExprValidLetExpr = bimap getMostRecentFirstOfPair (eitherValue . bimap (getMostRecentFirstOfPair . snd) (ContainerSingle . ContainerSingleValue)) validLetExpr
            mapM_ T.putStr . uncurry betaReduceContainer $ letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            T.putStrLn Data.Text.empty
        Right value -> case validateRecursionLetBindingTypesContainer . mapLetBindings (eitherLetBindingToLetBindingEither . first identifyVariablesContainer . letBindingEitherToEitherLetBinding) $ first (\(a, b) -> first (\(x, y) -> (x, y, b)) a) value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Replace print with actual formatted error message
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let simplifiedFinalExprValidLetExpr = bimap (first fst) (eitherValue . bimap (first fst . snd) (ContainerSingle . ContainerSingleValue)) validLetExpr
            mapM_ T.putStr . uncurry betaReduceContainer $ letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            T.putStrLn Data.Text.empty
      Nothing -> case mutualReferenceLetExprParse vExprs of
        Just validSyntax -> case mutualUnfoldIndexValuesTrie validSyntax of
          Left value -> do
            T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid."
            T.putStrLn ""
            traverse_ (mapM_ T.putStrLn) . invalidRebindMessage $ fmap (fmap (fmap snd)) value
          Right value -> case validateRecursionLetBindingTypesContainer . mapLetBindings (eitherLetBindingToLetBindingEither . first identifyVariablesContainer . letBindingEitherToEitherLetBinding) $ first (\(a, b) -> first (\(x, y) -> (x, y, b)) a) value of
            Left invalidRecursions -> do
              T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
              --TODO: Replace print with actual formatted error message
              --print invalidRecursions
              T.putStrLn Data.Text.empty
            Right validLetExpr -> do
              let simplifiedFinalExprValidLetExpr = bimap (first fst) (eitherValue . bimap (first fst . snd) (ContainerSingle . ContainerSingleValue)) validLetExpr
              mapM_ T.putStr . uncurry betaReduceContainer $ letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
              T.putStrLn Data.Text.empty
        Nothing -> do
          putStrLn "[Error]: Input was not syntactically valid."
          exitFailure
    else case linearReferenceLetExprParse vExprs of
      Just validSyntax -> case linearUnfoldIndexValuesTrie validSyntax of
        Left value -> do
          --Get the final let binding, which will contain a cumulative Trie of all let bindings
          let finalTrie = snd . NE.last $ letExprLetBindingValues value
          let
            getRight (Right b) = Just $ fmap snd b
            getRight _ = Nothing

          T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid when the 'rebind' switch is not provided."
          T.putStrLn ""
          traverse_ (mapM_ T.putStrLn) . invalidRebindMessage . trieLBToLetBindings $ filterMapTrieLB getRight finalTrie
        Right value -> case validateRecursionLetBindingTypesContainer . mapLetBindings (eitherLetBindingToLetBindingEither . first identifyVariablesContainer . letBindingEitherToEitherLetBinding) $ first (\(a, b) -> first (\(x, y) -> (x, y, b)) a) value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Replace print with actual formatted error message
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let simplifiedFinalExprValidLetExpr = bimap (first fst) (eitherValue . bimap (first fst . snd) (ContainerSingle . ContainerSingleValue)) validLetExpr
            mapM_ T.putStr . uncurry betaReduceContainer $ letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            T.putStrLn Data.Text.empty
      Nothing -> case mutualReferenceLetExprParse vExprs of
        Just validSyntax -> case mutualUnfoldIndexValuesTrie validSyntax of
          Left value -> do
            T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid."
            T.putStrLn ""
            traverse_ (mapM_ T.putStrLn) . invalidRebindMessage $ fmap (fmap (fmap snd)) value
          Right value -> case validateRecursionLetBindingTypesContainer . mapLetBindings (eitherLetBindingToLetBindingEither . first identifyVariablesContainer . letBindingEitherToEitherLetBinding) $ first (\(a, b) -> first (\(x, y) -> (x, y, b)) a) value of
            Left invalidRecursions -> do
              T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
              --TODO: Replace print with actual formatted error message
              --print invalidRecursions
              T.putStrLn Data.Text.empty
            Right validLetExpr -> do
              let simplifiedFinalExprValidLetExpr = bimap (first fst) (eitherValue . bimap (first fst . snd) (ContainerSingle . ContainerSingleValue)) validLetExpr
              mapM_ T.putStr . uncurry betaReduceContainer $ letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
              T.putStrLn Data.Text.empty
        Nothing -> do
          putStrLn "[Error]: Input was not syntactically valid."
          exitFailure
