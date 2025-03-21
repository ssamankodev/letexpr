{-# LANGUAGE OverloadedStrings #-}

module Main where

  import Data.Foldable (traverse_)
  import Data.Bifunctor
  import Data.List.NonEmpty (NonEmpty(..))
  import Data.Text
  import qualified Data.Text.IO as T
  import System.Exit
  import System.IO (getContents', getLine, hGetContents', stdin, hGetContents)
  import System.Environment (getArgs, getEnvironment)
  import qualified Data.Trie as Trie
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
          --  At this point, the type of the Left value is
          --
          --  LetExpr
          --    (Either
          --      (RecursionAllowance, ExprText)
          --      ExprText
          --    , Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --    (Either
          --      (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text)
          --       ExprText)
          --
          --  Starting with the type of the LetBindings, not the final expression,
          --
          --  (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))
          --
          --  We distribute the Either, such that we get
          --
          --  Either
          --    ((RecursionAllowance, ExprText), Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --    (ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --
          --  Then, we focus on the Left branch as that is where we need to do all the validation work. Thus, we want to convert it from
          --
          --  ((RecursionAllowance, ExprText), Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --
          --  to
          --
          --  (RecursionAllowance, ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --
          --  to
          --
          --  (RecursionAllowance, LetBindingTypes, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --
          --  to
          --
          --  (Valid LetBindingTypes, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
          --
        Left value -> case validateRecursionLetBindingTypesNew . mapLetBindingsLeft (validateLetBindingTypesContainer . identifyVariablesContainer . fmap flattenTuple) $ first inverseDistributeEither value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Implement printing of invalid recursive LetBindingTypes
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let simplifiedFinalExprValidLetExpr = bimap (first (fst . getFirst)) (toContainerIntText . first (second (first getFirst))) validLetExpr
            -- The explanation for modifying the variable 'validLetExpr' is that it originally has the type of
            --
            -- Either
            --   (NonEmpty (LetBinding LetBindingTypes))
            --   (LetExpr (Container Int Text) a)
            --
            --  where the type variable 'a' stands for
            --
            --  Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text)
            --          ExprText
            --
            --  as originally modified by function 'linearUnfoldIndexValuesTrie'.
            --
            --  To satisfy letExprContainerToFinalContainer's type signature, we need to modify the second type variable of the LetExpr from
            --
            --  Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text)
            --          ExprText
            --
            --  to
            --
            --  Either (ExprRef, Container (Int, ExprText) Text)
            --          ExprText
            --
            --  So, starting from the original type of
            --
            --  LetExpr (Container Int Text)
            --          (Either (ExprRef, Container (Int, ExprText) Text) ExprText))
            --
            --  We want to modify the second type variable of the LetExpr, so we use 'second'.
            --  Now, the function we supply will modify the second type variable.
            --  We want to modify the Left value of the Either, so we use 'first'.
            --  Now the function we supply will modify the Left tuple value.
            --  We want to modify the Container value in the tuple, so we use 'second'.
            --  Now the function we supply will modify the Container value of the tuple.
            --  We want to modify the first type variable of the Container, to change it from
            --
            --  Either (Int, ExprText) (NonEmpty (Int, ExprText))
            --
            --  to
            --
            --  (Int, ExprText)
            --
            --  , so we use 'first'.
            --
            --  Now, the function we supply will modify the first type variable of the Container.
            --  The function 'getFirst' returns the value of the Left untouched or it gets the head of the non empty list of the Right.
            --
            let containerized = letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            mapM_ T.putStr $ uncurry betaReduceContainer containerized
            T.putStrLn Data.Text.empty
        Right value -> case validateRecursionLetBindingTypesNew . mapLetBindingsLeft (validateLetBindingTypesContainer . identifyVariablesContainer) $ first (first flattenTuple . inverseDistributeEither) value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Replace print with actual formatted error message
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let simplifiedFinalExprValidLetExpr = bimap (first fst) toContainerIntText validLetExpr
            let containerized = letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            mapM_ T.putStr $ uncurry betaReduceContainer containerized
            T.putStrLn Data.Text.empty
      Nothing -> case mutualReferenceLetExprParse vExprs of
        Just validSyntax -> case mutualUnfoldIndexValuesTrie validSyntax of
          Left value -> do
            T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid."
            T.putStrLn ""
            traverse_ (mapM_ T.putStrLn) . invalidRebindMessage $ fmap (fmap (fmap snd)) value
          Right value -> case validateRecursionLetBindingTypesNew . mapLetBindingsLeft (validateLetBindingTypesContainer . identifyVariablesContainer . fmap flattenTuple) $ first inverseDistributeEither value of
            Left invalidRecursions -> do
              T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
              --TODO: Replace print with actual formatted error message
              --print invalidRecursions
              T.putStrLn Data.Text.empty
            Right validLetExpr -> do
              let simplifiedFinalExprValidLetExpr = bimap (first fst) toContainerIntText validLetExpr
              let containerized = letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
              mapM_ T.putStr $ uncurry betaReduceContainer containerized
              T.putStrLn Data.Text.empty
        Nothing -> do
          putStrLn "[Error]: Input was not syntactically valid."
          exitFailure
    else case linearReferenceLetExprParse vExprs of
      Just validSyntax -> case linearUnfoldIndexValuesTrie validSyntax of
        Left value -> do
          --Get the final let binding, which will contain a cumulative Trie of all let bindings
          let finalTrie = snd $ getFinalLetBindingValue value
          --Given [LetBinding (NonEmpty a)],
          --the first fmap is for the list,
          --the second fmap is for the LetBinding,
          --the third fmap is for the NonEmpty list.
          let modifyListLetBinding = fmap . fmap . fmap

          T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid."
          T.putStrLn ""
          traverse_ (mapM_ T.putStrLn) . invalidRebindMessage . modifyListLetBinding snd $ getRebinds finalTrie
        Right value -> case validateRecursionLetBindingTypesNew . mapLetBindingsLeft (validateLetBindingTypesContainer . identifyVariablesContainer . fmap flattenTuple) $ first inverseDistributeEither value of
          Left invalidRecursions -> do
            T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
            --TODO: Replace print with actual formatted error message
            --print invalidRecursions
            T.putStrLn Data.Text.empty
          Right validLetExpr -> do
            let simplifiedFinalExprValidLetExpr = bimap (first fst) toContainerIntText validLetExpr
            let containerized = letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
            mapM_ T.putStr $ uncurry betaReduceContainer containerized
            T.putStrLn Data.Text.empty
      Nothing -> case mutualReferenceLetExprParse vExprs of
        Just validSyntax -> case mutualUnfoldIndexValuesTrie validSyntax of
          Left value -> do
            T.putStrLn "[Error]: Input rebinds at least one mutually referential variable, which is invalid."
            T.putStrLn ""
            traverse_ (mapM_ T.putStrLn) . invalidRebindMessage $ fmap (fmap (fmap snd)) value
          Right value -> case validateRecursionLetBindingTypesNew . mapLetBindingsLeft (validateLetBindingTypesContainer . identifyVariablesContainer . fmap flattenTuple) $ first inverseDistributeEither value of
            Left invalidRecursions -> do
              T.putStrLn $ "[ERROR]: Some let bindings were recursive in definition, but were not defined as being recursive with the '" <> "rec" <> "' modifier."
              --TODO: Replace print with actual formatted error message
              --print invalidRecursions
              T.putStrLn Data.Text.empty
            Right validLetExpr -> do
              let simplifiedFinalExprValidLetExpr = bimap (first fst) toContainerIntText validLetExpr
              let containerized = letExprContainerToFinalContainer simplifiedFinalExprValidLetExpr
              mapM_ T.putStr $ uncurry betaReduceContainer containerized
              T.putStrLn Data.Text.empty
        Nothing -> do
          putStrLn "[Error]: Input was not syntactically valid."
          exitFailure
