{-# LANGUAGE TemplateHaskell #-}

module Test.LetExpr (testsLetExpr) where

  import MyLib
  import Hedgehog
  import qualified Hedgehog.Gen as Gen
  import qualified Hedgehog.Range as Range

{-
Need to make tests for:
insertOrPrependEitherTrieLB
insertOrPrependTrieLB
filterMapTrieLB
matchTrieLB
-}

  testsLetExpr :: IO Bool
  testsLetExpr =
    checkParallel $$(discover)

  emptyTrieLBRoundTrip :: Property
  emptyTrieLBRoundTrip =
    property $ do
      case trieLBToLetBindings emptyTrieLB of
        [] -> success
        _ -> failure
