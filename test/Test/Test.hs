{-# LANGUAGE TemplateHaskell #-}

module Test.Test (tests, test1) where

  import Hedgehog
  import qualified Hedgehog.Gen as Gen
  import qualified Hedgehog.Range as Range

  tests :: IO Bool
  tests =
    checkParallel $$(discover)

  test1 :: Property
  test1 =
    property $ do
      xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
      reverse (reverse xs) === xs

  test2 :: Property
  test2 =
    property $ do
      undefined
