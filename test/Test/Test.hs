{-# LANGUAGE TemplateHaskell #-}

module Test.Test (tests, test1) where

  import MyLib
  import Hedgehog
  import qualified Hedgehog.Gen as Gen
  import qualified Hedgehog.Range as Range

  tests :: IO Bool
  tests =
    checkParallel $$(discover)

  --First attempt at trying to use the hedgehog library for my program
  test1 :: Property
  test1 =
    property $ do
      xs <- forAll $ Gen.text (Range.linear 0 10000) Gen.unicode
      exprTextT (ExprText xs) === xs

  test2 :: Property
  test2 =
    property $ do
      xs <- forAll $ Gen.utf8 (Range.linear 0 10000) Gen.unicode
      varBS (MyLib.Var xs) === xs
