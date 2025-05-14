{-# LANGUAGE TemplateHaskell #-}

module Test.Test (tests) where

  import MyLib
  import Hedgehog
  import qualified Hedgehog.Gen as Gen
  import qualified Hedgehog.Range as Range

  tests :: IO Bool
  tests =
    checkParallel $$(discover)

{-
  varRoundTripBS :: Property
  varRoundTripBS =
    property $ do
      xs <- forAll $ Gen.utf8 (Range.linear 0 10000) Gen.unicode
      MyLib.varToBS (MyLib.bsToVar xs) === xs

  testFlattenTuple :: Property
  testFlattenTuple =
    property $ do
      xs <- forAll $ Gen.integral_ (Range.linear 0 10000)
      ys <- forAll $ Gen.integral_ (Range.linear 0 10000)
      zs <- forAll $ Gen.integral_ (Range.linear 0 10000)
      MyLib.flattenTuple ((xs, ys), zs) === (xs, ys, zs)
-}
