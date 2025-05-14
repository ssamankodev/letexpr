{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

  import Test.Test
  import Test.LetExpr

  main :: IO ()
  main = do
    tests
    testsLetExpr
    pure ()
