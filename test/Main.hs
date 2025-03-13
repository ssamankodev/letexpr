{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

  import Test.Test

  main :: IO ()
  main = tests >> pure ()
