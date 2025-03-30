{-# LANGUAGE OverloadedStrings #-}

module MyLib.Print(invalidRebindMessage, variableUnderline, exprRecInvalidRecursionMessage, letBindingRebindsMessage) where

  import MyLib.LetExpr
  import Data.Text(Text)
  import qualified Data.Text as T
  import Data.List.NonEmpty
  import Data.Bifunctor
  import Data.Foldable1

-- ------------------
-- | Error Messages |
-- ------------------

  variableUnderline
    :: LetBindingTypes
    -> Text
  variableUnderline expr = fold1 . containerVariableUnderline $ letBindingTypesToContainer expr

  containerVariableUnderline
    :: Container Var Text
    -> NonEmpty Text
  containerVariableUnderline = containerToList . bimap (T.map (const '^') . varT) (T.map (const ' '))

  --This function should be explaining how the given LetBinding was invalid.
  --It should state what the given Var/whole LetBinding is, then underline
  exprRecInvalidRecursionMessage :: Var -> Text
  exprRecInvalidRecursionMessage var = "The let expression contains a let binding that recursively binds variable '" `T.append` varT var `T.append` "' to itself."

  letBindingRebindsMessage
    :: LetBinding (NonEmpty Text)
    -> NonEmpty Text
  letBindingRebindsMessage lb =
    ("Variable '" <> varT (letBindingVar lb) <> "' was bound to the following definitions, in order of recency:")
    <| fmap (T.unfoldrN 4 (\x -> Just (' ', x)) () <>) (letBindingValue lb)

  invalidRebindMessage
    :: [LetBinding (NonEmpty Text)]
    -> [NonEmpty Text]
  invalidRebindMessage = fmap letBindingRebindsMessage
