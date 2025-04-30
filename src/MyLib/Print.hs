{-# LANGUAGE OverloadedStrings #-}

module MyLib.Print(invalidRebindMessage, variableUnderline, exprRecInvalidRecursionMessage, letBindingRebindsMessage) where

  import MyLib.LetExpr
  import MyLib.Container
  import Data.Text(Text)
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import Data.List.NonEmpty
  import Data.Bifunctor
  import Data.Foldable1
  import Queue

-- ------------------
-- | Error Messages |
-- ------------------

  variableUnderline
    :: LetBindingTypesContainer
    -> Text
  variableUnderline expr = fold1 . containerVariableUnderline $ letBindingTypesContainerToContainer expr

  containerVariableUnderline
    :: Container Var Text
    -> NonEmpty Text
  containerVariableUnderline = containerToList . bimap (T.map (const '^') . TE.decodeUtf8 . (\(Var var) -> var)) (T.map (const ' '))

  --This function should be explaining how the given LetBinding was invalid.
  --It should state what the given Var/whole LetBinding is, then underline
  exprRecInvalidRecursionMessage :: Var -> Text
  exprRecInvalidRecursionMessage var = "The let expression contains a let binding that recursively binds variable '" `T.append` TE.decodeUtf8 ((\(Var inner) -> inner) var) `T.append` "' to itself."

  letBindingRebindsMessage
    :: LetBinding (NonEmpty Text)
    -> NonEmpty Text
  letBindingRebindsMessage lb =
    ("Variable '" <> letBindingCaseVarBS TE.decodeUtf8 lb <> "' was bound to the following definitions, in order of recency:")
    <| fmap (T.unfoldrN 4 (\x -> Just (' ', x)) () <>) (letBindingCaseVarBSValue (\_ val -> val) lb)

  invalidRebindMessage
    :: [LetBinding (NonEmpty Text)]
    -> [NonEmpty Text]
  invalidRebindMessage = fmap letBindingRebindsMessage
