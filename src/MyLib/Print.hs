{-# LANGUAGE OverloadedStrings #-}

module MyLib.Print(invalidRebindMessage, exprRecInvalidRecursionMessage, letBindingRebindsMessage) where

  import MyLib.LetExpr
  import MyLib.Container
  import Data.Text(Text)
  import qualified Data.Text as T
  import qualified Data.Text.Lazy as L
  import Data.List.NonEmpty
  import Data.Bifunctor
  import Data.Foldable1
  import GHC.Int (Int64)

-- ------------------
-- | Error Messages |
-- ------------------

  repeatChar
    :: GHC.Int.Int64
    -> Char
    -> Text
  repeatChar rep char = L.toStrict . L.take rep $ L.repeat char

  containerFactorRecVariableOriginalAndUnderline
    :: ContainerFactor Var Text
    -> Printable Text
  containerFactorRecVariableOriginalAndUnderline container = 
    (fold1 . containerToList . first (fold1 . printableToList . varPrintable) $ containerFactorToContainer container)
      `printableEnqueueFront` printableInfixed (repeatChar 4 ' ') "\n" (containerFactorRecVariableUnderline container)

  containerFactorOrNormalRecVariableOriginalAndUnderline
    :: ContainerFactorOrNormal Var Text
    -> Printable Text
  containerFactorOrNormalRecVariableOriginalAndUnderline container = 
    (fold1 . containerToList . first (fold1 . printableToList . varPrintable) $ containerFactorOrNormalToContainer container)
      `printableEnqueueFront` printableInfixed (repeatChar 4 ' ') "\n" (containerFactorOrNormalRecVariableUnderline container)

  containerFactorRecVariableUnderline
    :: ContainerFactor Var Text
    -> Text
  containerFactorRecVariableUnderline container@(ContainerFactor factor _) = containerVariableUnderline factor $ containerFactorToContainer container

  containerFactorOrNormalRecVariableUnderline
    :: ContainerFactorOrNormal Var Text
    -> Text
  containerFactorOrNormalRecVariableUnderline container@(ContainerFactorOrNormal factor _) = containerVariableUnderline factor $ containerFactorOrNormalToContainer container

  containerVariableUnderline
    :: Var
    -> Container Var Text
    -> Text
  containerVariableUnderline match container =
    let
      underlineVarOrEmpty :: Var -> Var -> Text
      underlineVarOrEmpty match' var' =
        if match' == var'
        then T.map (const '^') . fold1 . printableToList $ varPrintable var'
        else T.map (const ' ') . fold1 . printableToList $ varPrintable var'
    in
    fold1 . containerToList $ bimap (underlineVarOrEmpty match) (T.map (const ' ')) container

  exprRecInvalidRecursionMessage :: LetBinding RecursiveLetBindingTypesContainer -> Text
  exprRecInvalidRecursionMessage lb = "The let expression contains a let binding that recursively binds variable '" <> (fold1 . printableToList $ letBindingVarPrintable lb) <> "' to itself." <> "\n" <> (fold1 . printableToList $ exprThenUnderlineRecVar lb)

  exprThenUnderlineRecVar
    :: LetBinding RecursiveLetBindingTypesContainer
    -> Printable Text
  exprThenUnderlineRecVar lb =
    let
      recToPrintable
        :: RecursiveLetBindingTypesContainer
        -> Printable Text
      recToPrintable (RecLetBindingContainerFactor container) = fold1 . printableToList . printable $ containerFactorRecVariableOriginalAndUnderline container
      recToPrintable (RecLetBindingContainerFactorOrNormal container) = fold1 . printableToList . printable $ containerFactorOrNormalRecVariableOriginalAndUnderline container
    in
    fold1 . printableToList . letBindingValuePrintable $ fmap recToPrintable lb

  letBindingRebindsMessage
    :: LetBinding (NonEmpty Text)
    -> NonEmpty Text
  letBindingRebindsMessage lb =
    "Variable '" <> fold1 (printableToList $ letBindingVarPrintable lb) <> "' was bound to the following definitions, in order of recency:"
    <| fmap (fold1
         . printableToList
         . letBindingValuePrintablePrefixed (repeatChar 4 ' '))
         (letBindingNonEmptyToNonEmptyLetBinding lb)

  invalidRebindMessage
    :: [LetBinding (NonEmpty Text)]
    -> [NonEmpty Text]
  invalidRebindMessage = fmap letBindingRebindsMessage
