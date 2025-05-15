{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MyLib.Print(invalidRebindMessage, exprRecInvalidRecursionMessage, letBindingRebindsMessage) where

  import MyLib.LetExpr
  import MyLib.Container
  import Data.Text (Text)
  import qualified Data.Text as T
  import qualified Data.Text.Lazy as L
  import qualified Data.Text.Encoding as TE
  import Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.Foldable1
  import GHC.Int (Int64)
  import Queue (Queue)
  import qualified Queue as Q

-- ------------------
-- | Error Messages |
-- ------------------

  data Printable a
    = Printable [a] a (Queue a)
    | PrintablePrefixed a [a] a (Queue a)
    | PrintableSuffixed a [a] a (Queue a)
    | PrintableInfixed a a [a] a (Queue a)

  instance Semigroup a => Semigroup (Printable a) where
    (Printable front middle back) <> enqueueBack = Printable front middle $ back <> (Q.fromList . NE.toList $ printableToList enqueueBack)
    (PrintablePrefixed prefix front middle back) <> enqueueBack =
      let
        prefixFn :: Semigroup a => a -> a
        prefixFn = (prefix <>)
      in
      Printable (fmap prefixFn front) (prefixFn middle) (fmap prefixFn back <> (Q.fromList . NE.toList $ printableToList enqueueBack))
    (PrintableSuffixed suffix front middle back) <> enqueueBack =
      let
        suffixFn :: Semigroup a => a -> a
        suffixFn = (<> suffix)
      in
      Printable (fmap suffixFn front) (suffixFn middle) (fmap suffixFn back <> (Q.fromList . NE.toList $ printableToList enqueueBack))
    (PrintableInfixed prefix suffix front middle back) <> enqueueBack =
      let
        infixFn :: Semigroup a => a -> a
        infixFn x = prefix <> x <> suffix
      in
      Printable (fmap infixFn front) (infixFn middle) (fmap infixFn back <> (Q.fromList . NE.toList $ printableToList enqueueBack))

  --------------------

  printable
    :: a
    -> Printable a
  printable value = Printable [] value Q.empty

  printablePrefixed
    :: a
    -> a
    -> Printable a
  printablePrefixed prefix value = PrintablePrefixed prefix [] value Q.empty

  printableSuffixed
    :: a
    -> a
    -> Printable a
  printableSuffixed suffix value = PrintableSuffixed suffix [] value Q.empty

  printableInfixed
    :: a
    -> a
    -> a
    -> Printable a
  printableInfixed prefix suffix value = PrintableInfixed prefix suffix [] value Q.empty

  printableEnqueueFront
    :: a
    -> Printable a
    -> Printable a
  printableEnqueueFront value (Printable front middle back) = Printable (value : front) middle back
  printableEnqueueFront value (PrintablePrefixed prefix front middle back) = PrintablePrefixed prefix (value : front) middle back
  printableEnqueueFront value (PrintableSuffixed suffix front middle back) = PrintableSuffixed suffix (value : front) middle back
  printableEnqueueFront value (PrintableInfixed prefix suffix front middle back) = PrintableInfixed prefix suffix (value : front) middle back

  printableEnqueueBack
    :: a
    -> Printable a
    -> Printable a
  printableEnqueueBack value (Printable front middle back) = Printable front middle $ Q.enqueue value back
  printableEnqueueBack value (PrintablePrefixed prefix front middle back) = PrintablePrefixed prefix front middle $ Q.enqueue value back
  printableEnqueueBack value (PrintableSuffixed suffix front middle back) = PrintableSuffixed suffix front middle $ Q.enqueue value back
  printableEnqueueBack value (PrintableInfixed prefix suffix front middle back) = PrintableInfixed prefix suffix front middle $ Q.enqueue value back

  letBindingVarPrintable
    :: LetBinding a
    -> Printable Text
  letBindingVarPrintable lb = printable . varToText . NE.head . letExprLetBindingValues $ letExpr (mapLetBinding const lb) lb

  letBindingValuePrintable
    :: LetBinding a
    -> Printable a
  letBindingValuePrintable lb = printable . NE.head . letExprLetBindingValues $ letExpr lb lb

  varPrintable
    :: Var
    -> Printable Text
  varPrintable var = printable $ varToText var

  printableToList
    :: Semigroup a
    => Printable a
    -> NonEmpty a
  printableToList (Printable front middle back) = NE.prependList front $ middle :| Q.toList back
  printableToList (PrintablePrefixed prefix front middle back) = fmap (prefix <>) . NE.prependList front $ middle :| Q.toList back
  printableToList (PrintableSuffixed suffix front middle back) = fmap (<> suffix) . NE.prependList front $ middle :| Q.toList back
  printableToList (PrintableInfixed prefix suffix front middle back) = fmap (\x -> prefix <> x <> suffix) . NE.prependList front $ middle :| Q.toList back

  ------------

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
         . printablePrefixed (repeatChar 4 ' ')
         . fold1
         . printableToList
         . letBindingValuePrintable)
         (letBindingNonEmptyToNonEmptyLetBinding lb)

  invalidRebindMessage
    :: [LetBinding (NonEmpty Text)]
    -> [NonEmpty Text]
  invalidRebindMessage = fmap letBindingRebindsMessage
