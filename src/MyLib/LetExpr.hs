{-# LANGUAGE StarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}

module MyLib.LetExpr (LetExpr(..), LetBinding, Var(..), TrieLB, Printable,  letBindingBS, filterMapOrMap, foldlLetExpr, letBindingCaseVar, letBindingCaseVarBS, letBindingCaseVarBSValue, mapLetBinding, letExpr, prependLetExpr, mapLetBindings, insertOrPrependTrieLB, insertOrPrependEitherTrieLB, emptyTrieLB, filterMapTrieLB, trieLBToLetBindings, matchTrieLB, letExprLetBindings, letExprLetBindingValues, letBindingEitherToEitherLetBinding, eitherLetBindingToLetBindingEither, letBindingTupleToTupleLetBinding, tupleLetBindingToLetBindingTuple, printableSetPrefix, printableSetSuffix, printable, printablePrefixed, printableSuffixed, printableInfixed, printableEnqueueFront, printableEnqueueBack, letBindingVarPrintable, letBindingValuePrintable, printableToList, letBindingNonEmptyToNonEmptyLetBinding, nonEmptyLetBindingToLetBindingNonEmpty) where

  import Data.List.NonEmpty (NonEmpty(..), (<|))
  import qualified Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.ByteString (ByteString)
  import qualified Data.ByteString as B
  import Data.Text (Text)
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import Data.Foldable
  import Data.Trie (Trie)
  import qualified Data.Trie as Trie
  import Queue (Queue)
  import qualified Queue as Q

  --Is a newtype for Text that represents a variable name
  newtype Var = Var ByteString
    deriving (Eq, Ord) via ByteString

  --A let binding which holds a variable and datum.
  data LetBinding a = LetBinding Var a
    deriving (Functor)

  --A let expression that has at least one let binding, which binds a variable to a body, and a final expression that is to be beta reduced by the preceding let bindings.
  data LetExpr a b
    = LetBind (NonEmpty (LetBinding a)) b
    deriving Functor

  instance Bifunctor LetExpr where
    bimap f g (LetBind nonEmpty finalExpr) = LetBind (fmap (fmap f) nonEmpty) $ g finalExpr

  newtype TrieLB a = TrieLB (Trie a)
    deriving Functor

  data Printable a
    = Printable [a] a (Queue a)
    | PrintablePrefixed a [a] a (Queue a)
    | PrintableSuffixed a [a] a (Queue a)
    | PrintableInfixed a a [a] a (Queue a)

  --------------------

  printableSetPrefix
    :: a
    -> Printable a
    -> Printable a
  printableSetPrefix prefix (Printable front middle back) = PrintablePrefixed prefix front middle back
  printableSetPrefix prefix (PrintablePrefixed _ front middle back) = PrintablePrefixed prefix front middle back
  printableSetPrefix prefix (PrintableSuffixed suffix front middle back) = PrintableInfixed prefix suffix front middle back
  printableSetPrefix prefix (PrintableInfixed _ suffix front middle back) = PrintableInfixed prefix suffix front middle back

  printableSetSuffix
    :: a
    -> Printable a
    -> Printable a
  printableSetSuffix suffix (Printable front middle back) = PrintableSuffixed suffix front middle back
  printableSetSuffix suffix (PrintablePrefixed prefix front middle back) = PrintableInfixed prefix suffix front middle back
  printableSetSuffix suffix (PrintableSuffixed _ front middle back) = PrintableSuffixed suffix front middle back
  printableSetSuffix suffix (PrintableInfixed prefix _ front middle back) = PrintableInfixed prefix suffix front middle back

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
  letBindingVarPrintable (LetBinding (Var var) _) = Printable [] (TE.decodeUtf8 var) Q.empty

  letBindingValuePrintable
    :: LetBinding a
    -> Printable a
  letBindingValuePrintable (LetBinding _ value) = Printable [] value Q.empty

  printableToList
    :: Semigroup a
    => Printable a
    -> NonEmpty a
  printableToList (Printable front middle back) = NE.prependList front $ middle :| Q.toList back
  printableToList (PrintablePrefixed prefix front middle back) = fmap (prefix <>) . NE.prependList front $ middle :| Q.toList back
  printableToList (PrintableSuffixed suffix front middle back) = fmap (<> suffix) . NE.prependList front $ middle :| Q.toList back
  printableToList (PrintableInfixed prefix suffix front middle back) = fmap (\x -> prefix <> x <> suffix) . NE.prependList front $ middle :| Q.toList back

  --------------------

  emptyTrieLB
    :: TrieLB a
  emptyTrieLB = TrieLB Trie.empty

  insertOrPrependEitherTrieLB
    :: LetBinding a
    -> TrieLB a
    -> Either (TrieLB a)
              (TrieLB (Either a (NonEmpty a)))
  insertOrPrependEitherTrieLB lb@(LetBinding (Var var) value) (TrieLB trie) =
    if Trie.member var trie
    then Right . insertOrPrependTrieLB lb . TrieLB $ Trie.filterMap (Just . Left) trie
    else Left . TrieLB $ Trie.insert var value trie

  insertOrPrependTrieLB
    :: LetBinding a
    -> TrieLB (Either a (NonEmpty a))
    -> TrieLB (Either a (NonEmpty a))
  insertOrPrependTrieLB (LetBinding (Var var) value) (TrieLB trie) =
    let
      insertOrPrepend = case Trie.lookup var trie of
        Nothing -> Left value
        Just (Left single) -> Right $ value <| NE.singleton single
        Just (Right multiple) -> Right $ value <| multiple
    in
    TrieLB $ Trie.insert var insertOrPrepend trie

  trieLBToLetBindings
    :: TrieLB a
    -> [LetBinding a]
  trieLBToLetBindings (TrieLB trie) = uncurry letBindingBS <$> Trie.toList trie

  filterMapTrieLB
    :: (a -> Maybe b)
    -> TrieLB a
    -> TrieLB b
  filterMapTrieLB filterFn (TrieLB trie) = TrieLB $ Trie.filterMap filterFn trie

  matchTrieLB
    :: TrieLB a
    -> ByteString
    -> Maybe (Int, (ByteString, a), ByteString)
  matchTrieLB (TrieLB trie) bs =
    let
      go trie' bs' accum = case Trie.match trie' bs' of
        Just (match, value, suffix) -> Just (accum, (match, value), suffix)
        Nothing -> case snd <$> B.uncons bs' of
          Just rest' -> go trie' rest' $ accum + 1
          Nothing -> Nothing
    in
    go trie bs 0

  letExprLetBindings
    :: LetExpr a b
    -> NonEmpty (LetBinding a)
  letExprLetBindings (LetBind nonEmpty _) = nonEmpty

  letExprLetBindingValues
    :: LetExpr a b
    -> NonEmpty a
  letExprLetBindingValues (LetBind nonEmpty _) = fmap (\(LetBinding _ value) -> value) nonEmpty

  letBindingBS
    :: ByteString
    -> a
    -> LetBinding a
  letBindingBS = LetBinding . Var

  prependLetExpr
    :: LetBinding a
    -> LetExpr a b
    -> LetExpr a b
  prependLetExpr lb (LetBind nonEmpty finalExpression) = LetBind (lb <| nonEmpty) finalExpression

  letExpr
    :: LetBinding a
    -> b
    -> LetExpr a b
  letExpr = LetBind . NE.singleton

  ------------------

  mapLetBindings
    :: (LetBinding a -> LetBinding b)
    -> LetExpr a c
    -> LetExpr b c
  mapLetBindings fn (LetBind nonEmpty finalExpression) = LetBind (fmap fn nonEmpty) finalExpression

  letBindingNonEmptyToNonEmptyLetBinding
    :: LetBinding (NonEmpty a)
    -> NonEmpty (LetBinding a)
  letBindingNonEmptyToNonEmptyLetBinding (LetBinding var nonEmpty) = fmap (LetBinding var) nonEmpty

  nonEmptyLetBindingToLetBindingNonEmpty
    :: NonEmpty (LetBinding a)
    -> LetBinding (NonEmpty a)
  nonEmptyLetBindingToLetBindingNonEmpty nonEmpty@((LetBinding var _) :| _) =
    LetBinding var $ fmap (\(LetBinding _ value) -> value) nonEmpty

  letBindingEitherToEitherLetBinding
    :: LetBinding (Either a b)
    -> Either (LetBinding a) (LetBinding b)
  letBindingEitherToEitherLetBinding (LetBinding var (Left a)) = Left $ LetBinding var a
  letBindingEitherToEitherLetBinding (LetBinding var (Right b)) = Right $ LetBinding var b

  eitherLetBindingToLetBindingEither
    :: Either (LetBinding a) (LetBinding b)
    -> LetBinding (Either a b)
  eitherLetBindingToLetBindingEither (Left (LetBinding var value)) = LetBinding var $ Left value
  eitherLetBindingToLetBindingEither (Right (LetBinding var value)) = LetBinding var $ Right value

  letBindingTupleToTupleLetBinding
    :: LetBinding (a, b)
    -> (LetBinding a, LetBinding b)
  letBindingTupleToTupleLetBinding (LetBinding var (a, b)) = (LetBinding var a, LetBinding var b)

  --Nota Bene: This function assumes that the LetBinding's share the same variable.
  tupleLetBindingToLetBindingTuple
    :: (LetBinding a, LetBinding b)
    -> LetBinding (a, b)
  tupleLetBindingToLetBindingTuple (LetBinding var a, LetBinding _ b) = LetBinding var (a, b)

  --Alternate version of filterMapOrMap where the Left return value is wrapped in a LetBinding
  filterMapOrMap
    :: (a -> Maybe c)
    -> (a -> d)
    -> LetExpr a b
    -> Either
         (NonEmpty (LetBinding c))
         (LetExpr d b)
  filterMapOrMap filterFn mapFn (LetBind nonEmpty finalExpression) =
    let
      eitherFilterMapOrMap
        :: (a -> Maybe c)
        -> (a -> d)
        -> NonEmpty (LetBinding a)
        -> Either (NonEmpty (LetBinding c)) (NonEmpty (LetBinding d))
      eitherFilterMapOrMap filterFn' mapFn' ((LetBinding var value) :| []) = case filterFn' value of
        Just filterSatisfy -> Left . NE.singleton $ LetBinding var filterSatisfy
        Nothing -> Right . NE.singleton . LetBinding var $ mapFn' value
      eitherFilterMapOrMap filterFn' mapFn' ((LetBinding var value) :| (next : rest)) = case filterFn' value of
        Just filterSatisfy -> Left . filterMapLB filterFn' (LetBinding var filterSatisfy) $ next :| rest
        Nothing -> second ((LetBinding var $ mapFn' value) <|) $ eitherFilterMapOrMap filterFn' mapFn' (next :| rest)

      filterMapLB
        :: (a -> Maybe c)
        -> LetBinding c
        -> NonEmpty (LetBinding a)
        -> NonEmpty (LetBinding c)
      filterMapLB filterFn' filteredLB' ((LetBinding var value) :| []) = case filterFn' value of
        Just filterSatisfy -> filteredLB' <| NE.singleton (LetBinding var filterSatisfy)
        Nothing -> NE.singleton filteredLB'
      filterMapLB filterFn' filteredLB' ((LetBinding var value) :| (next : rest)) = case filterFn' value of
        Just filterSatisfy -> filteredLB' <| filterMapLB filterFn' (LetBinding var filterSatisfy) (next :| rest)
        Nothing -> filterMapLB filterFn' filteredLB' $ next :| rest
    in
    case eitherFilterMapOrMap filterFn mapFn nonEmpty of
      Left filteredNonEmpty -> Left filteredNonEmpty
      Right mappedNonEmpty -> Right $ LetBind mappedNonEmpty finalExpression

  foldlLetExpr
    :: (b -> a -> b)
    -> b
    -> LetExpr a c
    -> b
  foldlLetExpr fn accum (LetBind nonEmpty _) = foldl' fn accum $ fmap (\(LetBinding _ value) -> value) nonEmpty

  mapLetBinding
    :: (Var -> a -> b)
    -> LetBinding a
    -> LetBinding b
  mapLetBinding fn (LetBinding var value) = LetBinding var $ fn var value

  letBindingCaseVar
    :: (Var -> a)
    -> LetBinding b
    -> a
  letBindingCaseVar fn (LetBinding var _) = fn var

  letBindingCaseVarBS
    :: (ByteString -> a)
    -> LetBinding b
    -> a
  letBindingCaseVarBS fn (LetBinding (Var bs) _) = fn bs

  letBindingCaseVarBSValue
    :: (ByteString -> a -> b)
    -> LetBinding a
    -> b
  letBindingCaseVarBSValue fn (LetBinding (Var bs) value) = fn bs value
