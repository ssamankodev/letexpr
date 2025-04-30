{-# LANGUAGE StarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}

module MyLib.LetExpr (LetExpr(..), LetBinding, Var(..), TrieLB, Printable,  letBindingBS, filterMapOrMap, foldlLetExpr, letBindingCaseVar, letBindingCaseVarBS, letBindingCaseVarBSValue, mapLetBinding, letExpr, prependLetExpr, mapLetBindings, insertOrPrependTrieLB, insertOrPrependEitherTrieLB, emptyTrieLB, filterMapTrieLB, trieLBToLetBindings, matchTrieLB, letExprLetBindings, letExprLetBindingValues, letBindingEitherToEitherLetBinding, eitherLetBindingToLetBindingEither, letBindingTupleToTupleLetBinding, tupleLetBindingToLetBindingTuple, printable, printablePrefixed, printableSuffixed, printableInfixed, printableEnqueueFront, printableEnqueueBack, letBindingVarValuePrintable, letBindingVarPrintable, letBindingValuePrintable, printableToList) where

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
    = Printable (Queue a)
    | PrintablePrefixed a (Queue a)
    | PrintableSuffixed a (Queue a)
    | PrintableInfixed a a (Queue a)

  --------------------

  printable
    :: Printable a
  printable = Printable Q.empty

  printablePrefixed
    :: a
    -> Printable a
  printablePrefixed a = PrintablePrefixed a Q.empty

  printableSuffixed
    :: a
    -> Printable a
  printableSuffixed a = PrintableSuffixed a Q.empty

  printableInfixed
    :: a
    -> a
    -> Printable a
  printableInfixed prefix suffix = PrintableInfixed prefix suffix Q.empty

  printableEnqueueFront
    :: a
    -> Printable a
    -> Printable a
  printableEnqueueFront value (Printable queue) = Printable $ Q.enqueueFront value queue
  printableEnqueueFront value (PrintablePrefixed a queue) = PrintablePrefixed a $ Q.enqueueFront value queue
  printableEnqueueFront value (PrintableSuffixed a queue) = PrintableSuffixed a $ Q.enqueueFront value queue
  printableEnqueueFront value (PrintableInfixed prefix suffix queue) = PrintableInfixed prefix suffix $ Q.enqueueFront value queue

  printableEnqueueBack
    :: a
    -> Printable a
    -> Printable a
  printableEnqueueBack value (Printable queue) = Printable $ Q.enqueue value queue
  printableEnqueueBack value (PrintablePrefixed a queue) = PrintablePrefixed a $ Q.enqueue value queue
  printableEnqueueBack value (PrintableSuffixed a queue) = PrintableSuffixed a $ Q.enqueue value queue
  printableEnqueueBack value (PrintableInfixed prefix suffix queue) = PrintableInfixed prefix suffix $ Q.enqueue value queue

  letBindingVarValuePrintable
    :: LetBinding Text
    -> Printable Text
  letBindingVarValuePrintable (LetBinding (Var var) value) = Printable (Q.singleton $ TE.decodeUtf8 var <> value)

  letBindingVarPrintable
    :: LetBinding a
    -> Printable Text
  letBindingVarPrintable (LetBinding (Var var) _) = Printable (Q.singleton $ TE.decodeUtf8 var)

  letBindingValuePrintable
    :: LetBinding a
    -> Printable a
  letBindingValuePrintable (LetBinding _ value) = Printable (Q.singleton value)

  printableToList
    :: Semigroup a
    => Printable a
    -> [a]
  printableToList (Printable queue) = Q.toList queue
  printableToList (PrintablePrefixed _ Q.Empty) = []
  printableToList (PrintablePrefixed prefix (Q.Full curr rest)) = prefix <> curr : printableToList (PrintablePrefixed prefix rest)
  printableToList (PrintableSuffixed _ Q.Empty) = []
  printableToList (PrintableSuffixed suffix (Q.Full curr rest)) = curr <> suffix : printableToList (PrintableSuffixed suffix rest)
  printableToList (PrintableInfixed _ _ Q.Empty) = []
  printableToList (PrintableInfixed prefix suffix (Q.Full curr rest)) = prefix <> curr <> suffix : printableToList (PrintableInfixed prefix suffix rest)

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
