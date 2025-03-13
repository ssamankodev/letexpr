{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module MyLib.LetExpr (LetExpr(..), ExprText(..), LetBinding(..), Var(..), RecursionAllowance(..), getRebinds, mapLetBindings, mapLetBindingsLeft, validateRecursionLetBindingTypesNew, validateRecursionLetBindingTypes, letExprContainerToFinalContainer, betaReduceContainer, linearUnfoldIndexValuesTrie, mutualUnfoldIndexValuesTrie, validateLetBindingTypesContainer, getFirst, getFinalLetBindingValue, invalidRebindMessage, varT, varBS, toVar, exprTextToContainer, toContainerIntText, identifyVariablesContainer, inverseDistributeEither, flattenTuple) where

  import Data.Foldable(foldl')
  import Data.Maybe
  import Data.Text (Text())
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import Data.Text.Lazy.Builder (Builder)
  import qualified Data.Text.Lazy.Builder as TLB
  import qualified Data.Text.Lazy as TL (toStrict)
  import Data.List (sortBy, unfoldr, find)
  import Data.List.NonEmpty (NonEmpty(..), (<|))
  import qualified Data.List.NonEmpty as NE
  import Data.Sequence (Seq(..))
  import qualified Data.Sequence as Seq
  import Data.Maybe
  import Data.Kind (Type)
  import Data.Bifunctor
  import Data.Ord
  import Data.Trie (Trie)
  import qualified Data.Trie as Trie
  import Data.ByteString (ByteString)
  import qualified Data.ByteString as B
  import Data.Array (Array)
  import qualified Data.Array as DA

  --Is a newtype for Text that represents a variable name
  newtype Var = Var ByteString
    deriving (Eq, Show, Ord) via ByteString

  data LetBinding (dataType :: Type) = LetBinding Var dataType
    deriving (Functor, Show)

  data RecursionAllowance = Permit | Prohibit

  --Represents text that either references a variable introduced by a let-binding or is just plain-text.
  newtype ExprText = ExprText Text
    deriving Show

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --The Text value is the prefix of the overall expression if it is not a variable.
  data ExprRec
    = ExprRec Var Text ExprRecData
    | ExprRecNoText Var ExprRecData
    deriving Show

  data ExprRecData
    = ExprRecData Text ExprRecData   --Represents a recursive variable followed by a Text value
    | ExprRecDataNoText ExprRecData  --Represents a recursive variable not followed by a Text value
    | ExprRecDataFinal Text          --Represents a final recursive variable followed by a final Text value
    | ExprRecDataFinalNoText         --Represents a final recursive variable not followed by a final Text value
    deriving Show

  data ExprRef
    = ExprRef Text ExprRefData
    | ExprRefNoText ExprRefData
    deriving Show

  data ExprRefData
    = ExprRefData Var Text ExprRefData
    | ExprRefDataNoText Var ExprRefData
    | ExprRefDataFinal Var Text
    | ExprRefDataFinalNoText Var
    deriving Show

  data ExprRefRec
    = ExprRefRec Var Text ExprRefRecData
    | ExprRefRecNoText Var ExprRefRecData
    deriving Show

  data ExprRefRecData
    = ExprRefRecRefData Var Text ExprRefRecData
    | ExprRefRecRefDataNoText Var ExprRefRecData
    | ExprRefRecRecData Text ExprRefRecData
    | ExprRefRecRecDataNoText ExprRefRecData
    | ExprRefRecRefDataSwitch Var Text ExprRecData
    | ExprRefRecRefDataSwitchNoText Var ExprRecData
    | ExprRefRecRecDataSwitch Text ExprRefData
    | ExprRefRecRecDataSwitchNoText ExprRefData
    deriving Show

  data LetBindingTypes
    = LetBindingNonVar ExprText
    | LetBindingRec ExprRec
    | LetBindingRef ExprRef
    | LetBindingRefRec ExprRefRec
    deriving Show

  data Container a b
    = Container b (ContainerData a b)
    | ContainerNoInitial (ContainerData a b)
    | ContainerSingle b
    deriving Functor

  instance Bifunctor Container where
    bimap f g (Container b rest) = Container (g b) $ bimap f g rest
    bimap f g (ContainerNoInitial rest) = ContainerNoInitial $ bimap f g rest
    bimap _ g (ContainerSingle b) = ContainerSingle (g b)

  data ContainerData a b
    = ContainerData a b (ContainerData a b)
    | ContainerDataNoExtra a (ContainerData a b)
    | ContainerDataFinal a b
    | ContainerDataFinalNoExtra a
    deriving Functor

  instance Bifunctor ContainerData where
    bimap f g (ContainerData a b rest) = ContainerData (f a) (g b) $ bimap f g rest
    bimap f g (ContainerDataNoExtra a rest) = ContainerDataNoExtra (f a) $ bimap f g rest
    bimap f g (ContainerDataFinal a b) = ContainerDataFinal (f a) (g b)
    bimap f _ (ContainerDataFinalNoExtra a) = ContainerDataFinalNoExtra (f a)

  data LetExpr dataType finalExpr
    = LetBind (LetBinding dataType) (LetExpr dataType finalExpr)
    | LetBindFinal (LetBinding dataType) finalExpr
    deriving (Functor, Show)

  instance Bifunctor LetExpr where
    bimap f g (LetBind (LetBinding var expr) rest) = LetBind (LetBinding var $ f expr) $ bimap f g rest
    bimap f g (LetBindFinal (LetBinding var expr) finalExpr) = LetBindFinal (LetBinding var $ f expr) $ g finalExpr

  data Valid a
    = Valid a
    | ValidInexact a
    | Invalid a

  --------------------

  exprTextT
    :: ExprText
    -> Text
  exprTextT (ExprText text) = text

  toVar
    :: Text
    -> Var
  toVar = Var . TE.encodeUtf8

  varT
    :: Var
    -> Text
  varT (Var name) = TE.decodeUtf8 name

  varBS
    :: Var
    -> ByteString
  varBS (Var name) = name

  mapLetBindings
    :: (LetBinding a -> LetBinding c)
    -> LetExpr a b
    -> LetExpr c b
  mapLetBindings fn (LetBind lb rest) = LetBind (fn lb) $ mapLetBindings fn rest
  mapLetBindings fn (LetBindFinal lb finalExpr) = LetBindFinal (fn lb) finalExpr

  mapLetBindingsLeft
    :: (LetBinding a -> LetBinding b)
    -> LetExpr (Either a c) d
    -> LetExpr (Either b c) d
  mapLetBindingsLeft fn (LetBind (LetBinding var (Left value)) rest) = LetBind (fmap Left (fn (LetBinding var value))) $ mapLetBindingsLeft fn rest
  mapLetBindingsLeft fn (LetBind (LetBinding var (Right value)) rest) = LetBind (LetBinding var (Right value)) $ mapLetBindingsLeft fn rest
  mapLetBindingsLeft fn (LetBindFinal (LetBinding var (Left value)) finalExpr) = LetBindFinal (fmap Left (fn (LetBinding var value))) $ finalExpr
  mapLetBindingsLeft _ (LetBindFinal (LetBinding var (Right value)) finalExpr) = LetBindFinal (LetBinding var (Right value)) finalExpr

  ------------------

  validRecursion
    :: RecursionAllowance
    -> LetBindingTypes
    -> Valid LetBindingTypes
  validRecursion Prohibit lbt@(LetBindingNonVar _) = Valid lbt
  validRecursion Prohibit lbt@(LetBindingRef _) = Valid lbt
  validRecursion Prohibit lbt = Invalid lbt
  validRecursion Permit   lbt@(LetBindingNonVar _) = ValidInexact lbt
  validRecursion Permit   lbt@(LetBindingRef _) = ValidInexact lbt
  validRecursion Permit   lbt = Valid lbt

  --Given a Trie of rebinds, return LetBinding's where the Var is the Text-ified key and the value is the NonEmpty ExprText that were assigned to the same variable.
  getRebinds
    :: Trie (Either a (NonEmpty a))
    -> [LetBinding (NonEmpty a)]
  getRebinds trie =
    let
      filterFn :: Either a (NonEmpty a) -> Maybe (NonEmpty a)
      filterFn (Left _) = Nothing
      filterFn (Right nonEmpty) = Just nonEmpty

      mapFn :: (ByteString, b) -> LetBinding b
      mapFn (bs, b) = LetBinding (Var bs) b
    in
    fmap mapFn $ Trie.toList $ Trie.filterMap filterFn trie

  foldlLetExpr
    :: (b -> LetBinding a -> b)
    -> b
    -> LetExpr a c
    -> b
  foldlLetExpr fn accum (LetBind lb rest) = foldlLetExpr fn (fn accum lb) rest
  foldlLetExpr fn accum (LetBindFinal lb _) = fn accum lb

  exprTextToContainer
    :: ExprText
    -> Container a Text
  exprTextToContainer (ExprText text) = ContainerSingle text

  betaReduceContainer
    :: Container Int Text
    -> Array Int (Container Int Text)
    -> NonEmpty Text
  betaReduceContainer (Container text rest) arr = text <| betaReduceContainerData rest arr
  betaReduceContainer (ContainerNoInitial rest) arr = betaReduceContainerData rest arr
  betaReduceContainer (ContainerSingle text) _ = NE.singleton text

  betaReduceContainerData
    :: ContainerData Int Text
    -> Array Int (Container Int Text)
    -> NonEmpty Text
  betaReduceContainerData (ContainerData index text rest) arr = betaReduceContainer (arr DA.! index) arr <> (text <| betaReduceContainerData rest arr)
  betaReduceContainerData (ContainerDataNoExtra index rest) arr = betaReduceContainer (arr DA.! index) arr <> betaReduceContainerData rest arr
  betaReduceContainerData (ContainerDataFinal index text) arr = betaReduceContainer (arr DA.! index) arr <> NE.singleton text
  betaReduceContainerData (ContainerDataFinalNoExtra index) arr = betaReduceContainer (arr DA.! index) arr

  toContainerIntText
    :: Either (ExprRef, Container (Int, ExprText) Text) ExprText
    -> Container Int Text
  toContainerIntText (Left value) = first fst $ snd value
  toContainerIntText (Right value) = exprTextToContainer value

  letExprContainerToFinalContainer
    :: LetExpr (Container Int Text) (Container Int Text)
    -> (Container Int Text, Array Int (Container Int Text))
  letExprContainerToFinalContainer letExpr =
    let
      go
        :: Int
        -> [(Int, Container Int Text)]
        -> LetExpr (Container Int Text) (Container Int Text)
        -> (Container Int Text, Int, [(Int, Container Int Text)])
      go accum accumAssocs (LetBind (LetBinding _ container) rest) = go (accum + 1) ((accum, container) : accumAssocs) rest
      go accum accumAssocs (LetBindFinal (LetBinding _ container) finalContainer) = (finalContainer, accum, (accum, container) : accumAssocs)
    in
    case go 0 [] letExpr of
      (finalContainer, highestIndex, accumAssocs) -> (finalContainer, DA.array (0, highestIndex) accumAssocs)

  --Given a LetExpr, get back either a filtered version of its matching elements or a mapped version.
  filterMapOrMap
    :: (a -> Maybe c)
    -> (a -> d)
    -> LetExpr a b
    -> Either
         (NonEmpty c)
         (LetExpr d b)
  filterMapOrMap filterFn mapFn (LetBind (LetBinding var expr) rest) =
    let
      prepend
        :: (a -> Maybe c)
        -> (NonEmpty c -> NonEmpty c)
        -> c
        -> LetExpr a b
        -> NonEmpty c
      prepend filterFn' prependFn' single' (LetBind (LetBinding _ expr') rest') = case filterFn' expr' of
        Nothing -> prepend filterFn' prependFn' single' rest'
        Just found -> prepend filterFn' (prependFn' . (single' <|)) found rest'
      prepend filterFn' prependFn' single' (LetBindFinal (LetBinding _ expr') _) = case filterFn' expr' of
        Nothing -> prependFn' $ NE.singleton single'
        Just found -> prependFn' $ single' <| NE.singleton found
    in
    case filterFn expr of
      Nothing -> second (LetBind (LetBinding var (mapFn expr))) $ filterMapOrMap filterFn mapFn rest
      Just found -> Left $ prepend filterFn id found rest
  filterMapOrMap filterFn mapFn (LetBindFinal (LetBinding var expr) finalExpr) = case filterFn expr of
    Nothing -> Right $ LetBindFinal (LetBinding var (mapFn expr)) finalExpr
    Just found -> Left $ NE.singleton found

  --Alternate version of filterMapOrMap where the Left return value is wrapped in a LetBinding
  filterMapOrMapLetBinding
    :: (LetBinding a -> Maybe c)
    -> (a -> d)
    -> LetExpr a b
    -> Either
         (NonEmpty c)
         (LetExpr d b)
  filterMapOrMapLetBinding filterFn mapFn (LetBind lb@(LetBinding var expr) rest) =
    let
      prepend
        :: (LetBinding a -> Maybe c)
        -> (NonEmpty c -> NonEmpty c)
        -> c
        -> LetExpr a b
        -> NonEmpty c
      prepend filterFn' prependFn' single' (LetBind lb' rest') = case filterFn' lb' of
        Nothing -> prepend filterFn' prependFn' single' rest'
        Just found -> prepend filterFn' (prependFn' . (single' <|)) found rest'
      prepend filterFn' prependFn' single' (LetBindFinal lb' _) = case filterFn' lb' of
        Nothing -> prependFn' $ NE.singleton single'
        Just found -> prependFn' $ single' <| NE.singleton found
    in
    case filterFn lb of
      Nothing -> second (LetBind (LetBinding var (mapFn expr))) $ filterMapOrMapLetBinding filterFn mapFn rest
      Just found -> Left $ prepend filterFn id found rest
  filterMapOrMapLetBinding filterFn mapFn (LetBindFinal lb@(LetBinding var expr) finalExpr) = case filterFn lb of
    Nothing -> Right $ LetBindFinal (LetBinding var (mapFn expr)) finalExpr
    Just found -> Left $ NE.singleton found

  validateRecursionLetBindingTypesNew
    :: forall a b c . LetExpr (Either (Valid LetBindingTypes, Container c Text, a) (ExprText, a)) b
    -> Either (NonEmpty (LetBinding LetBindingTypes)) (LetExpr (Container c Text) b)
  validateRecursionLetBindingTypesNew letExpr =
    let
      filterFn
        :: LetBinding (Either (Valid LetBindingTypes, Container c Text, a) (ExprText, a))
        -> Maybe (LetBinding LetBindingTypes)
      filterFn (LetBinding var (Left (Invalid lbt, _, _))) = Just $ LetBinding var lbt
      filterFn _ = Nothing

      mapFn :: (Either (Valid LetBindingTypes, Container c Text, a) (ExprText, a))
            -> Container c Text
      mapFn (Left (_, container, _)) = container
      mapFn (Right (expr, _)) = exprTextToContainer expr
    in
    filterMapOrMapLetBinding filterFn mapFn letExpr

  --Either return Invalid recursive let bindings or return LetExpr (Container Int Text) a to be turned into an array to supply to the final expression of a transformed-into Container Int Text
  validateRecursionLetBindingTypes
    :: forall a b . LetExpr (Either (Valid LetBindingTypes, Container Int Text) ExprText, b) a
    -> Either
         (NonEmpty (LetBinding LetBindingTypes))
         (LetExpr (Container Int Text) a)
  validateRecursionLetBindingTypes letExpr =
    let
      filterFn :: LetBinding (Either (Valid LetBindingTypes, d) e, f) -> Maybe (LetBinding LetBindingTypes)
      filterFn (LetBinding var (Left (Invalid lbt, _), _)) = Just $ LetBinding var lbt
      filterFn _ = Nothing

      mapFn :: (Either (Valid LetBindingTypes, Container Int Text) ExprText, b) -> Container Int Text
      mapFn (Left (_, container), _) = container
      mapFn (Right expr, _) = exprTextToContainer expr
    in
    filterMapOrMapLetBinding filterFn mapFn letExpr

  flattenTuple
    :: ((a, b), c)
    -> (a, b, c)
  flattenTuple ((a, b), c) = (a, b, c)

  inverseDistributeEither
    :: LetBinding (Either a b, c)
    -> LetBinding (Either (a, c) (b, c))
  inverseDistributeEither (LetBinding var (Left a, c)) = LetBinding var $ Left (a, c)
  inverseDistributeEither (LetBinding var (Right b, c)) = LetBinding var $ Right (b, c)

  identifyVariablesContainer
    :: LetBinding (RecursionAllowance, ExprText, Trie a)
    -> LetBinding (RecursionAllowance, LetBindingTypes, Container a Text, Trie a)
  identifyVariablesContainer (LetBinding var (recAll, ExprText expr, trie)) = LetBinding var $ case identifyVariablesInTextContainer expr trie of
    Right (ExprText text) -> (recAll, LetBindingNonVar (ExprText text), ContainerSingle text, trie)
    Left (exprRef, container) -> (recAll, exprRefToLetBindingTypes var exprRef, container, trie)

  validateLetBindingTypesContainer
    :: LetBinding (RecursionAllowance, LetBindingTypes, a, b)
    -> LetBinding (Valid LetBindingTypes, a, b)
  validateLetBindingTypesContainer (LetBinding var (recAll, lbt, a, b)) = LetBinding var (validRecursion recAll lbt, a, b)

  identifyVariablesInTextContainer
    :: Text
    -> Trie a
    -> Either (ExprRef, Container a Text) ExprText
  identifyVariablesInTextContainer text trie =
    let
      takeUntilMatch :: Trie.Trie a -> B.ByteString -> Maybe (Text, (Var, a), B.ByteString)
      takeUntilMatch trie' bs' =
        let
          go :: Trie.Trie a -> B.ByteString -> Int -> Maybe (Int, (B.ByteString, a), B.ByteString)
          go trie'' bs'' accum'' = case Trie.match trie'' bs'' of
            Just (match'', value'', suffix'') -> Just (accum'', (match'', value''), suffix'')
            Nothing -> case fmap snd $ B.uncons bs'' of
              Just rest'' -> go trie'' rest'' $ accum'' + 1
              Nothing -> Nothing
        in
        case go trie' bs' 0 of
          Nothing -> Nothing
          Just (accum', (match', value'), suffix') -> Just (TE.decodeUtf8 $ B.take accum' bs', (Var match', value'), suffix')

      bsToExprRefDataContainerData :: Trie.Trie a -> Var -> a -> B.ByteString -> (ExprRefData, ContainerData a Text)
      bsToExprRefDataContainerData trie' var' value' bs' =
        if B.null bs'
        then (ExprRefDataFinalNoText var', ContainerDataFinalNoExtra value')
        else case takeUntilMatch trie' bs' of
          Nothing -> (ExprRefDataFinal var' $ TE.decodeUtf8 bs', ContainerDataFinal value' $ TE.decodeUtf8 bs')
          Just (T.Empty, (match', found'), suffix') -> bimap (ExprRefDataNoText var') (ContainerDataNoExtra value') $ bsToExprRefDataContainerData trie' match' found' suffix'
          Just (nonEmpty, (match', found'), suffix') -> bimap (ExprRefData var' nonEmpty) (ContainerData value' nonEmpty) $ bsToExprRefDataContainerData trie' match' found' suffix'
    in
    case takeUntilMatch trie $ TE.encodeUtf8 text of
      Nothing -> Right $ ExprText text
      Just (T.Empty, (match, value), suffix) -> Left . bimap (ExprRefNoText) (ContainerNoInitial) $ bsToExprRefDataContainerData trie match value suffix
      Just (nonEmpty, (match, value), suffix) -> Left . bimap (ExprRef nonEmpty) (Container nonEmpty) $ bsToExprRefDataContainerData trie match value suffix

  linearUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText
    -> Either
         (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
                  (Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text) ExprText))
         (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Int, ExprText))
                  (Either (ExprRef, Container (Int, ExprText) Text) ExprText))
  linearUnfoldIndexValuesTrie =
    let
      go
        :: Int
        -> Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))
        -> (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))) (Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))) (Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text) ExprText))
        -> Trie (Int, ExprText)
        -> (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Int, ExprText)) (Either (ExprRef, Container (Int, ExprText) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Int, ExprText)) (Either (ExprRef, Container (Int, ExprText) Text) ExprText))
        -> LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText
        -> Either
             (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
                      (Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text) ExprText))
             (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Int, ExprText))
                      (Either (ExprRef, Container (Int, ExprText) Text) ExprText))
      go index rebindTrie rebindPrepend noRebindTrie noRebindPrepend curr@(LetBind lb@(LetBinding (Var name) expr) rest) =
        let
          updatedNoRebindTrie =  case expr of
            Left (_, inner) -> Trie.insert name (index, inner) noRebindTrie
            Right inner -> Trie.insert name (index, inner) noRebindTrie

          updatedRebindTrie = insertOrPrepend rebindTrie index lb
        in
        if Trie.member name rebindTrie
        then Left . rebindPrepend $ goRebind index rebindTrie curr
        else
          go
            (index + 1)
            updatedRebindTrie
            (rebindPrepend . LetBind (fmap (, updatedRebindTrie) lb))
            updatedNoRebindTrie
            (noRebindPrepend . LetBind (fmap (, updatedNoRebindTrie) lb))
            rest
      go index rebindTrie rebindPrepend noRebindTrie noRebindPrepend curr@(LetBindFinal lb@(LetBinding (Var name) expr) (ExprText text)) =
        let
          updatedNoRebindTrie = case expr of
            Left (_, inner) -> Trie.insert name (index, inner) noRebindTrie
            Right inner -> Trie.insert name (index, inner) noRebindTrie
        in
        if Trie.member name noRebindTrie
        then Left . rebindPrepend $ goRebind index rebindTrie curr
        else Right . noRebindPrepend $ LetBindFinal (fmap (, updatedNoRebindTrie) lb) (identifyVariablesInTextContainer text updatedNoRebindTrie)

      goRebind
        :: Int
        -> Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))
        -> LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText
        -> LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText))))
                   (Either (ExprRef, Container (Either (Int, ExprText) (NonEmpty (Int, ExprText))) Text) ExprText)
      goRebind index trie (LetBind lb rest) =
        let
          updatedTrie = insertOrPrepend trie index lb
        in
        LetBind (fmap (, updatedTrie) lb) $ goRebind (index + 1) updatedTrie rest
      goRebind index trie (LetBindFinal lb (ExprText text)) =
        let
          updatedTrie = insertOrPrepend trie index lb
        in
        LetBindFinal (fmap (, updatedTrie) lb) $ identifyVariablesInTextContainer text updatedTrie

      insertOrPrepend
        :: Trie (Either (Int, a) (NonEmpty (Int, a)))
        -> Int
        -> LetBinding (Either (RecursionAllowance, a) a)
        -> Trie (Either (Int, a) (NonEmpty (Int, a)))
      insertOrPrepend trie index (LetBinding (Var name) expr) =
        let
          innerExpr = case expr of
            Left (_, inner) -> (index, inner)
            Right inner -> (index, inner)
        in
        case Trie.lookup name trie of
          Nothing ->  Trie.insert name (Left innerExpr) trie
          Just (Left singleExpr) -> Trie.insert name (Right $ innerExpr <| NE.singleton singleExpr) trie
          Just (Right multiExpr) -> Trie.insert name (Right $ innerExpr <| multiExpr) trie
    in
    go 0 Trie.empty id Trie.empty id

  mutualUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText
    -> Either
         ([LetBinding (NonEmpty (Int, ExprText))])
         (LetExpr (Either (RecursionAllowance, ExprText) ExprText, Trie (Int, ExprText))
                  (Either (ExprRef, Container (Int, ExprText) Text) ExprText))
  mutualUnfoldIndexValuesTrie letExpr =
    let
      getEitherValue :: Either (a, b) b -> b
      getEitherValue (Left (_, b)) = b
      getEitherValue (Right b) = b

      foldFn
        :: (Int, Either (Trie (Int, ExprText)) (Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))))
           -> LetBinding ExprText
           -> (Int, Either (Trie (Int, ExprText)) (Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))))
      foldFn (index, Left singleTrie) lb@(LetBinding var expr) =
        if Trie.member (varBS var) singleTrie
        then foldFn (index, Right $ Trie.filterMap (Just . Left) singleTrie) lb
        else (index + 1, Left $ Trie.insert (varBS var) (index, expr) singleTrie)
      foldFn (index, Right multiTrie) (LetBinding var expr) =
        let
          trieInsert :: Either (Int, ExprText) (NonEmpty (Int, ExprText)) -> Trie (Either (Int, ExprText) (NonEmpty (Int, ExprText)))
          trieInsert a = Trie.insert (varBS var) a multiTrie
        in
        (index + 1, Right . trieInsert $ case Trie.lookup (varBS var) multiTrie of
          Nothing -> Left (index, expr)
          Just (Left singleExpr) -> Right $ (index, expr) <| NE.singleton singleExpr
          Just (Right multiExpr) -> Right $ (index, expr) <| multiExpr
        )
    in
    case snd . foldlLetExpr foldFn (0, Left Trie.empty) $ first getEitherValue letExpr of
      Left singleTrie -> Right $ bimap (, singleTrie) (flip identifyVariablesInTextContainer singleTrie . exprTextT) letExpr
      Right multiTrie -> Left $ getRebinds multiTrie

  --------------------

  getFirst
    :: Either a (NonEmpty a)
    -> a
  getFirst (Left a) = a
  getFirst (Right (a :| _)) = a

  --------------------

  getFinalLetBindingValue :: LetExpr a b -> a
  getFinalLetBindingValue (LetBind _ rest) = getFinalLetBindingValue rest
  getFinalLetBindingValue (LetBindFinal (LetBinding _ value) _) = value

 ----------------------------------------------------

  exprRefToLetBindingTypes
    :: Var
    -> ExprRef
    -> LetBindingTypes
  exprRefToLetBindingTypes var exprRef@(ExprRefNoText rest) = case exprRefDataToLetBindingTypes var rest of
    Left _ -> LetBindingRef exprRef
    Right (Left expr) -> LetBindingRec $ ExprRecNoText var expr
    Right (Right expr) -> LetBindingRefRec $ ExprRefRecNoText var expr
  exprRefToLetBindingTypes var exprRef@(ExprRef text rest) = case exprRefDataToLetBindingTypes var rest of
    Left _ -> LetBindingRef exprRef
    Right (Left expr) -> LetBindingRec $ ExprRec var text expr
    Right (Right expr) -> LetBindingRefRec $ ExprRefRec var text expr

  exprRefDataToLetBindingTypes
    :: Var
    -> ExprRefData
    -> Either ExprRefData
              (Either ExprRecData
                      ExprRefRecData)
  exprRefDataToLetBindingTypes var (ExprRefDataFinal exprVar exprText) =
    if var == exprVar
    then Right . Left $ ExprRecDataFinal exprText
    else Left $ ExprRefDataFinal exprVar exprText
  exprRefDataToLetBindingTypes var (ExprRefDataFinalNoText exprVar) =
    if var == exprVar
    then Right . Left $ ExprRecDataFinalNoText
    else Left $ ExprRefDataFinalNoText exprVar
  exprRefDataToLetBindingTypes var (ExprRefData exprVar exprText rest) =
    if var == exprVar
    then case exprRefDataToLetBindingTypes var rest of
      Left expr -> Right . Right $ ExprRefRecRecDataSwitch exprText expr
      Right (Left expr) -> Right . Left $ ExprRecData exprText expr
      Right (Right expr) -> Right . Right $ ExprRefRecRecData exprText expr
    else case exprRefDataToLetBindingTypes var rest of
      Left expr -> Left $ ExprRefData exprVar exprText expr
      Right (Left expr) -> Right . Right $ ExprRefRecRefDataSwitch exprVar exprText expr
      Right (Right expr) -> Right . Right $ ExprRefRecRefData exprVar exprText expr
  exprRefDataToLetBindingTypes var (ExprRefDataNoText exprVar rest) =
    if var == exprVar
    then case exprRefDataToLetBindingTypes var rest of
      Left expr -> Right . Right $ ExprRefRecRecDataSwitchNoText expr
      Right (Left expr) -> Right . Left $ ExprRecDataNoText expr
      Right (Right expr) -> Right . Right $ ExprRefRecRecDataNoText expr
    else case exprRefDataToLetBindingTypes var rest of
      Left expr -> Left $ ExprRefDataNoText exprVar expr
      Right (Left expr) -> Right . Right $ ExprRefRecRefDataSwitchNoText exprVar expr
      Right (Right expr) -> Right . Right $ ExprRefRecRefDataNoText exprVar expr

--------------------------------------------

-- ------------------
-- | Error Messages |
-- ------------------

  invalidRecursionMessageUnderline
    :: LetBindingTypes
    -> Maybe Text
  invalidRecursionMessageUnderline (LetBindingRec expr) = Just $ T.concat . NE.toList $ exprRecUnderline expr
  invalidRecursionMessageUnderline (LetBindingRefRec expr) = Just $ T.concat . NE.toList $ exprRefRecUnderline expr
  invalidRecursionMessageUnderline _ = Nothing

  exprRecUnderline
    :: ExprRec
    -> NonEmpty Text
  exprRecUnderline (ExprRec var initial rest) = T.map (const ' ') initial <| exprRecDataUnderline (varT var) rest
  exprRecUnderline (ExprRecNoText var rest) = exprRecDataUnderline (varT var) rest

  exprRecDataUnderline
    :: Text
    -> ExprRecData
    -> NonEmpty Text
  exprRecDataUnderline varName (ExprRecData text rest) = T.map (const '^') varName <| T.map (const ' ') text <| exprRecDataUnderline varName rest
  exprRecDataUnderline varName (ExprRecDataNoText rest) = T.map (const '^') varName <| exprRecDataUnderline varName rest
  exprRecDataUnderline varName (ExprRecDataFinal text) = T.map (const '^') varName <| NE.singleton (T.map (const ' ') text)
  exprRecDataUnderline varName (ExprRecDataFinalNoText) = NE.singleton $ T.map (const '^') varName

  exprRefUnderline
    :: ExprRef
    -> NonEmpty Text
  exprRefUnderline (ExprRef initial rest) = T.map (const ' ') initial <| exprRefDataUnderline rest
  exprRefUnderline (ExprRefNoText rest) = exprRefDataUnderline rest

  exprRefDataUnderline
    :: ExprRefData
    -> NonEmpty Text
  exprRefDataUnderline (ExprRefData var text rest) = T.map (const '^') (varT var) <| T.map (const ' ') text <| exprRefDataUnderline rest
  exprRefDataUnderline (ExprRefDataNoText var rest) = T.map (const '^') (varT var) <| exprRefDataUnderline rest
  exprRefDataUnderline (ExprRefDataFinal var text) = T.map (const '^') (varT var) <| NE.singleton (T.map (const ' ') text)
  exprRefDataUnderline (ExprRefDataFinalNoText var) = NE.singleton $ T.map (const '^') (varT var)

  exprRefRecUnderline
    :: ExprRefRec
    -> NonEmpty Text
  exprRefRecUnderline (ExprRefRec var initial rest) = T.map (const ' ') initial <| exprRefRecDataUnderline (varT var) rest
  exprRefRecUnderline (ExprRefRecNoText var rest) = exprRefRecDataUnderline (varT var) rest

  exprRefRecDataUnderline
    :: Text
    -> ExprRefRecData
    -> NonEmpty Text
  exprRefRecDataUnderline varName (ExprRefRecRefData var text rest) = T.map (const '^') (varT var) <| T.map (const ' ') text <| exprRefRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRefDataNoText var rest) = T.map (const '^') (varT var) <| exprRefRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRecData text rest) = T.map (const '^') varName <| T.map (const ' ') text <| exprRefRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRecDataNoText rest) = T.map (const '^') varName <| exprRefRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRefDataSwitch var text rest) = T.map (const '^') (varT var) <| T.map (const ' ') text <| exprRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRefDataSwitchNoText var rest) = T.map (const '^') (varT var) <| exprRecDataUnderline varName rest
  exprRefRecDataUnderline varName (ExprRefRecRecDataSwitch text rest) = T.map (const '^') varName <| T.map (const ' ') text <| exprRefDataUnderline rest
  exprRefRecDataUnderline varName (ExprRefRecRecDataSwitchNoText rest) = T.map (const '^') varName <| exprRefDataUnderline rest

  --This function should be explaining how the given LetBinding was invalid.
  --It should state what the given Var/whole LetBinding is, then underline
  exprRecInvalidRecursionMessage :: Var -> Text
  exprRecInvalidRecursionMessage var = "The let expression contains a let binding that recursively binds variable '" `T.append` varT var `T.append` "' to itself."

  letBindingRebindsMessage
    :: LetBinding (NonEmpty ExprText)
    -> NonEmpty Text
  letBindingRebindsMessage (LetBinding var nonEmpty) =
    let
      exprText :: ExprText -> Text
      exprText (ExprText expr) = expr
    in
    ("Variable '" <> varT var <> "' was bound to the following definitions, in order of recency:")
    <| fmap ((T.unfoldrN 4 (\x -> Just (' ', x)) () <>) . exprText) nonEmpty

  invalidRebindMessage
    :: [LetBinding (NonEmpty ExprText)]
    -> [NonEmpty Text]
  invalidRebindMessage = fmap letBindingRebindsMessage
