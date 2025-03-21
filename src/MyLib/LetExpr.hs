{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module MyLib.LetExpr (LetExpr(..), ExprText(..), LetBinding(..), Var(..), RecursionAllowance(..), getRebinds, firstLetBindings, mapLetBindingsLeft, mapLetExprEitherLeft, validateRecursionLetBindingTypesNew, validateRecursionLetBindingTypes, letExprContainerToFinalContainer, betaReduceContainer, linearUnfoldIndexValuesTrie, mutualUnfoldIndexValuesTrie, validateLetBindingTypesContainer, getFirst, getFinalLetBindingValue, invalidRebindMessage, varT, varBS, toVar, exprTextToContainer, toContainerIntText, identifyVariablesContainer, inverseDistributeEither, flattenTuple, exprTextT) where

  import Data.Text (Text())
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import Data.List.NonEmpty (NonEmpty(..), (<|))
  import qualified Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.Trie (Trie)
  import qualified Data.Trie as Trie
  import Data.ByteString (ByteString)
  import qualified Data.ByteString as B
  import Data.Array (Array)
  import qualified Data.Array as DA

  --Is a newtype for Text that represents a variable name
  newtype Var = Var ByteString
    deriving (Eq, Ord) via ByteString

  --A let binding which holds a variable and datum.
  data LetBinding a = LetBinding Var a
    deriving (Functor)

  --A data type thar represents whether recursion is permitted in a given instance or not.
  data RecursionAllowance = Permit | Prohibit

  --Represents text that either references a variable introduced by a let-binding or is just plain-text.
  newtype ExprText = ExprText Text

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --The Text value is the prefix of the overall expression if it is not a variable.
  data ExprRec
    = ExprRec Var Text ExprRecData
    | ExprRecNoText Var ExprRecData

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --Represents an expression with recursive references.
  data ExprRecData
    = ExprRecData Text ExprRecData   --Represents a recursive variable followed by a Text value
    | ExprRecDataNoText ExprRecData  --Represents a recursive variable
    | ExprRecDataFinal Text          --Represents a final recursive variable followed by a final Text value
    | ExprRecDataFinalNoText         --Represents a final recursive variable

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  data ExprRef
    = ExprRef Text ExprRefData
    | ExprRefNoText ExprRefData

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --Represents an expression with references to other let bindings.
  data ExprRefData
    = ExprRefData Var Text ExprRefData  --Represents a non-recursive variable followed by a Text value
    | ExprRefDataNoText Var ExprRefData --Represents a non-recursive variable
    | ExprRefDataFinal Var Text         --Represents a final non-recursive variable followed by a final Text value
    | ExprRefDataFinalNoText Var        --Represents a final non-recursive variable

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --Represents an expression with recursive references or non-recursive references to other let bindings.
  data ExprRefRec
    = ExprRefRec Var Text ExprRefRecData
    | ExprRefRecNoText Var ExprRefRecData

  --INVARIANT TO UPHOLD: The Text values should not be empty. If they are, they should be switched to the alternate data constructor which is equivalent except for not storing a Text value.
  --Represents an expression with recursive references or non-recursive references to other let bindings.
  data ExprRefRecData
    = ExprRefRecRefData Var Text ExprRefRecData     --Represents a non-recursive variable followed by a Text value
    | ExprRefRecRefDataNoText Var ExprRefRecData    --Represents a non-recursive variable followed by a Text value
    | ExprRefRecRecData Text ExprRefRecData         --Represents a recursive variable followed by a Text value
    | ExprRefRecRecDataNoText ExprRefRecData        --Represents a recursive variable
    | ExprRefRecRefDataSwitch Var Text ExprRecData  --Represents a non-recursive variable followed by a Text value and a recursive expression
    | ExprRefRecRefDataSwitchNoText Var ExprRecData --Represents a non-recursive variable followed by a recursive expression
    | ExprRefRecRecDataSwitch Text ExprRefData      --Represents a recursive variable followed by a Text value and a non-recursive expression
    | ExprRefRecRecDataSwitchNoText ExprRefData     --Represents a recursive variable followed by a non-recursive expression

  --There exists 4 types of let bindings:
  --  Non-variable: The body only contains text with no references.
  --  Recursive: The body contains references, but only recursive references.
  --  Reference: The body contains references, but only non-recursive references.
  --  Reference-Recursive: The body contains references, both recursive and non-recursive.
  data LetBindingTypes
    = LetBindingNonVar ExprText
    | LetBindingRec ExprRec
    | LetBindingRef ExprRef
    | LetBindingRefRec ExprRefRec

  --A container of two types of data, where the first type variable is the primary data type and the second type variable is the secondary data type. It can hold datum of the secondary data type before it holds a ContainerData of the same type variables, or it can just hold a ContainerData of the same type variables, or it can just hold a single datum of the secondary data type.
  data Container a b
    = Container b (ContainerData a b)
    | ContainerNoInitial (ContainerData a b)
    | ContainerSingle b
    deriving Functor

  instance Bifunctor Container where
    bimap f g (Container b rest) = Container (g b) $ bimap f g rest
    bimap f g (ContainerNoInitial rest) = ContainerNoInitial $ bimap f g rest
    bimap _ g (ContainerSingle b) = ContainerSingle (g b)

  --A container of two types of data, where every constructor must at minimum hold one datum of the primary data type (i.e., the first type variable). It may additionally hold a datum of the secondary data type (e.g., the second type variable).
  data ContainerData a b
    = ContainerData a b (ContainerData a b)
    | ContainerDataNoExtra a (ContainerData a b)
    | ContainerDataFinal a b
    | ContainerDataFinalNoExtra a
    deriving (Eq, Functor)

  instance Bifunctor ContainerData where
    bimap f g (ContainerData a b rest) = ContainerData (f a) (g b) $ bimap f g rest
    bimap f g (ContainerDataNoExtra a rest) = ContainerDataNoExtra (f a) $ bimap f g rest
    bimap f g (ContainerDataFinal a b) = ContainerDataFinal (f a) (g b)
    bimap f _ (ContainerDataFinalNoExtra a) = ContainerDataFinalNoExtra (f a)

  --A let expression that has at least one let binding, which binds a variable to a body, and a final expression that is to be beta reduced by the preceding let bindings.
  data LetExpr dataType finalExpr
    = LetBind (LetBinding dataType) (LetExpr dataType finalExpr)
    | LetBindFinal (LetBinding dataType) finalExpr
    deriving Functor

  instance Bifunctor LetExpr where
    bimap f g (LetBind (LetBinding var expr) rest) = LetBind (LetBinding var $ f expr) $ bimap f g rest
    bimap f g (LetBindFinal (LetBinding var expr) finalExpr) = LetBindFinal (LetBinding var $ f expr) $ g finalExpr

  -- Holds a value and prescribes whether it is valid, valid but inexact or redundant, or invalid.
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

  embedLetBinding
    :: LetBinding a
    -> LetBinding (LetBinding a)
  embedLetBinding lb@(LetBinding var expr) = LetBinding var lb

  mapLetBinding
    :: (LetBinding a -> b)
    -> LetBinding a
    -> LetBinding b
  mapLetBinding fn = fmap fn . embedLetBinding

  bimapLetBindings
    :: (LetBinding a -> c)
    -> (b -> d)
    -> LetExpr a b
    -> LetExpr c d
  bimapLetBindings fnLB fnFE (LetBind lb next) = LetBind (mapLetBinding fnLB lb) $ bimapLetBindings fnLB fnFE next
  bimapLetBindings fnLB fnFE (LetBindFinal lb finalExpression) = LetBindFinal (mapLetBinding fnLB lb) $ fnFE finalExpression

  firstLetBindings
    :: (LetBinding a -> c)
    -> LetExpr a b
    -> LetExpr c b
  firstLetBindings fn = bimapLetBindings fn id

  mapLetBindingsLeft
    :: (LetBinding a -> b)
    -> LetBinding (Either a c)
    -> (Either b c)
  mapLetBindingsLeft fn lb = letBindingValue . eitherToLetBinding . first (fmap fn . embedLetBinding) $ letBindingToEither lb

  mapLetExprEitherLeft
    :: (LetBinding a -> b)
    -> LetExpr (Either a c) d
    -> LetExpr (Either b c) d
  mapLetExprEitherLeft fn = firstLetBindings (mapLetBindingsLeft fn)

  letBindingValue
    :: LetBinding a
    -> a
  letBindingValue (LetBinding _ a) = a

  letBindingToEither
    :: LetBinding (Either a b)
    -> Either (LetBinding a) (LetBinding b)
  letBindingToEither (LetBinding var (Left value)) = Left $ LetBinding var value
  letBindingToEither (LetBinding var (Right value)) = Right $ LetBinding var value

  eitherToLetBinding
    :: Either (LetBinding a) (LetBinding b)
    -> LetBinding (Either a b)
  eitherToLetBinding (Left (LetBinding var value)) = LetBinding var $ Left value
  eitherToLetBinding (Right (LetBinding var value)) = LetBinding var $ Right value

  foldlLetExpr
    :: (b -> LetBinding a -> b)
    -> b
    -> LetExpr a c
    -> b
  foldlLetExpr fn accum (LetBind lb rest) = foldlLetExpr fn (fn accum lb) rest
  foldlLetExpr fn accum (LetBindFinal lb _) = fn accum lb

  getFirst
    :: Either a (NonEmpty a)
    -> a
  getFirst (Left a) = a
  getFirst (Right (a :| _)) = a

  getFinalLetBindingValue :: LetExpr a b -> a
  getFinalLetBindingValue (LetBind _ rest) = getFinalLetBindingValue rest
  getFinalLetBindingValue (LetBindFinal (LetBinding _ value) _) = value

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
    fmap mapFn . Trie.toList $ Trie.filterMap filterFn trie

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
    :: (Either a b, c)
    -> Either (a, c) (b, c)
  inverseDistributeEither (Left a, c) = Left (a, c)
  inverseDistributeEither (Right b, c) = Right (b, c)

  identifyVariablesContainer
    :: LetBinding (RecursionAllowance, ExprText, Trie a)
    -> (RecursionAllowance, LetBindingTypes, Container a Text, Trie a)
  identifyVariablesContainer (LetBinding var (recAll, ExprText expr, trie)) = case identifyVariablesInTextContainer expr trie of
    Right (ExprText text) -> (recAll, LetBindingNonVar (ExprText text), ContainerSingle text, trie)
    Left (exprRef, container) -> (recAll, exprRefToLetBindingTypes var exprRef, container, trie)

  validateLetBindingTypesContainer
    :: (RecursionAllowance, LetBindingTypes, a, b)
    -> (Valid LetBindingTypes, a, b)
  validateLetBindingTypesContainer (recAll, lbt, a, b) = (validRecursion recAll lbt, a, b)

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
