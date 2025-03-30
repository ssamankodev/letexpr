{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.BetaReduce(betaReduceContainer, toContainerIntText, letExprContainerToFinalContainer, validateRecursionLetBindingTypesNew, validateLetBindingTypesContainer, identifyVariablesContainer, identifyVariablesInTextContainer, linearUnfoldIndexValuesTrie, mutualUnfoldIndexValuesTrie, validRecursion, getRebinds) where

  import MyLib.LetExpr
  import Data.List.NonEmpty (NonEmpty)
  import qualified Data.List.NonEmpty as NE
  import Data.List.NonEmpty ((<|))
  import Data.Text (Text)
  import Data.Text.Encoding as TE
  import Data.Array (Array)
  import qualified Data.Array as DA
  import qualified Data.Text as T
  import Data.Trie (Trie)
  import qualified Data.Trie as Trie
  import Data.ByteString (ByteString)
  import qualified Data.ByteString as B
  import Data.Bifunctor

  -- Holds a value and prescribes whether it is valid, valid but inexact or redundant, or invalid.
  data Valid a
    = Valid a
    | ValidInexact a
    | Invalid a

  betaReduceContainer
    :: Container Int Text
    -> Array Int (Container Int Text)
    -> NonEmpty Text
  betaReduceContainer containerObj arr = foldlContainerToList $ bimap (\index -> betaReduceContainer (arr DA.! index) arr) NE.singleton containerObj

  toContainerIntText
    :: Either (ExprRef, Container (Int, Text) Text) ExprText
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
      go accum accumAssocs (LetBind lb rest) = go (accum + 1) ((accum, letBindingValue lb) : accumAssocs) rest
      go accum accumAssocs (LetBindFinal lb finalContainer) = (finalContainer, accum, (accum, letBindingValue lb) : accumAssocs)
    in
    case go 0 [] letExpr of
      (finalContainer, highestIndex, accumAssocs) -> (finalContainer, DA.array (0, highestIndex) accumAssocs)

  validateRecursionLetBindingTypesNew
    :: forall b c . LetExpr (Either (Valid LetBindingTypes, Container c Text) ExprText) b
    -> Either (NonEmpty (LetBinding LetBindingTypes)) (LetExpr (Container c Text) b)
  validateRecursionLetBindingTypesNew letExpr =
    let
      filterFn
        :: LetBinding (Either (Valid LetBindingTypes) ExprText)
        -> Maybe (LetBinding LetBindingTypes)
      filterFn (LetBinding var (Left (Invalid lbt))) = Just $ LetBinding var lbt
      filterFn _ = Nothing

      mapFn :: (Either (Valid LetBindingTypes, Container c Text) ExprText)
            -> Container c Text
      mapFn (Left (_, container)) = container
      mapFn (Right expr) = exprTextToContainer expr
    in
    filterMapOrMapLetBinding (filterFn . fmap (first fst)) mapFn letExpr

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

  validateLetBindingTypesContainer
    :: (RecursionAllowance, LetBindingTypes, a, b)
    -> (Valid LetBindingTypes, a, b)
  validateLetBindingTypesContainer (recAll, lbt, a, b) = (validRecursion recAll lbt, a, b)

  identifyVariablesContainer
    :: LetBinding (RecursionAllowance, Text, Trie a)
    -> (RecursionAllowance, LetBindingTypes, Container a Text, Trie a)
  identifyVariablesContainer (LetBinding var (recAll, expr, trie)) = case identifyVariablesInTextContainer expr trie of
    Right exprText -> (recAll, LetBindingNonVar exprText, exprTextToContainer exprText, trie)
    Left (exprRef, container) -> (recAll, exprRefToLetBindingTypes var exprRef, container, trie)

  identifyVariablesInTextContainer
    :: Text
    -> Trie a
    -> Either (ExprRef, Container a Text) ExprText
  identifyVariablesInTextContainer text trie =
    let
      takeUntilMatch :: Trie.Trie a -> ByteString -> Maybe (Text, (Var, a), ByteString)
      takeUntilMatch trie' bs' =
        let
          go :: Trie.Trie a -> ByteString -> Int -> Maybe (Int, (ByteString, a), ByteString)
          go trie'' bs'' accum'' = case Trie.match trie'' bs'' of
            Just (match'', value'', suffix'') -> Just (accum'', (match'', value''), suffix'')
            Nothing -> case fmap snd $ B.uncons bs'' of
              Just rest'' -> go trie'' rest'' $ accum'' + 1
              Nothing -> Nothing
        in
        case go trie' bs' 0 of
          Nothing -> Nothing
          Just (accum', matching', suffix') -> Just (TE.decodeUtf8 $ B.take accum' bs', first bsToVar matching', suffix')

      bsToExprRefDataContainerData :: Trie.Trie a -> Var -> a -> ByteString -> (ExprRefData, ContainerData a Text)
      bsToExprRefDataContainerData trie' var' value' bs' =
        if B.null bs'
        then (exprRefDataFinalNoText var', containerDataFinalNoExtra value')
        else case takeUntilMatch trie' bs' of
          Nothing -> (exprRefDataFinal var' $ TE.decodeUtf8 bs', containerDataFinal value' $ TE.decodeUtf8 bs')
          Just (T.Empty, (match', found'), suffix') -> bimap (exprRefDataNoText var') (containerDataNoExtra value') $ bsToExprRefDataContainerData trie' match' found' suffix'
          Just (nonEmpty, (match', found'), suffix') -> bimap (exprRefData var' nonEmpty) (containerData value' nonEmpty) $ bsToExprRefDataContainerData trie' match' found' suffix'
    in
    case takeUntilMatch trie $ TE.encodeUtf8 text of
      Nothing -> Right $ toExprText text
      Just (T.Empty, (match, value), suffix) -> Left . bimap (exprRefNoText) (containerNoInitial) $ bsToExprRefDataContainerData trie match value suffix
      Just (nonEmpty, (match, value), suffix) -> Left . bimap (exprRef nonEmpty) (container nonEmpty) $ bsToExprRefDataContainerData trie match value suffix

  linearUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                  (Either (ExprRef, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                  (Either (ExprRef, Container (Int, Text) Text) ExprText))
  linearUnfoldIndexValuesTrie =
    let
      go
        :: Int
        -> Trie (Either (Int, Text) (NonEmpty (Int, Text)))
        -> (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                    (Either (ExprRef, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                       (Either (ExprRef, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
        -> Trie (Int, Text)
        -> (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                    (Either (ExprRef, Container (Int, Text) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                       (Either (ExprRef, Container (Int, Text) Text) ExprText))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> Either
             (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                      (Either (ExprRef, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
             (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                      (Either (ExprRef, Container (Int, Text) Text) ExprText))
      go index rebindTrie rebindPrepend noRebindTrie noRebindPrepend curr@(LetBind lb rest) =
        let
          updatedNoRebindTrie = case letBindingValue lb of
            Left (_, inner) -> Trie.insert (varBS $ letBindingVar lb) (index, inner) noRebindTrie
            Right inner -> Trie.insert (varBS $ letBindingVar lb) (index, inner) noRebindTrie

          updatedRebindTrie = insertOrPrepend rebindTrie index lb
        in
        if Trie.member (varBS $ letBindingVar lb) rebindTrie
        then Left . rebindPrepend $ goRebind index rebindTrie curr
        else
          go
            (index + 1)
            updatedRebindTrie
            (rebindPrepend . LetBind (fmap (, updatedRebindTrie) lb))
            updatedNoRebindTrie
            (noRebindPrepend . LetBind (fmap (, updatedNoRebindTrie) lb))
            rest
      go index rebindTrie rebindPrepend noRebindTrie noRebindPrepend curr@(LetBindFinal lb text) =
        let
          updatedNoRebindTrie = case letBindingValue lb of
            Left (_, inner) -> Trie.insert (varBS $ letBindingVar lb) (index, inner) noRebindTrie
            Right inner -> Trie.insert (varBS $ letBindingVar lb) (index, inner) noRebindTrie
        in
        if Trie.member (varBS $ letBindingVar lb) noRebindTrie
        then Left . rebindPrepend $ goRebind index rebindTrie curr
        else Right . noRebindPrepend $ LetBindFinal (fmap (, updatedNoRebindTrie) lb) (identifyVariablesInTextContainer text updatedNoRebindTrie)

      goRebind
        :: Int
        -> Trie (Either (Int, Text) (NonEmpty (Int, Text)))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                   (Either (ExprRef, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText)
      goRebind index trie (LetBind lb rest) =
        let
          updatedTrie = insertOrPrepend trie index lb
        in
        LetBind (fmap (, updatedTrie) lb) $ goRebind (index + 1) updatedTrie rest
      goRebind index trie (LetBindFinal lb text) =
        let
          updatedTrie = insertOrPrepend trie index lb
        in
        LetBindFinal (fmap (, updatedTrie) lb) $ identifyVariablesInTextContainer text updatedTrie

      insertOrPrepend
        :: forall a
         . Trie (Either (Int, a) (NonEmpty (Int, a)))
        -> Int
        -> LetBinding (Either (RecursionAllowance, a) a)
        -> Trie (Either (Int, a) (NonEmpty (Int, a)))
      insertOrPrepend trie index lb =
        let
          innerExpr = case letBindingValue lb of
            Left (_, inner) -> (index, inner)
            Right inner -> (index, inner)

          insert :: Either (Int, a) (NonEmpty (Int, a)) -> Trie (Either (Int, a) (NonEmpty (Int, a)))
          insert a = Trie.insert (varBS $ letBindingVar lb) a trie
        in
        case Trie.lookup (varBS $ letBindingVar lb) trie of
          Nothing ->  insert (Left innerExpr)
          Just (Left singleExpr) -> insert (Right $ innerExpr <| NE.singleton singleExpr)
          Just (Right multiExpr) -> insert (Right $ innerExpr <| multiExpr)
    in
    go 0 Trie.empty id Trie.empty id

  mutualUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         ([LetBinding (NonEmpty (Int, Text))])
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                  (Either (ExprRef, Container (Int, Text) Text) ExprText))
  mutualUnfoldIndexValuesTrie letExpr =
    let
      getEitherValue :: Either (a, b) b -> b
      getEitherValue (Left (_, b)) = b
      getEitherValue (Right b) = b

      foldFn
        :: forall a
        .  (Int, Either (Trie (Int, a)) (Trie (Either (Int, a) (NonEmpty (Int, a)))))
        -> LetBinding a
        -> (Int, Either (Trie (Int, a)) (Trie (Either (Int, a) (NonEmpty (Int, a)))))
      foldFn (index, Left singleTrie) lb =
        let
          lbVar :: ByteString
          lbVar = varBS $ letBindingVar lb
        in
        if Trie.member lbVar singleTrie
        then foldFn (index, Right $ Trie.filterMap (Just . Left) singleTrie) lb
        else (index + 1, Left $ Trie.insert lbVar (index, letBindingValue lb) singleTrie)
      foldFn (index, Right multiTrie) lb =
        let
          lbVar :: ByteString
          lbVar = varBS $ letBindingVar lb

          lbVal :: (Int, a)
          lbVal = (index, letBindingValue lb)

          trieInsert :: Either (Int, a) (NonEmpty (Int, a)) -> Trie (Either (Int, a) (NonEmpty (Int, a)))
          trieInsert a = Trie.insert lbVar a multiTrie
        in
        (index + 1, Right . trieInsert $ case Trie.lookup lbVar multiTrie of
          Nothing -> Left lbVal
          Just (Left singleExpr) -> Right $ lbVal <| NE.singleton singleExpr
          Just (Right multiExpr) -> Right $ lbVal <| multiExpr
        )
    in
    case snd . foldlLetExpr foldFn (0, Left Trie.empty) $ first getEitherValue letExpr of
      Left singleTrie -> Right $ bimap (, singleTrie) (flip identifyVariablesInTextContainer singleTrie) letExpr
      Right multiTrie -> Left $ getRebinds multiTrie

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
      mapFn (bs, b) = LetBinding (bsToVar bs) b
    in
    fmap mapFn . Trie.toList $ Trie.filterMap filterFn trie
