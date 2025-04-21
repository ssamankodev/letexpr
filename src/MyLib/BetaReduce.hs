{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.BetaReduce(betaReduceContainer, letExprContainerToFinalContainer, validateRecursionLetBindingTypesContainer, validateLetBindingTypesContainer, identifyVariablesContainer, identifyVariablesInTextContainer, linearUnfoldIndexValuesTrie, mutualUnfoldIndexValuesTrie, getRebinds, eitherValue) where

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

  letExprContainerToFinalContainer
    :: LetExpr a b
    -> (b, Array Int a)
  letExprContainerToFinalContainer letExpr =
    let
      go
        :: Int
        -> [(Int, a)]
        -> LetExpr a b
        -> (b, Int, [(Int, a)])
      go accum accumAssocs (LetBind lb rest) = go (accum + 1) ((accum, letBindingValue lb) : accumAssocs) rest
      go accum accumAssocs (LetBindFinal lb finalContainer) = (finalContainer, accum, (accum, letBindingValue lb) : accumAssocs)
    in
    case go 0 [] letExpr of
      (finalContainer, highestIndex, accumAssocs) -> (finalContainer, DA.array (0, highestIndex) accumAssocs)

  validateRecursionLetBindingTypesContainer
    :: forall b c . LetExpr (Either (Valid LetBindingTypesContainer, Container c Text) ExprText) b
    -> Either (NonEmpty (LetBinding LetBindingTypesContainer)) (LetExpr (Container c Text) b)
  validateRecursionLetBindingTypesContainer letExpr =
    let
      filterFn
        :: LetBinding (Either (Valid LetBindingTypesContainer) ExprText)
        -> Maybe (LetBinding LetBindingTypesContainer)
      filterFn lb = case letBindingValue lb of
        Left (Invalid lbt) -> Just $ fmap (const lbt) lb
        _ -> Nothing
    in
    filterMapOrMapLetBinding (filterFn . fmap (first fst)) (eitherValue . bimap snd exprTextToContainer) letExpr

  validateLetBindingTypesContainer
    :: (RecursionAllowance, LetBindingTypesContainer, a, b)
    -> (Valid LetBindingTypesContainer, a, b)
  validateLetBindingTypesContainer (recAll, lbt, a, b) = (validRecursionContainer recAll lbt, a, b)

  identifyVariablesContainer
    :: LetBinding (RecursionAllowance, Text, Trie a)
    -> (RecursionAllowance, LetBindingTypesContainer, Container a Text, Trie a)
  identifyVariablesContainer lb = case letBindingValue lb of
    (recAll, expr, trie) -> case identifyVariablesInTextContainer expr trie of
      Right exprText -> (recAll, LetBindingContainerSingle (ContainerSingleValue $ exprTextToText exprText), exprTextToContainer exprText, trie)
      Left (ContainerNormal containerNormal, container) -> (recAll, LetBindingContainerNormal $ ContainerNormal containerNormal, container, trie)

  identifyVariablesInTextContainer
    :: Text
    -> Trie a
    -> Either (ContainerNormal Var Text, Container a Text) ExprText
  identifyVariablesInTextContainer text trie =
    let
      takeUntilMatch :: Trie.Trie a -> ByteString -> Maybe (Text, (Var, a), ByteString)
      takeUntilMatch trie' bs' =
        let
          go :: Trie a -> ByteString -> Int -> Maybe (Int, (ByteString, a), ByteString)
          go trie'' bs'' accum'' = case Trie.match trie'' bs'' of
            Just (match'', value'', suffix'') -> Just (accum'', (match'', value''), suffix'')
            Nothing -> case fmap snd $ B.uncons bs'' of
              Just rest'' -> go trie'' rest'' $ accum'' + 1
              Nothing -> Nothing
        in
        case go trie' bs' 0 of
          Nothing -> Nothing
          Just (accum', matching', suffix') -> Just (TE.decodeUtf8 $ B.take accum' bs', first bsToVar matching', suffix')

      bsToContainerData :: Trie.Trie a -> Var -> a -> ByteString -> (ContainerData Var Text, ContainerData a Text)
      bsToContainerData trie' var' value' bs' =
        if B.null bs'
        then (normalToContainerData $ NormalNoExtra var', normalToContainerData $ NormalNoExtra value')
        else case takeUntilMatch trie' bs' of
          Nothing -> (normalToContainerData . Normal var' $ TE.decodeUtf8 bs', normalToContainerData . Normal value' $ TE.decodeUtf8 bs')
          Just (T.Empty, (match', found'), suffix') -> bimap (prependContainerData (NormalNoExtra var')) (prependContainerData (NormalNoExtra value')) $ bsToContainerData trie' match' found' suffix'
          Just (nonEmpty, (match', found'), suffix') -> bimap (prependContainerData (Normal var' nonEmpty)) (prependContainerData (Normal value' nonEmpty)) $ bsToContainerData trie' match' found' suffix'
    in
    case takeUntilMatch trie $ TE.encodeUtf8 text of
      Nothing -> Right $ textToExprText text
      Just (T.Empty, (match, value), suffix) -> Left . bimap (ContainerNormal . ContainerShellNoExtra) (Container . ContainerShellNoExtra) $ bsToContainerData trie match value suffix
      Just (nonEmpty, (match, value), suffix) -> Left . bimap (ContainerNormal . ContainerShell nonEmpty) (Container . ContainerShell nonEmpty) $ bsToContainerData trie match value suffix

  linearUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                  (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                  (Either (ContainerNormal Var Text, Container (Int, Text) Text) ExprText))
  linearUnfoldIndexValuesTrie =
    let
      go
        :: Int
        -> Trie (Either (Int, Text) (NonEmpty (Int, Text)))
        -> (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                    (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                       (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
        -> Trie (Int, Text)
        -> (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                    (Either (ContainerNormal Var Text, Container (Int, Text) Text) ExprText)
            -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                       (Either (ContainerNormal Var Text, Container (Int, Text) Text) ExprText))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> Either
             (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                      (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText))
             (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                      (Either (ContainerNormal Var Text, Container (Int, Text) Text) ExprText))
      go index rebindTrie rebindPrepend noRebindTrie noRebindPrepend curr@(LetBind lb rest) =
        let
          updatedNoRebindTrie = letBindingCaseVarBS Trie.insert lb (index, eitherValue . first snd $ letBindingValue lb) noRebindTrie

          updatedRebindTrie = insertOrPrepend rebindTrie $ fmap ((index,) . eitherValue . first snd) lb
        in
        if letBindingCaseVarBS Trie.member lb rebindTrie
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
          updatedNoRebindTrie = letBindingCaseVarBS Trie.insert lb (index, eitherValue . first snd $ letBindingValue lb) noRebindTrie
        in
        if letBindingCaseVarBS Trie.member lb noRebindTrie
        then Left . rebindPrepend $ goRebind index rebindTrie curr
        else Right . noRebindPrepend $ LetBindFinal (fmap (, updatedNoRebindTrie) lb) (identifyVariablesInTextContainer text updatedNoRebindTrie)

      goRebind
        :: Int
        -> Trie (Either (Int, Text) (NonEmpty (Int, Text)))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> LetExpr (Either (RecursionAllowance, Text) Text, Trie (Either (Int, Text) (NonEmpty (Int, Text))))
                   (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) ExprText)
      goRebind index trie (LetBind lb rest) =
        let
          updatedTrie = insertOrPrepend trie $ fmap ((index,) . eitherValue . first snd) lb
        in
        LetBind (fmap (, updatedTrie) lb) $ goRebind (index + 1) updatedTrie rest
      goRebind index trie (LetBindFinal lb text) =
        let
          updatedTrie = insertOrPrepend trie $ fmap ((index,) . eitherValue . first snd) lb
        in
        LetBindFinal (fmap (, updatedTrie) lb) $ identifyVariablesInTextContainer text updatedTrie

      insertOrPrepend
        :: forall a
        .  Trie (Either a (NonEmpty a))
        -> LetBinding a
        -> Trie (Either a (NonEmpty a))
      insertOrPrepend trie lb =
        let
          innerExpr = letBindingValue lb

          insert :: Either a (NonEmpty a) -> Trie (Either a (NonEmpty a))
          insert a = letBindingCaseVarBS Trie.insert lb a trie
        in
        case letBindingCaseVarBS Trie.lookup lb trie of
          Nothing ->  insert (Left innerExpr)
          Just (Left singleExpr) -> insert (Right $ innerExpr <| NE.singleton singleExpr)
          Just (Right multiExpr) -> insert (Right $ innerExpr <| multiExpr)
    in
    go 0 Trie.empty id Trie.empty id

  mutualUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         [LetBinding (NonEmpty (Int, Text))]
         (LetExpr (Either (RecursionAllowance, Text) Text, Trie (Int, Text))
                  (Either (ContainerNormal Var Text, Container (Int, Text) Text) ExprText))
  mutualUnfoldIndexValuesTrie letExpr =
    let
      foldFn
        :: forall a
        .  (Int, Either (Trie (Int, a)) (Trie (Either (Int, a) (NonEmpty (Int, a)))))
        -> LetBinding a
        -> (Int, Either (Trie (Int, a)) (Trie (Either (Int, a) (NonEmpty (Int, a)))))
      foldFn (index, Left singleTrie) lb =
        if letBindingCaseVarBS Trie.member lb singleTrie
        then foldFn (index, Right $ Trie.filterMap (Just . Left) singleTrie) lb
        else (index + 1, Left $ letBindingCaseVarBS Trie.insert lb (index, letBindingValue lb) singleTrie)
      foldFn (index, Right multiTrie) lb = second Right $ foldFnMulti (index, multiTrie) lb

      foldFnMulti
        :: forall a
        .  (Int, Trie (Either (Int, a) (NonEmpty (Int, a))))
        -> LetBinding a
        -> (Int, Trie (Either (Int, a) (NonEmpty (Int, a))))
      foldFnMulti (index, trie) lb =
        let
          lbVal :: (Int, a)
          lbVal = (index, letBindingValue lb)
        in
        (index + 1, flip (letBindingCaseVarBS Trie.insert lb) trie $ case letBindingCaseVarBS Trie.lookup lb trie of
          Nothing -> Left lbVal
          Just (Left singleExpr) -> Right $ lbVal <| NE.singleton singleExpr
          Just (Right multiExpr) -> Right $ lbVal <| multiExpr
        )
    in
    case snd . foldlLetExpr foldFn (0, Left Trie.empty) $ first (eitherValue . first snd) letExpr of
      Left singleTrie -> Right $ bimap (, singleTrie) (flip identifyVariablesInTextContainer singleTrie) letExpr
      Right multiTrie -> Left $ getRebinds multiTrie

  eitherValue :: Either a a -> a
  eitherValue (Left a) = a
  eitherValue (Right a) = a

  validRecursionContainer
    :: RecursionAllowance
    -> LetBindingTypesContainer
    -> Valid LetBindingTypesContainer
  validRecursionContainer Prohibit lbt@(LetBindingContainerSingle _) = Valid lbt
  validRecursionContainer Prohibit lbt@(LetBindingContainerNormal _) = Valid lbt
  validRecursionContainer Prohibit lbt = Invalid lbt
  validRecursionContainer Permit lbt@(LetBindingContainerSingle _) = ValidInexact lbt
  validRecursionContainer Permit lbt@(LetBindingContainerNormal _) = ValidInexact lbt
  validRecursionContainer Permit lbt = Valid lbt

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
      mapFn (bs, b) = letBinding (bsToVar bs) b
    in
    fmap mapFn . Trie.toList $ Trie.filterMap filterFn trie
