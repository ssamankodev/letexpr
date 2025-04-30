{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.BetaReduce(RecursionAllowance(..), betaReduceContainer, letExprContainerToFinalContainer, validateRecursionLetBindingTypesContainer, identifyVariablesContainer, identifyVariablesInTextContainer, linearUnfoldIndexValuesTrie, mutualUnfoldIndexValuesTrie, trieLBToLetBindings, eitherValue) where

  import MyLib.LetExpr
  import MyLib.Container
  import Data.List.NonEmpty (NonEmpty(..))
  import qualified Data.List.NonEmpty as NE
  import Data.Text (Text)
  import Data.Text.Encoding as TE
  import Data.Array (Array)
  import qualified Data.Array as DA
  import qualified Data.Text as T
  import Data.ByteString (ByteString)
  import qualified Data.ByteString as B
  import Data.Bifunctor

  --A data type thar represents whether recursion is permitted in a given instance or not.
  data RecursionAllowance = Permit | Prohibit

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
  letExprContainerToFinalContainer lb@(LetBind _ finalExpression) =
    let
      indexify :: Int -> NonEmpty a -> ([(Int, a)], Int)
      indexify index (a :| []) = ([(index, a)], index)
      indexify index (a :| (next : rest)) = first ((index, a):) $ indexify (index + 1) (next :| rest)
    in
    case indexify 0 $ letExprLetBindingValues lb of
      (indexed, highestIndex) -> (finalExpression, DA.array (0, highestIndex) indexed)

  validateRecursionLetBindingTypesContainer
    :: forall b c . LetExpr (Either (Valid LetBindingTypesContainer, Container c Text) Text) b
    -> Either (NonEmpty (LetBinding LetBindingTypesContainer)) (LetExpr (Container c Text) b)
  validateRecursionLetBindingTypesContainer expr =
    let
      filterFn
        :: Either (Valid LetBindingTypesContainer) Text
        -> Maybe LetBindingTypesContainer
      filterFn (Left (Invalid lbt)) = Just lbt
      filterFn _ = Nothing
    in
    filterMapOrMap (filterFn . first fst) (eitherValue . bimap snd (ContainerSingle . ContainerSingleValue)) expr

  identifyVariablesContainer
    :: LetBinding (RecursionAllowance, Text, TrieLB a)
    -> LetBinding (Valid LetBindingTypesContainer, Container a Text)
  identifyVariablesContainer lb =
    let
      fn
        :: (RecursionAllowance, Text, TrieLB a)
        -> Either ((RecursionAllowance, Container Var Text), Container a Text) (Valid LetBindingTypesContainer, Container a Text)
      fn (recAll, expr, trie) = case identifyVariablesInTextContainer expr trie of
        Left (containerNormal, container) -> Left ((recAll, containerNormalToContainer containerNormal), container)
        Right exprText -> Right (validRecursionContainer recAll . LetBindingContainerSingle $ ContainerSingleValue exprText, ContainerSingle (ContainerSingleValue exprText))
    in
    fmap eitherValue
      . eitherLetBindingToLetBindingEither
      . first (tupleLetBindingToLetBindingTuple
              . first (fmap (uncurry validRecursionContainer)
                      . tupleLetBindingToLetBindingTuple
                      . second containerToLetBindingTypes
                      . letBindingTupleToTupleLetBinding)
              . letBindingTupleToTupleLetBinding)
      . letBindingEitherToEitherLetBinding
      $ fmap fn lb

  identifyVariablesInTextContainer
    :: Text
    -> TrieLB a
    -> Either (ContainerNormal Var Text, Container a Text) Text
  identifyVariablesInTextContainer text trie =
    let
      takeUntilMatch :: TrieLB a -> ByteString -> Maybe (Text, (Var, a), ByteString)
      takeUntilMatch trie' bs' =
        case matchTrieLB trie' bs' of
          Nothing -> Nothing
          Just (accum', matching', suffix') -> Just (TE.decodeUtf8 $ B.take accum' bs', first Var matching', suffix')

      bsToContainerData :: TrieLB a -> Var -> a -> ByteString -> (ContainerData Var Text, ContainerData a Text)
      bsToContainerData trie' var' value' bs' =
        if B.null bs'
        then (normalToContainerData $ NormalNoExtra var', normalToContainerData $ NormalNoExtra value')
        else case takeUntilMatch trie' bs' of
          Nothing -> (normalToContainerData . Normal var' $ TE.decodeUtf8 bs', normalToContainerData . Normal value' $ TE.decodeUtf8 bs')
          Just (T.Empty, (match', found'), suffix') -> bimap (prependContainerData (NormalNoExtra var')) (prependContainerData (NormalNoExtra value')) $ bsToContainerData trie' match' found' suffix'
          Just (nonEmpty, (match', found'), suffix') -> bimap (prependContainerData (Normal var' nonEmpty)) (prependContainerData (Normal value' nonEmpty)) $ bsToContainerData trie' match' found' suffix'
    in
    case takeUntilMatch trie $ TE.encodeUtf8 text of
      Just (T.Empty, (match, value), suffix) -> Left . bimap (ContainerNormal . ContainerShellNoExtra) (Container . ContainerShellNoExtra) $ bsToContainerData trie match value suffix
      Just (nonEmpty, (match, value), suffix) -> Left . bimap (ContainerNormal . ContainerShell nonEmpty) (Container . ContainerShell nonEmpty) $ bsToContainerData trie match value suffix
      Nothing -> Right text

  linearUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         (LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Either (Int, Text) (NonEmpty (Int, Text))))
                  (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) Text))
         (LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Int, Text))
                  (Either (ContainerNormal Var Text, Container (Int, Text) Text) Text))
  linearUnfoldIndexValuesTrie =
    let
      go
        :: Int
        -> TrieLB (Int, Text)
        -> TrieLB (Either (Int, Text) (NonEmpty (Int, Text)))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> Either
             (LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Either (Int, Text) (NonEmpty (Int, Text))))
                      (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) Text))
             (LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Int, Text))
                      (Either (ContainerNormal Var Text, Container (Int, Text) Text) Text))
      go index noRebindTrie _ (LetBind (lb :| []) finalExpression) =
        case insertOrPrependEitherTrieLB (fmap ((index,) . eitherValue . first snd) lb) noRebindTrie of
          Left updatedNoRebindTrie -> Right $ LetBind (NE.singleton $ fmap (, updatedNoRebindTrie) lb) $ identifyVariablesInTextContainer finalExpression updatedNoRebindTrie
          Right updatedRebindTrie -> Left $ LetBind (NE.singleton $ fmap (, updatedRebindTrie) lb) $ identifyVariablesInTextContainer finalExpression updatedRebindTrie
      go index noRebindTrie rebindTrie (LetBind (lb :| (next : rest)) finalExpression) =
        let
          modifiedLB :: LetBinding (Int, Text)
          modifiedLB = fmap ((index,) . eitherValue . first snd) lb
        in
        case insertOrPrependEitherTrieLB modifiedLB noRebindTrie of
          Left updatedNoRebindTrie ->
            let
              updatedRebindTrie = insertOrPrependTrieLB modifiedLB rebindTrie
            in
            case go (index + 1) updatedNoRebindTrie updatedRebindTrie $ LetBind (next :| rest) finalExpression of
              Left expr -> Left $ prependLetExpr (fmap (, updatedRebindTrie) lb) expr
              Right expr -> Right $ prependLetExpr (fmap (, updatedNoRebindTrie) lb) expr
          Right updatedRebindTrie -> Left . prependLetExpr (fmap (, updatedRebindTrie) lb) . goRebind (index + 1) updatedRebindTrie $ LetBind (next :| rest) finalExpression

      goRebind
        :: Int
        -> TrieLB (Either (Int, Text) (NonEmpty (Int, Text)))
        -> LetExpr (Either (RecursionAllowance, Text) Text) Text
        -> LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Either (Int, Text) (NonEmpty (Int, Text))))
                   (Either (ContainerNormal Var Text, Container (Either (Int, Text) (NonEmpty (Int, Text))) Text) Text)
      goRebind index trie (LetBind (lb :| []) finalExpression) =
        let
          updatedRebindTrie = insertOrPrependTrieLB (fmap ((index,) . eitherValue . first snd) lb) trie
        in
        letExpr (fmap (, updatedRebindTrie) lb) $ identifyVariablesInTextContainer finalExpression updatedRebindTrie
      goRebind index trie (LetBind (lb :| (next : rest)) finalExpression) =
        let
          updatedRebindTrie = insertOrPrependTrieLB (fmap ((index,) . eitherValue . first snd) lb) trie
        in
        prependLetExpr (fmap (, updatedRebindTrie) lb) . goRebind (index + 1) updatedRebindTrie $ LetBind (next :| rest) finalExpression
    in
    go 0 emptyTrieLB emptyTrieLB

  mutualUnfoldIndexValuesTrie
    :: LetExpr (Either (RecursionAllowance, Text) Text) Text
    -> Either
         [LetBinding (NonEmpty (Int, Text))]
         (LetExpr (Either (RecursionAllowance, Text) Text, TrieLB (Int, Text))
                  (Either (ContainerNormal Var Text, Container (Int, Text) Text) Text))
  mutualUnfoldIndexValuesTrie (LetBind nonEmpty finalExpression) =
    let
      go
        :: Int
        -> TrieLB (Int, Text)
        -> NonEmpty (LetBinding Text)
        -> Either (TrieLB (Int, Text)) (TrieLB (Either (Int, Text) (NonEmpty (Int, Text))))
      go index trie (lb :| []) = insertOrPrependEitherTrieLB (fmap (index,) lb) trie
      go index trie (lb :| (next : rest)) = case insertOrPrependEitherTrieLB (fmap (index,) lb) trie of
        Left updatedNoRebindTrie -> go (index + 1) updatedNoRebindTrie (next :| rest)
        Right updatedRebindTrie -> Right $ goRebind (index + 1) updatedRebindTrie (next :| rest)

      goRebind
        :: Int
        -> TrieLB (Either (Int, Text) (NonEmpty (Int, Text)))
        -> NonEmpty (LetBinding Text)
        -> TrieLB (Either (Int, Text) (NonEmpty (Int, Text)))
      goRebind index trie (lb :| []) = insertOrPrependTrieLB (fmap (index,) lb) trie
      goRebind index trie (lb :| (next : rest)) = goRebind (index + 1) (insertOrPrependTrieLB (fmap (index,) lb) trie) (next :| rest)

      getRight
        :: Either a b
        -> Maybe b
      getRight (Right right) = Just right
      getRight _ = Nothing
    in
    case go 0 emptyTrieLB $ fmap (fmap (eitherValue . first snd)) nonEmpty of
      Left singleTrie -> Right $ LetBind (fmap (fmap (, singleTrie)) nonEmpty) (identifyVariablesInTextContainer finalExpression singleTrie)
      Right multiTrie -> Left . trieLBToLetBindings $ filterMapTrieLB getRight multiTrie

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

  eitherValue :: Either a a -> a
  eitherValue (Left a) = a
  eitherValue (Right a) = a
