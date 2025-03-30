{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module MyLib.LetExpr (LetExpr(..), ExprText, ExprRef, ExprRefData, ExprRec, ExprRefRec, Container, ContainerData, LetBinding(..), Var, RecursionAllowance(..), LetBindingTypes(..), exprRef, exprRefNoText, exprRefData, exprRefDataNoText, exprRefDataFinal, exprRefDataFinalNoText, container, containerNoInitial, containerSingle, containerData, containerDataNoExtra, containerDataFinal, containerDataFinalNoExtra, firstLetBindings, mapLetBindingsLeft, mapLetExprEitherLeft, getFirst, getFinalLetBindingValue, varT, varBS, toVar, bsToVar, exprTextToContainer, inverseDistributeEither, flattenTuple, exprTextT, letExprLetBind, letExprLetBindFinal, letBinding, toExprText, letBindingTypesToContainer, containerToList, letBindingVar, letBindingValue, foldlContainerToList, foldlContainerDataToList, filterMapOrMap, filterMapOrMapLetBinding, foldlLetExpr, exprRefToLetBindingTypes) where

  import Data.Text (Text())
  import qualified Data.Text.Encoding as TE
  import Data.List.NonEmpty (NonEmpty(..), (<|), append)
  import qualified Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.ByteString (ByteString)

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

  --------------------

  exprTextT
    :: ExprText
    -> Text
  exprTextT (ExprText text) = text

  toExprText
    :: Text
    -> ExprText
  toExprText = ExprText

  toVar
    :: Text
    -> Var
  toVar = Var . TE.encodeUtf8

  bsToVar
    :: ByteString
    -> Var
  bsToVar = Var

  varT
    :: Var
    -> Text
  varT (Var name) = TE.decodeUtf8 name

  varBS
    :: Var
    -> ByteString
  varBS (Var name) = name

  letBindingVar
    :: LetBinding a
    -> Var
  letBindingVar (LetBinding var _) = var

  letBindingValue
    :: LetBinding a
    -> a
  letBindingValue (LetBinding _ a) = a

  letBinding
    :: Var
    -> a
    -> LetBinding a
  letBinding = LetBinding

  letExprLetBind
    :: LetBinding a
    -> (LetExpr a b -> LetExpr a b)
  letExprLetBind = LetBind

  letExprLetBindFinal
    :: LetBinding a
    -> b
    -> LetExpr a b
  letExprLetBindFinal = LetBindFinal

  foldlContainerToList
    :: Semigroup a
    => Container a a
    -> a
  foldlContainerToList (Container b rest) = b <> foldlContainerDataToList rest
  foldlContainerToList (ContainerNoInitial rest) = foldlContainerDataToList rest
  foldlContainerToList (ContainerSingle b) = b

  foldlContainerDataToList
    :: Semigroup a
    => ContainerData a a
    -> a
  foldlContainerDataToList (ContainerData a b rest) = a <> b <> foldlContainerDataToList rest
  foldlContainerDataToList (ContainerDataNoExtra a rest) = a <> foldlContainerDataToList rest
  foldlContainerDataToList (ContainerDataFinal a b) = a <> b
  foldlContainerDataToList (ContainerDataFinalNoExtra a) = a

  containerToList
    :: Container a a
    -> NonEmpty a
  containerToList (Container initial rest) = initial <| containerDataToList rest
  containerToList (ContainerNoInitial rest) = containerDataToList rest
  containerToList (ContainerSingle single) = NE.singleton single

  containerDataToList
    :: ContainerData a a
    -> NonEmpty a
  containerDataToList (ContainerData a b rest) = a <| b <| containerDataToList rest
  containerDataToList (ContainerDataNoExtra a rest) = a <| containerDataToList rest
  containerDataToList (ContainerDataFinal a b) = a <| NE.singleton b
  containerDataToList (ContainerDataFinalNoExtra a) = NE.singleton a

  ------------------

  letBindingTypesToContainer
    :: LetBindingTypes
    -> Container Var Text
  letBindingTypesToContainer (LetBindingNonVar expr) = exprTextToContainer expr
  letBindingTypesToContainer (LetBindingRef expr) = exprRefToContainer expr
  letBindingTypesToContainer (LetBindingRec expr) = exprRecToContainer expr
  letBindingTypesToContainer (LetBindingRefRec expr) = exprRefRecToContainer expr

  exprTextToContainer
    :: ExprText
    -> Container a Text
  exprTextToContainer (ExprText text) = ContainerSingle text

  exprRefToContainer
    :: ExprRef
    -> Container Var Text
  exprRefToContainer (ExprRef text rest) = Container text $ exprRefDataToContainerData rest
  exprRefToContainer (ExprRefNoText rest) = ContainerNoInitial $ exprRefDataToContainerData rest

  exprRefDataToContainerData
    :: ExprRefData
    -> ContainerData Var Text
  exprRefDataToContainerData (ExprRefData var text rest) = ContainerData var text $ exprRefDataToContainerData rest
  exprRefDataToContainerData (ExprRefDataNoText var rest) = ContainerDataNoExtra var $ exprRefDataToContainerData rest
  exprRefDataToContainerData (ExprRefDataFinal var text) = ContainerDataFinal var text
  exprRefDataToContainerData (ExprRefDataFinalNoText var) = ContainerDataFinalNoExtra var

  exprRecToContainer
    :: ExprRec
    -> Container Var Text
  exprRecToContainer (ExprRec var text rest) = Container text $ exprRecDataToContainerData var rest
  exprRecToContainer (ExprRecNoText var rest) = ContainerNoInitial $ exprRecDataToContainerData var rest

  exprRecDataToContainerData
    :: Var
    -> ExprRecData
    -> ContainerData Var Text
  exprRecDataToContainerData var (ExprRecData text rest) = ContainerData var text $ exprRecDataToContainerData var rest
  exprRecDataToContainerData var (ExprRecDataNoText rest) = ContainerDataNoExtra var $ exprRecDataToContainerData var rest
  exprRecDataToContainerData var (ExprRecDataFinal text) = ContainerDataFinal var text
  exprRecDataToContainerData var ExprRecDataFinalNoText = ContainerDataFinalNoExtra var

  exprRefRecToContainer
    :: ExprRefRec
    -> Container Var Text
  exprRefRecToContainer (ExprRefRec var text rest) = Container text $ exprRefRecDataToContainerData var rest
  exprRefRecToContainer (ExprRefRecNoText var rest) = ContainerNoInitial $ exprRefRecDataToContainerData var rest

  exprRefRecDataToContainerData
    :: Var
    -> ExprRefRecData
    -> ContainerData Var Text
  exprRefRecDataToContainerData recVar (ExprRefRecRefData var text rest) = ContainerData var text $ exprRefRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRefDataNoText var rest) = ContainerDataNoExtra var $ exprRefRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRecData text rest) = ContainerData recVar text $ exprRefRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRecDataNoText rest) = ContainerDataNoExtra recVar $ exprRefRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRefDataSwitch var text rest) = ContainerData var text $ exprRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRefDataSwitchNoText var rest) = ContainerDataNoExtra var $ exprRecDataToContainerData recVar rest
  exprRefRecDataToContainerData recVar (ExprRefRecRecDataSwitch text rest) = ContainerData recVar text $ exprRefDataToContainerData rest
  exprRefRecDataToContainerData recVar (ExprRefRecRecDataSwitchNoText rest) = ContainerDataNoExtra recVar $ exprRefDataToContainerData rest

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

  exprRef
    :: Text
    -> (ExprRefData -> ExprRef)
  exprRef = ExprRef

  exprRefNoText
    :: ExprRefData
    -> ExprRef
  exprRefNoText = ExprRefNoText

  exprRefData
    :: Var
    -> Text
    -> (ExprRefData -> ExprRefData)
  exprRefData = ExprRefData

  exprRefDataNoText
    :: Var
    -> (ExprRefData -> ExprRefData)
  exprRefDataNoText = ExprRefDataNoText

  exprRefDataFinal
    :: Var
    -> Text
    -> ExprRefData
  exprRefDataFinal = ExprRefDataFinal

  exprRefDataFinalNoText
    :: Var
    -> ExprRefData
  exprRefDataFinalNoText = ExprRefDataFinalNoText

  container
    :: b
    -> (ContainerData a b -> Container a b)
  container = Container

  containerNoInitial
    :: ContainerData a b
    -> Container a b
  containerNoInitial = ContainerNoInitial

  containerSingle
    :: b
    -> Container a b
  containerSingle = ContainerSingle

  containerData
    :: a
    -> b
    -> (ContainerData a b -> ContainerData a b)
  containerData = ContainerData

  containerDataNoExtra
    :: a
    -> (ContainerData a b -> ContainerData a b)
  containerDataNoExtra = ContainerDataNoExtra

  containerDataFinal
    :: a
    -> b
    -> ContainerData a b
  containerDataFinal = ContainerDataFinal

  containerDataFinalNoExtra
    :: a
    -> ContainerData a b
  containerDataFinalNoExtra = ContainerDataFinalNoExtra

-------------------------------------------

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

  flattenTuple
    :: ((a, b), c)
    -> (a, b, c)
  flattenTuple ((a, b), c) = (a, b, c)

  inverseDistributeEither
    :: (Either a b, c)
    -> Either (a, c) (b, c)
  inverseDistributeEither (Left a, c) = Left (a, c)
  inverseDistributeEither (Right b, c) = Right (b, c)

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
    -> Either b c
  mapLetBindingsLeft fn lb = letBindingValue . eitherToLetBinding . first (fmap fn . embedLetBinding) $ letBindingToEither lb

  mapLetExprEitherLeft
    :: (LetBinding a -> b)
    -> LetExpr (Either a c) d
    -> LetExpr (Either b c) d
  mapLetExprEitherLeft fn = firstLetBindings (mapLetBindingsLeft fn)

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
