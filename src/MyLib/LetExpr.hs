{-# LANGUAGE StarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}

module MyLib.LetExpr (LetExpr(..), ExprText, Container(..), ContainerShell(..), ContainerData, LetBinding, Var, RecursionAllowance(..), LetBindingTypesContainer(..), Normal(..), Factor(..), ContainerNormal(..),  bsToVar, exprTextToContainer, flattenTuple, letExprLetBind, letExprLetBindFinal, letBinding, textToExprText, exprTextToText, containerToList, letBindingValue, foldlContainerToList, foldlContainerDataToList, filterMapOrMapLetBinding, foldlLetExpr, firstLetBindings, varToBS, letBindingCaseVar, letBindingCaseVarBS, prependContainerData, normalToContainerData, ContainerSingle(..), letBindingTypesContainerToContainer) where

  import Data.Text (Text)
  import Data.List.NonEmpty (NonEmpty(..), (<|))
  import qualified Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.ByteString (ByteString)
  import Data.Foldable1 (fold1)

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

  data LetBindingTypesContainer
    = LetBindingContainerSingle (ContainerSingle Text)
    | LetBindingContainerFactor (ContainerFactor Var Text)
    | LetBindingContainerNormal (ContainerNormal Var Text)
    | LetBindingContainerFactorOrNormal (ContainerFactorOrNormal Var Text)

  --A container of two types of data, where the first type variable is the primary data type and the second type variable is the secondary data type. It can hold datum of the secondary data type before it holds a ContainerData of the same type variables, or it can just hold a ContainerData of the same type variables, or it can just hold a single datum of the secondary data type.
  data Container a b
    = Container (ContainerShell b (ContainerData a b))
    | ContainerSingle (ContainerSingle b)

  instance Functor (Container a) where
    fmap fn (Container (ContainerShell initial (ContainerData rest))) = Container (ContainerShell (fn initial) (ContainerData $ fmap (second fn) rest))
    fmap fn (Container (ContainerShellNoExtra (ContainerData rest))) = Container (ContainerShellNoExtra (ContainerData $ fmap (second fn) rest))
    fmap fn (ContainerSingle (ContainerSingleValue value)) = ContainerSingle . ContainerSingleValue $ fn value

  instance Bifunctor Container where
    bimap f g (Container rest) = Container $ bimap g (bimap f g) rest
    bimap _ g (ContainerSingle (ContainerSingleValue b)) = ContainerSingle $ ContainerSingleValue (g b)

  newtype ContainerSingle a
    = ContainerSingleValue a
    deriving Functor

  --A container of two types of data, where every constructor must at minimum hold one datum of the primary data type (i.e., the first type variable). It may additionally hold a datum of the secondary data type (e.g., the second type variable).
  newtype ContainerData a b
    = ContainerData (NonEmpty (Normal a b))
    deriving Functor

  instance Bifunctor ContainerData where
    bimap f g (ContainerData nonEmptyNormal) = ContainerData $ fmap (bimap f g) nonEmptyNormal

  data ContainerShell a b
    = ContainerShell a b
    | ContainerShellNoExtra b
    deriving Functor

  instance Bifunctor ContainerShell where
    bimap f g (ContainerShell a b) = ContainerShell (f a) (g b)
    bimap _ g (ContainerShellNoExtra b) = ContainerShellNoExtra (g b)

  newtype ContainerNormal a b
    = ContainerNormal (ContainerShell b (ContainerData a b))

  instance Functor (ContainerNormal a) where
    fmap f (ContainerNormal (ContainerShell b (ContainerData nonEmpty))) = ContainerNormal (ContainerShell (f b) (ContainerData $ fmap (second f) nonEmpty))
    fmap f (ContainerNormal (ContainerShellNoExtra (ContainerData nonEmpty))) = ContainerNormal (ContainerShellNoExtra (ContainerData $ fmap (second f) nonEmpty))

  instance Bifunctor ContainerNormal where
    bimap f g (ContainerNormal (ContainerShell initial (ContainerData rest))) = ContainerNormal (ContainerShell (g initial) (ContainerData $ fmap (bimap f g) rest))
    bimap f g (ContainerNormal (ContainerShellNoExtra (ContainerData rest))) = ContainerNormal (ContainerShellNoExtra (ContainerData $ fmap (bimap f g) rest))

  data ContainerFactor a b
    = ContainerFactor a (ContainerShell b (NonEmpty (Factor b)))

  instance Functor (ContainerFactor a) where
    fmap f (ContainerFactor factor (ContainerShell initial rest)) = ContainerFactor factor (ContainerShell (f initial) $ fmap (fmap f) rest)
    fmap f (ContainerFactor factor (ContainerShellNoExtra rest)) = ContainerFactor factor (ContainerShellNoExtra $ fmap (fmap f) rest)

  instance Bifunctor ContainerFactor where
    bimap f g (ContainerFactor factor (ContainerShell initial rest)) = ContainerFactor (f factor) (ContainerShell (g initial) $ fmap (fmap g) rest)
    bimap f g (ContainerFactor factor (ContainerShellNoExtra rest)) = ContainerFactor (f factor) (ContainerShellNoExtra $ fmap (fmap g) rest)

  data ContainerFactorOrNormal a b
    = ContainerFactorOrNormal a (ContainerShell b (ContainerFactorOrNormalData a b))

  instance Functor (ContainerFactorOrNormal a) where
    fmap f (ContainerFactorOrNormal factor (ContainerShell initial rest)) = ContainerFactorOrNormal factor (ContainerShell (f initial) $ second f rest)
    fmap f (ContainerFactorOrNormal factor (ContainerShellNoExtra rest)) = ContainerFactorOrNormal factor (ContainerShellNoExtra $ second f rest)

  instance Bifunctor ContainerFactorOrNormal where
    bimap f g (ContainerFactorOrNormal factor (ContainerShell initial rest)) = ContainerFactorOrNormal (f factor) (ContainerShell (g initial) $ bimap f g rest)
    bimap f g (ContainerFactorOrNormal factor (ContainerShellNoExtra rest)) = ContainerFactorOrNormal (f factor) (ContainerShellNoExtra $ bimap f g rest)

  data ContainerFactorOrNormalData a b
    = ContainerFactorOrNormalDataFactor (Factor b) (ContainerFactorOrNormalData a b)
    | ContainerFactorOrNormalDataNormal (Normal a b) (ContainerFactorOrNormalData a b)
    | ContainerFactorOrNormalDataFactorToNormalSwitch (Factor b) (NonEmpty (Normal a b))
    | ContainerFactorOrNormalDataNormalToFactorSwitch (Normal a b) (NonEmpty (Factor b))
    deriving Functor

  instance Bifunctor ContainerFactorOrNormalData where
    bimap f g (ContainerFactorOrNormalDataFactor factor rest) = ContainerFactorOrNormalDataFactor (fmap g factor) $ bimap f g rest
    bimap f g (ContainerFactorOrNormalDataNormal normal rest) = ContainerFactorOrNormalDataNormal (bimap f g normal) $ bimap f g rest
    bimap f g (ContainerFactorOrNormalDataFactorToNormalSwitch factor nonEmptyNormal) = ContainerFactorOrNormalDataFactorToNormalSwitch (fmap g factor) $ fmap (bimap f g) nonEmptyNormal
    bimap f g (ContainerFactorOrNormalDataNormalToFactorSwitch normal nonEmptyFactor) = ContainerFactorOrNormalDataNormalToFactorSwitch (bimap f g normal) $ fmap (fmap g) nonEmptyFactor

  data Factor a
    = Factor a
    | FactorNoExtra
    deriving Functor

  data Normal a b
    = Normal a b
    | NormalNoExtra a
    deriving Functor

  instance Bifunctor Normal where
    bimap f g (Normal a b) = Normal (f a) (g b)
    bimap f _ (NormalNoExtra a) = NormalNoExtra (f a)

  --A let expression that has at least one let binding, which binds a variable to a body, and a final expression that is to be beta reduced by the preceding let bindings.
  data LetExpr dataType finalExpr
    = LetBind (LetBinding dataType) (LetExpr dataType finalExpr)
    | LetBindFinal (LetBinding dataType) finalExpr
    deriving Functor

  instance Bifunctor LetExpr where
    bimap f g (LetBind (LetBinding var expr) rest) = LetBind (LetBinding var $ f expr) $ bimap f g rest
    bimap f g (LetBindFinal (LetBinding var expr) finalExpr) = LetBindFinal (LetBinding var $ f expr) $ g finalExpr

  --------------------

  textToExprText
    :: Text
    -> ExprText
  textToExprText = ExprText

  exprTextToText
    :: ExprText
    -> Text
  exprTextToText (ExprText text) = text

  bsToVar
    :: ByteString
    -> Var
  bsToVar = Var

  varToBS
    :: Var
    -> ByteString
  varToBS (Var bs) = bs

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
  foldlContainerToList (Container (ContainerShell b rest)) = b <> foldlContainerDataToList rest
  foldlContainerToList (Container (ContainerShellNoExtra rest)) = foldlContainerDataToList rest
  foldlContainerToList (ContainerSingle (ContainerSingleValue b)) = b

  foldlContainerDataToList
    :: Semigroup a
    => ContainerData a a
    -> a
  foldlContainerDataToList (ContainerData nonEmpty) = fold1 $ fmap normalConcat nonEmpty

  containerToList
    :: Semigroup a
    => Container a a
    -> NonEmpty a
  containerToList (Container (ContainerShell initial rest)) = initial <| containerDataToList rest
  containerToList (Container (ContainerShellNoExtra rest)) = containerDataToList rest
  containerToList (ContainerSingle (ContainerSingleValue single)) = NE.singleton single

  containerDataToList
    :: Semigroup a
    => ContainerData a a
    -> NonEmpty a
  containerDataToList (ContainerData nonEmpty) = fmap normalConcat nonEmpty

  ------------------

  exprTextToContainer
    :: ExprText
    -> Container a Text
  exprTextToContainer (ExprText text) = ContainerSingle (ContainerSingleValue text)

 ----------------------------------------------------

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

  foldlLetExpr
    :: (b -> LetBinding a -> b)
    -> b
    -> LetExpr a c
    -> b
  foldlLetExpr fn accum (LetBind lb rest) = foldlLetExpr fn (fn accum lb) rest
  foldlLetExpr fn accum (LetBindFinal lb _) = fn accum lb

  firstLetBindings
    :: (LetBinding a -> c)
    -> LetExpr a b
    -> LetExpr c b
  firstLetBindings fnLB (LetBind lb next) = LetBind (fmap (const (fnLB lb)) lb) $ firstLetBindings fnLB next
  firstLetBindings fnLB (LetBindFinal lb finalExpression) = LetBindFinal (fmap (const (fnLB lb)) lb) finalExpression

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

  ------

  factorToNormal
    :: a
    -> Factor b
    -> Normal a b
  factorToNormal a (Factor b) = Normal a b
  factorToNormal a FactorNoExtra = NormalNoExtra a

  normalConcat
    :: Semigroup a
    => Normal a a
    -> a
  normalConcat (Normal a b) = a <> b
  normalConcat (NormalNoExtra a) = a

  prependContainerData
    :: Normal a b
    -> ContainerData a b
    -> ContainerData a b
  prependContainerData normal (ContainerData current) = ContainerData $ normal <| current

  normalToContainerData
    :: Normal a b
    -> ContainerData a b
  normalToContainerData = ContainerData . NE.singleton

  containerFactorToContainer
    :: ContainerFactor a b
    -> Container a b
  containerFactorToContainer (ContainerFactor factor (ContainerShell initial rest)) = Container . ContainerShell initial . ContainerData $ fmap (factorToNormal factor) rest
  containerFactorToContainer (ContainerFactor factor (ContainerShellNoExtra rest)) = Container . ContainerShellNoExtra . ContainerData $ fmap (factorToNormal factor) rest

  containerNormalToContainer
    :: ContainerNormal a b
    -> Container a b
  containerNormalToContainer (ContainerNormal rest) = Container rest

  containerFactorOrNormalToContainer
    :: ContainerFactorOrNormal a b
    -> Container a b
  containerFactorOrNormalToContainer (ContainerFactorOrNormal factor (ContainerShell initial rest)) = Container (ContainerShell initial $ containerFactorOrNormalDataToContainerData factor rest)
  containerFactorOrNormalToContainer (ContainerFactorOrNormal factor (ContainerShellNoExtra rest)) = Container (ContainerShellNoExtra $ containerFactorOrNormalDataToContainerData factor rest)

  containerFactorOrNormalDataToContainerData
    :: a
    -> ContainerFactorOrNormalData a b
    -> ContainerData a b
  containerFactorOrNormalDataToContainerData factor (ContainerFactorOrNormalDataFactor factorValue rest) = prependContainerData (factorToNormal factor factorValue) $ containerFactorOrNormalDataToContainerData factor rest
  containerFactorOrNormalDataToContainerData factor (ContainerFactorOrNormalDataNormal normalValue rest) = prependContainerData normalValue $ containerFactorOrNormalDataToContainerData factor rest
  containerFactorOrNormalDataToContainerData factor (ContainerFactorOrNormalDataFactorToNormalSwitch factorValue rest) = ContainerData $ factorToNormal factor factorValue <| rest
  containerFactorOrNormalDataToContainerData factor (ContainerFactorOrNormalDataNormalToFactorSwitch normalValue rest) = ContainerData $ normalValue <| fmap (factorToNormal factor) rest

  letBindingTypesContainerToContainer
    :: LetBindingTypesContainer
    -> Container Var Text
  letBindingTypesContainerToContainer (LetBindingContainerSingle containerSingle) = ContainerSingle containerSingle
  letBindingTypesContainerToContainer (LetBindingContainerFactor containerFactor) = containerFactorToContainer containerFactor
  letBindingTypesContainerToContainer (LetBindingContainerNormal containerNormal) = containerNormalToContainer containerNormal
  letBindingTypesContainerToContainer (LetBindingContainerFactorOrNormal containerFactorOrNormal) = containerFactorOrNormalToContainer containerFactorOrNormal
