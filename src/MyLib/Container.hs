{-# LANGUAGE DeriveFunctor #-}

module MyLib.Container(Container(..), LetBindingTypesContainer(..), ContainerShell(..), ContainerNormal(..), ContainerData(..), ContainerSingle(..), Normal(..), containerToList, containerNormalToContainer, letBindingTypesContainerToContainer, containerToLetBindingTypes, prependContainerData, normalToContainerData, foldlContainerToList) where

  import Data.Text (Text)
  import Data.List.NonEmpty (NonEmpty(..), (<|))
  import qualified Data.List.NonEmpty as NE
  import Data.Bifunctor
  import Data.Foldable1 (fold1)
  import MyLib.LetExpr

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
    fmap fn (Container containerShell) = Container $ bimap fn (second fn) containerShell
    fmap fn (ContainerSingle containerSingle) = ContainerSingle $ fmap fn containerSingle

  instance Bifunctor Container where
    bimap f g (Container rest) = Container $ bimap g (bimap f g) rest
    bimap _ g (ContainerSingle containerSingle) = ContainerSingle $ fmap g containerSingle

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
    fmap f (ContainerNormal containerShell) = ContainerNormal $ bimap f (fmap f) containerShell

  instance Bifunctor ContainerNormal where
    bimap f g (ContainerNormal containerShell) = ContainerNormal (bimap g (bimap f g) containerShell)

  data ContainerFactor a b
    = ContainerFactor a (ContainerShell b (ContainerFactorData b))

  instance Functor (ContainerFactor a) where
    fmap f (ContainerFactor factor containerShell) = ContainerFactor factor $ bimap f (fmap f) containerShell

  instance Bifunctor ContainerFactor where
    bimap f g (ContainerFactor factor containerShell) = ContainerFactor (f factor) $ bimap g (fmap g) containerShell

  newtype ContainerFactorData a
    = ContainerFactorData (NonEmpty (Factor a))
    deriving Functor

  data ContainerFactorOrNormal a b
    = ContainerFactorOrNormal a (ContainerShell b (ContainerFactorOrNormalData a b))

  instance Functor (ContainerFactorOrNormal a) where
    fmap f (ContainerFactorOrNormal factor containerShell) = ContainerFactorOrNormal factor $ bimap f (second f) containerShell

  instance Bifunctor ContainerFactorOrNormal where
    bimap f g (ContainerFactorOrNormal factor containerShell) = ContainerFactorOrNormal (f factor) $ bimap g (bimap f g) containerShell

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

  foldlContainerToList
    :: Semigroup a
    => Container a a
    -> a
  foldlContainerToList (Container (ContainerShell b (ContainerData nonEmpty))) = b <> fold1 (fmap normalConcat nonEmpty)
  foldlContainerToList (Container (ContainerShellNoExtra (ContainerData nonEmpty))) = fold1 $ fmap normalConcat nonEmpty
  foldlContainerToList (ContainerSingle (ContainerSingleValue b)) = b

  containerToList
    :: Semigroup a
    => Container a a
    -> NonEmpty a
  containerToList (Container (ContainerShell initial (ContainerData nonEmpty))) = initial <| fmap normalConcat nonEmpty
  containerToList (Container (ContainerShellNoExtra (ContainerData nonEmpty))) = fmap normalConcat nonEmpty
  containerToList (ContainerSingle (ContainerSingleValue single)) = NE.singleton single

  factorToNormal
    :: a
    -> Factor b
    -> Normal a b
  factorToNormal a (Factor b) = Normal a b
  factorToNormal a FactorNoExtra = NormalNoExtra a

  normalToEitherFactorNormal
    :: Eq a
    => a
    -> Normal a b
    -> Either (Factor b)
              (Normal a b)
  normalToEitherFactorNormal match normal@(Normal a b) =
    if match == a
    then Left $ Factor b
    else Right normal
  normalToEitherFactorNormal match normal@(NormalNoExtra a) =
    if match == a
    then Left FactorNoExtra
    else Right normal

  containerDataToContainerFactorOrNormalData
    :: Eq a
    => a
    -> ContainerData a b
    -> Either (ContainerData a b)
              (Either (ContainerFactorData b)
                      (ContainerFactorOrNormalData a b))
  containerDataToContainerFactorOrNormalData match (ContainerData (normal :| [])) = case normalToEitherFactorNormal match normal of
    Left factor -> Right . Left . ContainerFactorData $ NE.singleton factor
    Right norm -> Left . ContainerData $ NE.singleton norm
  containerDataToContainerFactorOrNormalData match (ContainerData (normal :| (next : rest))) =
    let
      reversedNormalToFactorOrNormal
        :: Eq a
        => a
        -> ContainerData a b
        -> NonEmpty (Normal a b)
        -> Either (ContainerData a b)
                  (ContainerFactorOrNormalData a b)
      reversedNormalToFactorOrNormal match' processed@(ContainerData container) (normal' :| []) = case normalToEitherFactorNormal match' normal' of
        Left factor -> Right $ ContainerFactorOrNormalDataFactorToNormalSwitch factor container
        Right norm -> Left $ prependContainerData norm processed
      reversedNormalToFactorOrNormal match' processed@(ContainerData container) (normal' :| (next' : rest')) = case normalToEitherFactorNormal match' normal' of
        Left factor -> Right $ reversedNormalToFactorAndOrNormal match' (next' :| rest') $ ContainerFactorOrNormalDataFactorToNormalSwitch factor container
        Right norm -> reversedNormalToFactorOrNormal match' (prependContainerData norm processed) (next' :| rest')

      reversedFactorToFactorOrNormal
        :: Eq a
        => a
        -> ContainerFactorData b
        -> NonEmpty (Normal a b)
        -> Either (ContainerFactorData b)
                  (ContainerFactorOrNormalData a b)
      reversedFactorToFactorOrNormal match' processed@(ContainerFactorData container) (normal' :| []) = case normalToEitherFactorNormal match' normal' of
        Left factor -> Left $ prependContainerFactorData factor processed
        Right norm -> Right $ ContainerFactorOrNormalDataNormalToFactorSwitch norm container
      reversedFactorToFactorOrNormal match' processed@(ContainerFactorData container) (normal' :| (next' : rest')) = case normalToEitherFactorNormal match' normal' of
        Left factor -> reversedFactorToFactorOrNormal match' (prependContainerFactorData factor processed) (next' :| rest')
        Right norm -> Right $ reversedNormalToFactorAndOrNormal match' (next' :| rest') $ ContainerFactorOrNormalDataNormalToFactorSwitch norm container

      reversedNormalToFactorAndOrNormal
        :: Eq a
        => a
        -> NonEmpty (Normal a b)
        -> ContainerFactorOrNormalData a b
        -> ContainerFactorOrNormalData a b
      reversedNormalToFactorAndOrNormal match' (normal' :| []) processed = case normalToEitherFactorNormal match' normal' of
        Left factor -> ContainerFactorOrNormalDataFactor factor processed
        Right norm -> ContainerFactorOrNormalDataNormal norm processed
      reversedNormalToFactorAndOrNormal match' (normal' :| (next' : rest')) processed = reversedNormalToFactorAndOrNormal match' (next' :| rest') $ case normalToEitherFactorNormal match' normal' of
        Left factor -> ContainerFactorOrNormalDataFactor factor processed
        Right norm -> ContainerFactorOrNormalDataNormal norm processed
    in
    case normalToEitherFactorNormal match normal of
      Left factor -> case reversedFactorToFactorOrNormal match (ContainerFactorData $ NE.singleton factor) (next :| rest) of
        Left factor' -> Right $ Left factor'
        Right factorOrNormal' -> Right $ Right factorOrNormal'
      Right norm -> case reversedNormalToFactorOrNormal match (ContainerData $ NE.singleton norm) (next :| rest) of
        Left normal' -> Left normal'
        Right factorOrNormal' -> Right $ Right factorOrNormal'

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

  prependContainerFactorData
    :: Factor a
    -> ContainerFactorData a
    -> ContainerFactorData a
  prependContainerFactorData factor (ContainerFactorData current) = ContainerFactorData $ factor <| current

  normalToContainerData
    :: Normal a b
    -> ContainerData a b
  normalToContainerData = ContainerData . NE.singleton

  containerFactorToContainer
    :: ContainerFactor a b
    -> Container a b
  containerFactorToContainer (ContainerFactor factor containerShell) =
    let
      containerFactorDataToContainerData
        :: a
        -> ContainerFactorData b
        -> ContainerData a b
      containerFactorDataToContainerData match (ContainerFactorData nonEmpty) = ContainerData $ fmap (factorToNormal match) nonEmpty
    in
    Container $ second (containerFactorDataToContainerData factor) containerShell

  containerNormalToContainer
    :: ContainerNormal a b
    -> Container a b
  containerNormalToContainer (ContainerNormal rest) = Container rest

  containerFactorOrNormalToContainer
    :: ContainerFactorOrNormal a b
    -> Container a b
  containerFactorOrNormalToContainer (ContainerFactorOrNormal factor containerShell) = Container $ second (containerFactorOrNormalDataToContainerData factor) containerShell

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

  containerToLetBindingTypes
    :: LetBinding (Container Var Text)
    -> LetBinding LetBindingTypesContainer
  containerToLetBindingTypes lb =
    let
      fn
        :: Var
        -> Container Var Text
        -> LetBindingTypesContainer
      fn _ (ContainerSingle (ContainerSingleValue single)) = LetBindingContainerSingle $ ContainerSingleValue single
      fn match (Container (ContainerShell extra rest)) =
        case containerDataToContainerFactorOrNormalData match rest of
          Left ref -> LetBindingContainerNormal . ContainerNormal $ ContainerShell extra ref
          Right (Left rec) -> LetBindingContainerFactor . ContainerFactor match $ ContainerShell extra rec
          Right (Right refRec) -> LetBindingContainerFactorOrNormal . ContainerFactorOrNormal match $ ContainerShell extra refRec
      fn match (Container (ContainerShellNoExtra rest)) =
        case containerDataToContainerFactorOrNormalData match rest of
          Left ref -> LetBindingContainerNormal . ContainerNormal $ ContainerShellNoExtra ref
          Right (Left rec) -> LetBindingContainerFactor . ContainerFactor match $ ContainerShellNoExtra rec
          Right (Right refRec) -> LetBindingContainerFactorOrNormal . ContainerFactorOrNormal match $ ContainerShellNoExtra refRec
    in
    mapLetBinding fn lb
