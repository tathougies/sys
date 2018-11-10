{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}

module Sys.Core.Util where

import           Sys.Core.Lang

import           Control.Comonad

import           Data.Functor.Classes
import qualified Data.HashSet as HS
import           Data.Hashable
import           Data.Hashable.Lifted
import           Data.Text (Text)

import           GHC.Generics

data WhereIn var (f :: * -> *)
  = ThePlicityOfTheArguments (Maybe (Perhaps var)) (Maybe (Perhaps var))
  deriving Show

data MoreSpecifically var (f :: * -> *)
  = Namely (WhereIn var f)
  | RightHere
  deriving Show

newtype Id a = Id a
  deriving (Show, Eq, Ord)

instance Eq1 Id where
  liftEq (==.) (Id a) (Id b) = a ==. b

instance Hashable1 Id where
  liftHashWithSalt hashWithSalt' salt (Id a) =
    hashWithSalt' salt a

data Error var f
  = CantUnify (Lang var Perhaps f) (Lang var Perhaps f) (MoreSpecifically var f)
  | VariableNameMismatch var var (MoreSpecifically var f)

data Perhaps f
  = Explicit f
  | Placeholder
  deriving (Show, Functor, Foldable, Traversable)

really :: Id f -> Perhaps f
really (Id a) = Explicit a

fromPerhaps :: Perhaps f -> Maybe f
fromPerhaps Placeholder = Nothing
fromPerhaps (Explicit f) = Just f

data TyCheckResult var f term
  = TyCheckResult
  { tyCheckTy      :: term
  , tyCheckErrors  :: [ Error var (TyCheckResult var f) ]
  , tyCheckAnn     :: f term
  } deriving (Functor, Foldable, Traversable)

instance Comonad f => Comonad (TyCheckResult var f) where
  extract ty = extract (tyCheckAnn ty)
  duplicate ty =
    let mk a = TyCheckResult (tyCheckTy ty) (tyCheckErrors ty) (a <$ tyCheckAnn ty)
    in TyCheckResult (mk (tyCheckTy ty)) (tyCheckErrors ty)
                     (fmap (extract . fmap mk) (duplicate (tyCheckAnn ty)))

data SourceDescription
  = WhileTypingTheTargetOfAnApplication !SourceDescription
  | WhileTypingTheArgumentOfAnApplication !SourceDescription
  | WhileInferringTheTypeOf !SourceDescription
  | TheNameOfTheArgument !SourceDescription
  | EncounteredAt !Location
  deriving (Show, Eq, Generic)

instance Hashable SourceDescription -- TODO make efficient

data FileOffs
  = FileOffs
  { foLine :: {-# UNPACK #-} !Word
  , foCol  :: {-# UNPACK #-} !Word
  } deriving (Show, Generic, Hashable, Eq)

data Location
  = SourceLoc
  { locFilePath  :: {-# UNPACK #-} !Text
  , locStartOffs :: {-# UNPACK #-} !FileOffs
  , locEndOffs   :: {-# UNPACK #-} !FileOffs
  }
  deriving (Show, Generic, Hashable, Eq)

type SourceLocation = HS.HashSet SourceDescription

class SysLocated f where
  location :: f a -> HS.HashSet SourceDescription
  sourcedFrom :: f a -> f a -> b -> f b

-- instance SysLocated f => SysLocated (TyCheckResult var f) where
--  location = location . tyCheckAnn
--   sourcedFrom a b x = a { 

tyLocation :: SysLocated f => TyCheckResult var f a -> SourceLocation
tyLocation = location . tyCheckAnn
