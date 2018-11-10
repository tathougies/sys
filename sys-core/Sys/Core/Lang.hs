{-# LANGUAGE RankNTypes #-}
module Sys.Core.Lang where

import Control.Monad.Identity

import Data.Hashable
import Data.Hashable.Lifted
import Data.Functor.Classes

data Lev var constant recurs
  = LevBase -- Levity zero
  | LevLift !(recurs (Lev var constant recurs))
  | LevVar !(constant var)

data Builtin
  = AddUint8

data PrimType
  = PrimTypeUint8
  | PrimTypeUint16
  | PrimTypeUint32
  | PrimTypeUint64

  | PrimTypeInt8
  | PrimTypeInt16
  | PrimTypeInt32
  | PrimTypeInt64

  deriving Show

data Prim constant
  = PrimNum !(constant Integer)
    -- ^ A numeric value, the only primitive type

  | PrimBuiltin !(constant Builtin)
    -- ^ A builtin function

  | PrimType !(constant PrimType)
    -- ^ Primitive types (machine-width words)

data HoleId var constant
  = NamedHole !(constant var)
  | UnnamedHole !(constant Integer)

instance (Hashable1 constant, Hashable var) => Hashable (HoleId var constant) where
  hashWithSalt salt (NamedHole nm) =
    liftHashWithSalt hashWithSalt (salt `hashWithSalt` (1 :: Int)) nm
  hashWithSalt salt (UnnamedHole c) =
    liftHashWithSalt hashWithSalt (salt `hashWithSalt` (2 :: Int)) c

instance (Eq1 constant, Eq var) => Eq (HoleId var constant) where
  NamedHole   a == NamedHole   b = liftEq (==) a b
  UnnamedHole a == UnnamedHole b = liftEq (==) a b
  _ == _ = False

-- Nats
--
-- Nat : Type
-- Nat = inductive n => (b : Bin ** choose b Unit n)
--
-- z : Nat
-- z = ( O | Unit )
--
-- s :: Nat -> Nat
-- s n = collapse ( I | n )

-- Fin : Nat -> Type
-- Fin = (\n -> break n (\(b : Bin) (x : choose b Unit n) ->
--                            choose b Void

-- (=) : (?A : Type) -> (?a : A) -> (a : A) -> Type
-- (=) = ()
--
-- (b : x = y)

data Binding var
  = Reuse var
  | Introduce var
  deriving Show

data Lang var constant recurs
  = Ap  !(recurs (Lang var constant recurs))
        !(Maybe (constant var)) -- Optional name being bound
        !(recurs (Lang var constant recurs))
    -- ^ Function application
  | Lam !Bool {- Whether or not this is inferred -}
        !(constant (Binding var)) !(recurs (Lang var constant recurs))
        !(recurs (Lang var constant recurs))
    -- ^ Lambda abstraction, with typed binder

  | Pi !Bool {- Whether or not this should be inferred -}
       !(constant (Binding var)) !(recurs (Lang var constant recurs)) !(recurs (Lang var constant recurs))
    -- ^ The type of Lam

  | DPair !(constant var) !(recurs (Lang var constant recurs)) !(recurs (Lang var constant recurs))
    -- ^ The type of dependent pairs
  | Break !(recurs (Lang var constant recurs)) !(recurs (Lang var constant recurs))

  | Bin
    -- ^ Type of finite sets with two Elements
  | BinLeft | BinRight
  | Choose !(recurs (Lang var constant recurs))
           !(recurs (Lang var constant recurs))
           !(recurs (Lang var constant recurs))

  | Var !(constant var)
    -- ^ Variable binding

  | Prim !(recurs (Prim constant))

  | Levity
    -- ^ The type of levities

  | Type !(recurs (Lev var constant recurs))
    -- ^ The universe at levity

  | Hole !(HoleId var constant)
    -- ^ Named / unnamed holes

rewriteVarM :: (Applicative m, Traversable const, Traversable f)
            => (var -> m var') -> Lang var const f -> m (Lang var' const f)
rewriteVarM f (Ap fn nm arg) =
  Ap <$> traverse (rewriteVarM f) fn
     <*> traverse (traverse f) nm
     <*> traverse (rewriteVarM f) arg

rewriteVar :: (Traversable const, Traversable f)
           => (var -> var') -> Lang var const f -> Lang var' const f
rewriteVar f l =
  runIdentity (rewriteVarM (pure . f) l)

rewriteConstantM :: (Applicative m, Traversable f)
                 => (forall x. const x -> m (const' x))
                 -> Lang var const f -> m (Lang var const' f)
rewriteConstantM f (Ap fn nm arg) =
  Ap <$> traverse (rewriteConstantM f) fn
     <*> traverse f nm
     <*> traverse (rewriteConstantM f) arg

rewriteConstant :: Traversable f
                => (forall x. const x -> const' x)
                -> Lang var const f -> Lang var const' f
rewriteConstant f l =
  runIdentity (rewriteConstantM (pure . f) l)

rewriteRecursM :: (Monad m, Traversable const, Traversable recurs')
               => (forall x. recurs x -> m (recurs' x))
               -> Lang var const recurs -> m (Lang var const recurs')
rewriteRecursM f (Ap fn nm arg) =
  Ap <$> (traverse (rewriteRecursM f) =<< f fn)
     <*> pure nm
     <*> (traverse (rewriteRecursM f) =<< f arg)

rewriteRecurs :: (Traversable const, Traversable recurs')
              => (forall x. recurs x -> recurs' x)
              -> Lang var const recurs -> Lang var const recurs'
rewriteRecurs f l =
  runIdentity (rewriteRecursM (pure . f) l)
