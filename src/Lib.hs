{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Lib where

import Data.Kind (Constraint, Type)

type Morphism object_kind = object_kind -> object_kind -> Type

type Category :: forall {k}. Morphism k -> Constraint
class Category morphism where
  type ObjectConstraint morphism :: i -> Constraint
  id :: ObjectConstraint morphism a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)

instance Category (->) where
  type ObjectConstraint (->) = Vacuous (->)
  id x = x
  (.) f g x = f (g x)

type Vacuous :: Morphism k -> k -> Constraint
class Vacuous c a
instance Vacuous c a

type Functor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class
    ( Category src_morphism
    , Category tgt_morphism
    -- , forall a. ObjectConstraint src_morphism a => ObjectConstraint tgt_morphism (f a)
    -- the line above does not work, instead we use the workaround from https://gitlab.haskell.org/ghc/ghc/-/issues/14860#note_495352 in the line below:
    -- instead we use the workaround below:
    , forall a. ObjectConstraint src_morphism a => Obj tgt_morphism (f a)
    )
    => Functor src_morphism tgt_morphism f where
  fmap
    :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b)
    => (a `src_morphism` b) -> (f a `tgt_morphism` f b)

class    (ObjectConstraint x a) => Obj x a
instance (ObjectConstraint x a) => Obj x a

type NatTrans :: forall {i} {k}. Morphism i -> Morphism k -> Morphism (i -> k)
data NatTrans src_morphism tgt_morphism f g where
  Nat
    :: (Functor src_morphism tgt_morphism f, Functor src_morphism tgt_morphism g) 
    => { runNat :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) } 
    -> NatTrans src_morphism tgt_morphism f g

instance (Category src_morphism, Category tgt_morphism) => Category (NatTrans src_morphism tgt_morphism) where
  type ObjectConstraint (NatTrans src_morphism tgt_morphism) = Functor src_morphism tgt_morphism
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)

type Flip :: (i -> j -> Type) -> j -> i -> Type
newtype Flip p a b = Flip { runFlip :: p b a }

instance Functor (->) (NatTrans (->) (->)) p => Functor (->) (->) (Flip p a) where
  fmap f = Flip . runNat (fmap @(->) @(NatTrans (->) (->)) f) . runFlip

instance Category morphism => Category (Flip morphism) where
  type ObjectConstraint (Flip morphism) = ObjectConstraint morphism
  id = Flip id
  (.) (Flip f) (Flip g) = Flip (g . f)
