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

module Lib where

import Data.Kind (Constraint, Type)
import Data.Type.Equality ( type (~) )

type Morphism object_kind = object_kind -> object_kind -> Type

type Category :: forall {k}. Morphism k -> Constraint
class Category morphism where
  type ObjectConstraint morphism :: i -> Constraint
  id :: ObjectConstraint morphism a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)

instance Category (->) where
  type ObjectConstraint (->) = Vacuous
  id x = x
  (.) f g x = f (g x)

type Vacuous :: k -> Constraint
class Vacuous a
instance Vacuous a

type Functor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class
    ( Category src_morphism
    , Category tgt_morphism
    , LiftObjConstr src_morphism tgt_morphism f
    )
    => Functor src_morphism tgt_morphism f where
  fmap
    :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b)
    => (a `src_morphism` b) -> (f a `tgt_morphism` f b)

-- forall a. ObjectConstraint src_morphism a => ObjectConstraint tgt_morphism (f a)
-- the line above does not work, see https://gitlab.haskell.org/ghc/ghc/-/issues/16123#note_167743
-- instead we use the workaround below:
type LiftObjConstr :: Morphism i -> Morphism j -> (i -> j) -> Constraint
type LiftObjConstr src_morphism tgt_morphism f =
  (forall objConstr a.
     ( objConstr ~ ObjectConstraint tgt_morphism
     , ObjectConstraint src_morphism a
     )
     => objConstr (f a)
  )

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

instance (Functor (->) (->) (p a)) => Functor (Flip (->)) (Flip (->)) (p a) where
  fmap = Flip . fmap . runFlip

instance Category morphism => Category (Flip morphism) where
  type ObjectConstraint (Flip morphism) = ObjectConstraint morphism
  id = Flip id
  (.) (Flip f) (Flip g) = Flip (g . f)

instance 
    ( Functor (->) (NatTrans (->) (->)) p
    , LiftObjConstr (Flip (->)) (NatTrans (Flip (->)) (Flip (->))) p
    )
    => Functor (Flip (->)) (NatTrans (Flip (->)) (Flip (->))) p
    where
  fmap f = Nat (Flip (runNat (fmap @(->) @(NatTrans (->) (->)) (runFlip f))))