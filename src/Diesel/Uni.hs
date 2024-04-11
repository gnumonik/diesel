{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- for testing th
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveAnyClass, DeriveTraversable, DeriveFunctor #-}

module Diesel.Uni where

import qualified Data.Kind as GHC

import Data.GADT.Compare (GEq(..))
import Data.Constraint.Extras (Has (..))

import Diesel.Type
import Data.Constraint (Dict(..))

-- for testing th
import Diesel.TH.Derive
import Data.Type.Equality
import Data.Bifunctor (Bifunctor (..))

{-
    Class for things-that-can-be-constants in a given universe.

    This is the base class on which nearly every other Diesel class
    depends. Every constructor of `uni` must have an instance,
    and the `ty` parameter must be unique. (This is enforced by
    `Closed`).

-}
type KnownIn :: (Type k -> GHC.Type) -> Type k -> GHC.Constraint
class KnownIn uni ty where
  knownIn :: uni ty

{-
    Class of closed type universes. GEq guarantees that we can
    test equality. Has (KnownIn uni) can only be satisfied by a
    well-formed universe type.

    We don't really use this for anything directly & it mainly
    serves as a compile-time check that the universe really is closed.
-}
type Closed uni = (GEq uni, Has (KnownIn uni) uni)

{-
    Class for typeable things in a given universe.

    `Inner` is the workhorse of this library. It allows us to refer to
    specific Haskell types without directly mentioning them. It is
    an associated data family (rather than a type family) for
    injectivity and better inference.

    Because a well-formed uni will always be indexed by (Ty k), where
    `k` is something of kind GHC.Type, the Inner representation of
    (Ty k) will always be a constant.

    Users should never write instances for this, particularly because they
    cannot do so anyway. All of the valid instances should be derived from
    `KnownIn`.
-}
type TypeIn :: (Type k -> GHC.Type) -> Type k -> GHC.Constraint
class (GEq uni) => TypeIn uni ty where
  data Inner uni ty :: GHC.Type
  rep :: TyRep uni ty

instance (GEq uni, KnownIn uni (Ty t)) => TypeIn uni (Ty (t :: GHC.Type)) where
  newtype Inner uni (Ty t) = Val t deriving (Show, Eq)
  rep = TyRep knownIn

instance (GEq uni, TypeIn uni t1, TypeIn uni t2) => TypeIn uni (t1 :~> t2) where
  newtype Inner uni (t1 :~> t2) = Fun (Inner uni t1 -> Inner uni t2)
  rep = rep :~~> rep

instance (GEq uni, TypeIn uni a, TypeIn uni b) => TypeIn uni (a :& b) where
  data Inner uni (a :& b) = Inner uni a :/\ Inner uni b
  rep = rep :&& rep


instance (GEq uni, TypeIn uni a, TypeIn uni b) => TypeIn uni (a :| b) where
  data Inner uni (a :| b) = L (Inner uni a) | R  (Inner uni b)
  rep = rep :|| rep

instance (GEq uni, TypeIn uni a) => TypeIn uni (List a) where
  newtype Inner uni (Diesel.Type.List a) = ListVal [Inner uni a]
  rep = ListRep rep
{-
   Constraints over an `Inner`. This is a utility class to implement `Each`.

   Because our uni GADT must be parameterized by things of kind (Diesel.Type k)
   - specifically, by the "base case" `Ty` (i.e. they cannot be functions)
   we cannot use `Has` directly to walk under the existential, so we need this.
-}
class (c (Inner uni ty), TypeIn uni ty) => InnerC c uni ty where
  innerDict :: Dict (c (Inner uni ty))
  innerC :: forall r. TyRep uni ty -> (c (Inner uni ty) => r) -> r

instance (c (Inner uni t),  TypeIn uni t) => InnerC c uni t where
  innerDict = Dict
  innerC _ f = f

{-
   Universal quantification over the ground types of a type universe.
-}
class Has (InnerC c uni) uni => Each (c :: GHC.Type -> GHC.Constraint)  uni where
  each :: forall ty r. uni ty -> (c (Inner uni ty) => r) -> r
  each uni f = case argDict @(InnerC c uni) @uni uni of
    Dict ->  case innerDict @c @uni @ty  of
     (Dict :: Dict (c (Inner uni ty))) -> f
instance Has (InnerC c uni) uni => Each c uni

