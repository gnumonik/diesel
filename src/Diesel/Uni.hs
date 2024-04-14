{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- for testing th



{-# LANGUAGE DerivingStrategies #-}


module Diesel.Uni where

import qualified Data.Kind as GHC

import Data.GADT.Compare (GEq(..))
import Data.Constraint.Extras (Has (..))

import Diesel.Type
import Data.Constraint (Dict(..))

-- for testing th
import Data.String (IsString)
import Data.Proxy (Proxy)
import Prettyprinter
import Type.Reflection (Typeable, typeRep)

{-
    Class for things-that-can-be-constants in a given universe.

    This is the base class on which nearly every other Diesel class
    depends. Every constructor of `uni` must have an instance,
    and the `ty` parameter must be unique. (This is enforced by
    `Closed`).

-}
type KnownIn ::  (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Constraint
class KnownIn uni ty where
  knownIn :: uni ty


class KnownIn uni t  => IsInner uni (t :: GHC.Type) where
  type TypeOf t :: (Type GHC.Type)
  toType :: uni t -> TyRep uni (TypeOf t)
  fromType :: TyRep uni (TypeOf t) -> uni t

instance KnownIn uni (T t) => IsInner uni (T t) where
  type TypeOf (T t) = Ty t
  toType = RepT
  fromType (RepT uni) = uni

instance KnownIn uni (K f) => IsInner uni (K f) where
  type TypeOf (K f) = TyCon (K f)
  toType = RepK
  fromType (RepK uni) = uni


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
type TypeIn :: forall (k :: GHC.Type). (GHC.Type -> GHC.Type) -> Type k -> GHC.Constraint
class (GEq uni) => TypeIn uni ty where
  data Inner uni ty :: GHC.Type
  rep :: TyRep uni ty

instance (GEq uni, KnownIn uni (K f), IsInner uni (K f), TypeOf (K f) ~ TyCon (K f)) => TypeIn uni (TyCon (K f)) where
  newtype Inner uni (TyCon (K f)) = TyConProxy (Proxy f) deriving (Show, Eq, Ord)
  rep = RepK $ knownIn  @uni @(K f)

instance Typeable f => Pretty (Inner uni (TyCon (K f))) where
  pretty _ = viaShow $ typeRep @f


instance (GEq uni, KnownIn uni (T t)) => TypeIn uni (Ty (t :: GHC.Type)) where
  newtype Inner uni (Ty t) = Val t deriving (Eq)
  rep = RepT knownIn

deriving newtype instance Num t => Num (Inner uni (Ty t))
deriving newtype instance IsString t => IsString (Inner uni (Ty t))
deriving newtype instance Show t => Show (Inner uni (Ty t))
deriving newtype instance Ord t => Ord (Inner uni (Ty t))
deriving newtype instance Pretty t => Pretty (Inner uni (Ty t))


instance (
    GEq uni,
    KnownIn uni (K f),
    TypeIn uni ty)
  => TypeIn uni (TyCon (K  (f :: GHC.Type -> GHC.Type)) :@ ty) where
    newtype Inner uni (TyCon (K f) :@ ty) = Con1 (f (Inner uni ty))
    rep =  knownIn :@@ rep

deriving newtype instance ( Show (f (Inner uni t))) => Show (Inner uni (TyCon (K f) :@ t))
deriving newtype instance ( Pretty (f (Inner uni t))) => Pretty (Inner uni (TyCon (K f) :@ t))
deriving newtype instance (forall x. Eq x => Eq (f x), Eq (Inner uni t)) => Eq (Inner uni (TyCon (K f) :@ t))
deriving newtype instance (forall x. Ord x => Ord (f x),forall x. Eq x => Eq (f x), Ord (Inner uni t)) => Ord (Inner uni (TyCon (K f) :@ t))



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

instance GEq uni => TypeIn uni 'Star where
  data Inner uni Star = StarV deriving (Show, Eq, Ord)
  rep = StarRep

{-
   Constraints over an `Inner`. This is a utility class to implement `Each`.

   Because our uni GADT must be parameterized by things of kind (Diesel.Type k)
   - specifically, by the "base case" `Ty` (i.e. they cannot be functions)
   we cannot use `Has` directly to walk under the existential, so we need this.
-}

class (IsInner uni t, TypeIn uni (TypeOf t), c (Inner uni (TypeOf t))) => InnerC c uni t where
  innerDict :: Dict (c (Inner uni (TypeOf t)))


instance (IsInner uni t, TypeIn uni (TypeOf t), c (Inner uni (TypeOf t))) => InnerC c uni t where
  innerDict = Dict



{-
   Universal quantification over the ground types of a type universe.
-}
class Has (InnerC c uni) uni => Each (c :: GHC.Type  -> GHC.Constraint) uni where
  each :: forall t r. uni t -> (c (Inner uni (TypeOf t)) => r) -> r
  each uni f = case argDict @(InnerC c uni) @uni uni of
    Dict ->  case innerDict @c @uni @t  of
     (Dict :: Dict (c (Inner uni ty))) -> f
instance Has (InnerC c uni) uni => Each c uni
