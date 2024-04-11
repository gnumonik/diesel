{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}

module Diesel.Type where

import qualified Data.Kind as GHC
import Data.Type.Equality (type (:~:)(Refl))
import Data.GADT.Compare


{- Types in our language.

   A Type is either a primitive "ground type" (which must be of kind GHC.Type)
   or a function from Types to types.

   If the set of ground types is determined by a finitely enumable
   GADT with unique indices, we have a closed type universe.

   We never use this at the term level, but we use the promoted
   constructors. The point of this is that it lets us write
   typeclass instances that allow the constraint solver to
   distinguish ground terms from functions.
-}
data Type t
  = Ty t
  {- /\ A type constructor.
  -}
  | Type t :~> Type t
  | (Type t) :& (Type t)
  | (Type t) :| (Type t)
  | List (Type t)
  deriving (Show, Eq)
infixr 0 :~>
infixr 3 :&
infixr 2 :|

{-
   Witnesses a type in a given universe.
-}
data TyRep :: forall (k :: GHC.Type). (Type k -> GHC.Type ) -> Type k ->  GHC.Type where
  TyRep :: uni k -> TyRep uni k
  (:~~>) :: TyRep uni k1 -> TyRep uni k2  -> TyRep uni (k1 :~> k2)
  (:&&) :: TyRep uni k1 -> TyRep uni k2 -> TyRep uni (k1 :& k2)
  (:||) :: TyRep uni k1 -> TyRep uni k2 -> TyRep uni (k1 :| k2)
  ListRep :: TyRep uni k1 -> TyRep uni (List k1)



instance GEq uni => GEq (TyRep uni) where
  geq (TyRep t) (TyRep t') = case geq t t' of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (a :~~> b) (a' :~~> b') = case geq a a' of
    Nothing -> Nothing
    Just Refl -> case geq b b' of
      Just Refl -> Just Refl
      Nothing -> Nothing
  geq (a :&& b) (a' :&& b') = case geq a a' of
    Nothing -> Nothing
    Just Refl -> case geq b b' of
      Just Refl -> Just Refl
      Nothing -> Nothing
  geq (a :|| b) (a' :|| b') = case geq a a' of
    Nothing -> Nothing
    Just Refl -> case geq b b' of
      Just Refl -> Just Refl
      Nothing -> Nothing
  geq (ListRep a) (ListRep b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq _ _ = Nothing


