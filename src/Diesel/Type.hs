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
-}
data Type t
  = Ty t
  {- /\ A type constructor.
  -}
  | Type t :~> Type t
  {- /\ A function.
  -}
  deriving (Show, Eq)
infixr 0 :~>

{-
   Witnesses a type in a given universe.
-}
data TyRep :: forall (k :: GHC.Type). (Type k -> GHC.Type ) -> Type k ->  GHC.Type where
  TyRep :: uni k -> TyRep uni k
  (:~~>) :: TyRep uni k1 -> TyRep uni k2  -> TyRep uni (k1 :~> k2)

instance GEq uni => GEq (TyRep uni) where
  geq (TyRep t) (TyRep t') = case geq t t' of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (a :~~> b) (a' :~~> b') = case geq a a' of
    Nothing -> Nothing
    Just Refl -> case geq b b' of
      Just Refl -> Just Refl
      Nothing -> Nothing
  geq _ _ = Nothing

