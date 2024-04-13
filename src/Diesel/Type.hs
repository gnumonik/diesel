{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase, OverloadedStrings #-}


module Diesel.Type where

import qualified Data.Kind as GHC
import Data.Type.Equality (type (:~:)(Refl))
import Data.GADT.Compare
import Type.Reflection (Typeable, typeRep)
import Prettyprinter

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
  | TyCon t
  | Type t :~> Type t
  | (Type t) :& (Type t)
  | (Type t) :| (Type t)
  | List (Type t)
  -- A type expression.
  | Type t :@ Type t
  deriving (Show, Eq)
infixr 0 :~>
infixr 3 :&
infixr 2 :|
infixl 9 :@

data K a

instance Typeable k => Show (K k) where
  show _ = "K " <> show (typeRep @k)


type TyK a = Ty (K a)

{-
   Witnesses a type in a given universe.
-}
data TyRep :: forall (k :: GHC.Type). (Type k -> GHC.Type ) -> Type k ->  GHC.Type where
  TyRep :: uni (Ty k) -> TyRep uni (Ty k)
  TyConRep :: uni (TyCon (K f)) -> TyRep uni (TyCon (K f))
  (:~~>) :: TyRep uni k1 -> TyRep uni k2  -> TyRep uni (k1 :~> k2)
  (:&&) :: TyRep uni k1 -> TyRep uni k2 -> TyRep uni (k1 :& k2)
  (:||) :: TyRep uni k1 -> TyRep uni k2 -> TyRep uni (k1 :| k2)
  ListRep :: TyRep uni k1 -> TyRep uni (List k1)
  (:@@) :: uni (TyCon (K f)) -> TyRep uni a -> TyRep uni (TyCon (K f) :@ a)
infixl 9 :@@

deriving instance (forall tx. Show (uni tx)) => Show (TyRep uni t)

instance (forall tx. Pretty (uni tx)) => Pretty (TyRep uni t) where
  pretty = \case
    TyRep uni -> pretty uni
    TyConRep uni -> pretty uni
    t1 :~~> t2 -> pretty t1 <+> " ~> " <+> pretty t2
    t1 :&& t2  -> pretty t1 <+> " & " <+> pretty t2
    t1 :|| t2  -> pretty t1 <+> " | " <+> pretty t2
    ListRep t1 -> list [pretty t1]
    t1 :@@ t2  -> pretty t1 <+> " @ " <+> pretty t2



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


