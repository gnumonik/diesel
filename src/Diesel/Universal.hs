{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}

{-# LANGUAGE LambdaCase, OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Diesel.Universal where

import qualified Data.Kind as GHC

import Data.GADT.Compare (GEq (..))
import Data.Type.Equality (type (:~:)(Refl))
import Diesel.Type ( Type(List, (:|), (:&), (:~>)), TyRep )
import Prettyprinter

data Universal :: (GHC.Type -> GHC.Type) -> Type t -> GHC.Type where
  -- pair stuff
  FstPair :: forall uni a b. TyRep uni ((a :& b) :~> a) -> Universal uni ((a :& b) :~> a)
  SndPair :: forall uni a b. TyRep uni ((a :& b) :~> b) -> Universal uni ((a :& b) :~> b)
  InjPair :: forall uni a b. TyRep uni (a :~> b :~> (a :& b)) -> Universal uni (a :~> b :~> (a :& b))

  -- Sums
  InjL    :: forall uni l r. TyRep uni (l :~> (l :| r)) -> Universal uni (l :~> (l :| r))
  InjR    :: forall uni l r. TyRep uni (r :~> (l :| r)) -> Universal uni (r :~> (l :| r))
  Switch  :: forall uni l r x. TyRep uni ((l :~> x) :~> (r :~> x) :~> (l :| r) :~> x) -> Universal uni ((l :~> x) :~> (r :~> x) :~> (l :| r) :~> x)

  -- List operations
  ConsList :: forall uni x. TyRep uni (x :~> List x :~> List x) -> Universal uni (x :~> List x :~> List x)
  NilList :: forall uni x. TyRep uni (List x) -> Universal uni (List x)
  UnconsList :: forall uni x. TyRep uni (List x :~> (List x :| (x :& List x))) -> Universal uni (List x :~> (List x :| (x :& List x)))
  FoldrList :: forall uni a b. TyRep uni ((a :~> b :~> b) :~> b :~> List a :~> b) -> Universal uni ((a :~> b :~> b) :~> b :~> List a :~> b)

deriving instance (forall tx. Show (TyRep uni tx), forall tx. Show (uni tx)) => Show (Universal uni t)

instance (forall tx. Pretty (TyRep uni tx), forall tx. Pretty (uni tx)) => Pretty (Universal uni t) where
  pretty = \case
    FstPair _ -> "fst"
    SndPair _ -> "snd"
    InjPair _ -> "pair"
    InjL _ -> "inl"
    InjR _ -> "inr"
    Switch _ -> "switch"
    ConsList _ -> "cons"
    NilList _ -> "nil"
    UnconsList _ -> "uncons"
    FoldrList _ -> "foldr"


typeOfUniversal :: Universal uni t -> TyRep uni t
typeOfUniversal = \case
  FstPair r -> r
  SndPair r -> r
  InjPair r -> r
  InjL r -> r
  InjR r -> r
  Switch r -> r
  ConsList r -> r
  NilList r -> r
  UnconsList r -> r
  FoldrList r -> r


instance (GEq (TyRep uni), GEq uni) => GEq (Universal uni) where
  geq (FstPair a) (FstPair b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (SndPair a) (SndPair b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (InjPair a) (InjPair b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (InjL a) (InjL b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (InjR a) (InjR b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (Switch a) (Switch b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (ConsList a) (ConsList b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (NilList a) (NilList b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (UnconsList a) (UnconsList b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq (FoldrList a) (FoldrList b) = case geq a b of
    Nothing -> Nothing
    Just Refl -> Just Refl
  geq _ _ = Nothing
