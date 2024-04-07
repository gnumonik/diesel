{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Diesel.Expr where

import qualified Data.Kind as GHC

import Data.GADT.Compare (GEq (..))
import Data.Type.Equality (type (:~:)(Refl))

import Diesel.Type
import Diesel.Uni
import Data.Constraint.Extras

data Expr :: forall (t :: GHC.Type). (Type t -> GHC.Type) -> (Type t -> GHC.Type) -> Type t -> GHC.Type where
  Constant :: TypeIn uni (Ty t) => Inner uni (Ty t) -> Expr uni fun (Ty t)

  Abs :: TypeIn uni a => Int -> (Expr uni fun b) -> Expr uni fun (a :~> b)

  App :: TypeIn uni b => Expr uni fun (a :~> b) -> Expr uni fun a -> Expr uni fun b

  Builtin :: TypeIn uni (a :~> b) => fun (a :~> b) -> Expr uni fun (a :~> b)

  Var :: TyRep uni t -> Int -> Expr uni fun t

typeEq :: (GEq uni, GEq fun) => Expr uni fun a -> Expr uni fun b -> Maybe (Expr uni fun a :~: Expr uni fun b)
typeEq e1 e2 = case geq (typeOf e1) (typeOf e2) of
  Just Refl -> Just Refl
  Nothing -> Nothing

class ConstantIn uni k where
  val :: forall fun. Inner uni k -> Expr uni fun k

instance (TypeIn uni (Ty t), KnownIn uni (Ty t)) => ConstantIn uni (Ty t) where
  val = Constant

typeOf :: forall uni fun t. Expr uni fun t -> TyRep uni t
typeOf = \case
  Constant _ -> rep @_ @uni @t
  Abs _  body -> go body
  App _ _ -> rep @_ @uni @t
  Builtin _ -> rep @_ @uni @t
  Var trep _ -> trep
 where
   go :: forall a b. TypeIn uni a => Expr uni fun b -> TyRep uni (a :~> b)
   go e = rep @_ @uni @a :~~> typeOf e

subst :: forall uni fun x t
       . (GEq uni, GEq fun)
      => Int
      -> Expr uni fun x
      -> Expr uni fun t
      -> Maybe (Expr uni fun t)
subst i new = \case
  Constant _  -> Nothing
  Builtin _ -> Nothing
  App f a -> App <$> subst i new f <*> subst i new a
  Abs n b -> Abs n <$> subst n new b
  v@(Var _ n) | n == i -> case typeEq v new of
    Just Refl -> Just new
    Nothing -> Nothing
  _ -> Nothing

normalize :: forall uni fun a
           . (GEq uni, GEq fun)
          => Expr uni fun a
          -> Maybe (Expr uni fun a)
normalize = \case
  Constant v -> pure $ Constant v
  Builtin f -> pure $ Builtin f
  Var r n -> pure $ Var r n
  App f a -> do
    f' <- normalize f
    a' <- normalize a
    case f' of
      Abs n body -> subst n a' body
      other -> pure $ App other a'
  Abs n body -> Abs n <$> normalize body

lam1 :: forall uni fun a b. (TypeIn uni a) => (Expr uni fun a -> Expr uni fun b) -> Expr uni fun (a :~> b)
lam1 f = Abs n body
  where
    body = f $ Var (rep @_ @uni @a) n
    n = maxBV body + 1

bot :: Int
bot = 0

maxBV :: Expr uni fun t -> Int
maxBV = \case
  Var _ _ -> bot
  Builtin _ -> bot
  Constant _ -> bot
  App f a -> maxBV f `max` maxBV a
  Abs n _ -> n

{- NOTE: GEq instances checks structural equality (it's more like a real Eq instance),
         typeEq just gives you a proof of type equality (or not)
-}
instance (GEq uni, GEq fun, Each Eq uni) => GEq (Expr uni fun) where
  geq c1@(Constant x) c2@(Constant y) = case geq (typeOf c1) (typeOf c2) of
    Nothing -> Nothing
    Just Refl -> case typeOf c1 of
      TyRep uni -> if each @Eq @uni uni $ x == y
                   then  Just Refl
                   else Nothing
  geq e1@(Abs n body) e2@(Abs n' body') | n == n' = case (geq body body', geq (typeOf e1) (typeOf e2)) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
  geq e1@(App f a) e2@(App f' a') = case (geq f f', geq a a', geq (typeOf e1) (typeOf e2)) of
    (Just Refl, Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  geq (Builtin b1) (Builtin b2) = case geq b1 b2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (Var r n) (Var r' n') | n == n' = case geq r r' of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq _ _ = Nothing

instance ((forall k. Show (fun k)), Each Show uni) => Show (Expr uni fun ty)

(#) :: TypeIn uni b => Expr uni fun (a :~> b) -> Expr uni fun a -> Expr uni fun b
f # x = App f x

class Lam uni fun (a :: GHC.Type) b  | a -> b, uni fun b -> a where
  lam :: forall t. (TypeIn uni t, TypeIn uni b) => (Expr uni fun t -> a) -> Expr uni fun (t :~> b)

instance {-# OVERLAPPABLE #-} a' ~ Expr uni fun a => Lam uni fun a' a  where
  lam = lam1

instance ( a' ~ Expr uni fun a
         , TypeIn uni a
         , TypeIn uni b
         , Lam uni fun b' b
         ) => Lam uni fun (a' -> b') (a :~> b)  where
  lam f = lam $ \x -> lam (f x)
