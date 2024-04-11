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

module Diesel.Expr.Internal  where

import qualified Data.Kind as GHC

import Data.GADT.Compare (GEq (..), defaultEq)
import Data.Type.Equality (type (:~:)(Refl))


import Diesel.Type
import Diesel.Uni
import Data.List (foldl')
import Diesel.Universal

{-
  An expression.

  The first kind-index (`uni`) represents a GADT parameterized by the ground types
  of a type universe.

  The second kind index (`fun`) represents a GADT parameterized by the primitive
  or built-in functions available in the DSL.

  The final parameter is the Diesel.Type expression type.

  The constructors are not exported. While it would not be possible
  for a user to manipulate the AST in a type-unsafe way, we use
  plain `Int`s to disambiguate bound variables. That's OK so long as
  all functions are constructed with lam1 or lam, but isn't generally
  safe for users to manipulate.
-}
data Expr :: forall (t :: GHC.Type). (Type t -> GHC.Type) -> (Type t -> GHC.Type) -> Type t -> GHC.Type where
  Constant :: TypeIn uni (Ty t) => Inner uni (Ty t) -> Expr uni fun (Ty t)

  Abs :: TypeIn uni a => Int -> (Expr uni fun b) -> Expr uni fun (a :~> b)

  App :: TypeIn uni b => Expr uni fun (a :~> b) -> Expr uni fun a -> Expr uni fun b

  Builtin :: TypeIn uni (a :~> b) => fun (a :~> b) -> Expr uni fun (a :~> b)

  Data :: ADT uni fun t -> Expr uni fun t

  Var :: TyRep uni t -> Int -> Expr uni fun t

  CompilerBuiltin :: Universal uni t -> Expr uni fun t

data ADT :: forall (t :: GHC.Type). (Type t -> GHC.Type) -> (Type t -> GHC.Type) -> Type t -> GHC.Type where
  MkPair :: Expr uni fun a -> Expr uni fun b -> ADT uni fun (a :& b)
  InL :: TyRep uni b -> Expr uni fun a -> ADT uni fun (a :| b)
  InR :: TyRep uni a -> Expr uni fun b -> ADT uni fun (a :| b)
  MkList :: TyRep uni a -> [Expr uni fun a] -> ADT uni fun (List a)

typeOfADT ::  ADT uni fun t -> TyRep uni t
typeOfADT = \case
  MkPair a b -> typeOf a :&& typeOf b
  InL b a -> typeOf a :|| b
  InR a b -> a :|| typeOf b
  MkList r _ -> ListRep r

instance (GEq uni, GEq fun, Each Eq uni) => GEq (ADT uni fun) where
  geq (MkPair a b) (MkPair c d) = case (geq a c, geq b d) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  geq (InL repA a) (InL repB b) = case (geq repA repB, geq a b) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  geq (InR repA a) (InR repB b) = case (geq repA repB, geq a b) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  geq (MkList repA a) (MkList repB  b) = case geq repA repB  of
    Just Refl | and (zipWith defaultEq a b) -> Just Refl
    _ -> Nothing
  geq _ _ = Nothing

{-
    Type equality. *Only* checks the types, and completely ignores
    the structure of the Expr.
-}
typeEq :: (GEq uni, GEq fun) => Expr uni fun a -> Expr uni fun b -> Maybe (Expr uni fun a :~: Expr uni fun b)
typeEq e1 e2 = case geq (typeOf e1) (typeOf e2) of
  Just Refl -> Just Refl
  Nothing -> Nothing

typeOf :: forall uni fun t. Expr uni fun t -> TyRep uni t
typeOf = \case
  Constant _ -> rep @_ @uni @t
  Abs _  body -> go body
  App _ _ -> rep @_ @uni @t
  Builtin _ -> rep @_ @uni @t
  Var trep _ -> trep
  Data adt -> typeOfADT adt
  CompilerBuiltin ufun -> typeOfUniversal ufun
 where
   go :: forall a b. TypeIn uni a => Expr uni fun b -> TyRep uni (a :~> b)
   go e = rep @_ @uni @a :~~> typeOf e

{-
    NOTE: The GEq instance checks structural equality (it's more like a real Eq instance),
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

(#) :: TypeIn uni b => Expr uni fun (a :~> b) -> Expr uni fun a -> Expr uni fun b
f # x = App f x

{-  "Using Circular Programs for Higher-Order Syntax" - Emil Axelsson & Koen Claesson
    https://emilaxelsson.github.io/documents/axelsson2013using.pdf

    Really neat trick for safe construction of terms.
-}
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
  CompilerBuiltin _ -> bot
  Constant _ -> bot
  App f a -> maxBV f `max` maxBV a
  Abs n _ -> n
  Data adt -> case adt of
       MkPair a b -> maxBV a `max` maxBV b
       InL _ a -> maxBV a
       InR _ b -> maxBV b
       MkList _ xs -> foldl' (\acc x -> max (maxBV x) acc) 0 xs

{-
   Perform type-safe substitution.
-}
subst :: forall uni fun x t
       . (GEq uni, GEq fun)
      => Int
      -> Expr uni fun x
      -> Expr uni fun t
      -> Maybe (Expr uni fun t)
subst i new = \case
  Constant v  -> pure $ Constant v
  Builtin b -> pure $ Builtin b
  CompilerBuiltin u -> pure $ CompilerBuiltin u
  App f a -> App <$> subst i new f <*> subst i new a
  Abs n b -> Abs n <$> subst n new b
  v@(Var _ n) | n == i -> do
    Refl <- typeEq v new
    pure new
  Var r n -> pure $ Var r n
  Data adt -> Data <$> substADT i new adt

substADT :: forall uni fun x t
          . (GEq uni, GEq fun)
         => Int
         -> Expr uni fun x
         -> ADT uni fun t
         -> Maybe (ADT uni fun t)
substADT i new = \case
    MkPair a b ->  MkPair <$> subst i new a <*> subst i new b
    InL r e -> InL r <$> subst i new e
    InR r e -> InR r <$> subst i new e
    MkList r l -> MkList r <$> traverse (subst i new) l

normalize :: forall uni fun a
           . (GEq uni, GEq fun)
          => Expr uni fun a
          -> Maybe (Expr uni fun a)
normalize = \case
  Constant v -> pure $ Constant v
  Builtin f -> pure $ Builtin f
  CompilerBuiltin f -> pure $ CompilerBuiltin f
  Var r n -> pure $ Var r n
  App f a -> do
    f' <- normalize f
    a' <- normalize a
    case f' of
      Abs n body -> subst n a' body
      other -> pure $ App other a'
  Abs n body -> Abs n <$> normalize body
  Data adt -> Data <$> case adt of
    MkPair a b -> MkPair <$> normalize a <*> normalize b
    InL r a -> InL r <$> normalize a
    InR r a -> InR r <$> normalize a
    MkList r l -> MkList r <$> traverse normalize l

class TypeIn uni k => ConstantIn uni k where
  val :: forall fun. Inner uni k -> Expr uni fun k

instance (TypeIn uni (Ty t), KnownIn uni (Ty t)) => ConstantIn uni (Ty t) where
  val = Constant

instance (ConstantIn uni a, ConstantIn uni b) => ConstantIn uni (a :& b) where
  val (a :/\ b) = Data $ MkPair (val a) (val b)


mkPair_ :: Expr uni fun a -> Expr uni fun b -> Expr uni fun (a :& b)
mkPair_ e1 e2 = Data $ MkPair e1 e2

instance (TypeIn uni a, TypeIn uni b, ConstantIn uni a, ConstantIn uni b) => ConstantIn uni (a :| b) where
  val = \case
    L a -> Data $ InL rep (val a)
    R b -> Data $ InR rep (val b)

inL_ :: forall uni fun r l. TypeIn uni r => Expr uni fun l -> Expr uni fun (l :| r)
inL_ e1 = Data $ InL rep e1

inR_ :: forall uni fun l r. TypeIn uni l => Expr uni fun r -> Expr uni fun (l :| r)
inR_ e1 = Data $ InR rep e1

instance ConstantIn uni a => ConstantIn uni (List a) where
  val (ListVal xs) = Data $ MkList rep (val <$> xs)

list :: TypeIn uni a => [Expr uni fun a] -> Expr uni fun (List a)
list xs = Data $ MkList rep xs
