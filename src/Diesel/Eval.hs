{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE LambdaCase, QuantifiedConstraints #-}

module Diesel.Eval where

import qualified Data.Kind as GHC

import Data.GADT.Compare ( GEq )

import Diesel.Type
    ( Type((:~>)) )
import Diesel.Uni
    ( Inner((:/\), L, R, ListVal, Fun),
      TypeIn(..) )
import Diesel.Expr
    ( normalize,
      ADT(MkList, MkPair, InL, InR),
      Expr(..) )
import Data.Maybe ( fromMaybe )
import Diesel.Universal ( Universal(..) )
import Data.Coerce (coerce)


evalUniversal :: forall uni t. Universal uni t -> Inner uni t
evalUniversal = \case
  FstPair _ -> coerce $ \case (a :/\ _) -> a
  SndPair _ -> coerce $ \case (_ :/\ b) -> b
  InjPair _ -> coerce  $ \ a b -> a :/\ b
  InjL _     -> coerce $ \x -> L x
  InjR _     -> coerce $ \x -> R x
  Switch _   -> Fun $ \(Fun fL) -> Fun $ \(Fun fR) -> Fun $ \case
                           L x -> fL x
                           R x -> fR x
  ConsList _ -> coerce $ \x xs -> ListVal (x:xs)
  NilList _ -> ListVal []
  UnconsList _ -> coerce $ \case
    (y:ys) -> R (y :/\ coerce ys)
    emptee -> L (coerce emptee)
  FoldrList _ -> Fun $ \(Fun f) -> Fun $ \e -> Fun $ \(ListVal ta) ->  foldr (coerce f) e ta

asFunction :: Inner uni (a :~> b) -> Inner uni a -> Inner uni b
asFunction (Fun f) = f

{-
   Class for finitely enumerable GADTs indexed by Diesel.Type functions.

   Users define instances of this for the `fun` GADT in their
   `Expr uni fun ty` expressions in order to declare builtins.
-}
type Eval :: forall t. (GHC.Type -> GHC.Type) -> (Type t -> GHC.Type) ->  GHC.Constraint
class GEq fun =>  Eval uni fun  where
  evalBuiltin :: forall a. fun a -> Inner uni a  -- Inner uni a -> Inner uni b

eval :: forall uni fun ty
      . (GEq uni,  Eval uni fun, forall w. Show (Expr uni fun w))
     => Expr uni fun ty
     -> Either (Expr uni fun ty) (Inner uni ty)
eval e = go $ fromMaybe  e  (normalize e)
  where
    go :: forall uni' fun' ty'
        . (GEq uni', Eval uni' fun',forall z. Show (Expr uni' fun' z))
       => Expr uni' fun' ty'
       -> Either (Expr uni' fun' ty') (Inner uni' ty')
    go ex = case ex of
      Constant x -> pure x
      -- (App (Abs ty i b) x) -> case subst
      App f x -> case go f of
        Left bad -> error (show bad) -- Left ex
        Right (Fun f') -> case go x of
          Left bad -> error (show bad) --  Left ex
          Right x' -> pure $ f' x'
      Builtin  _ fun -> pure $ evalBuiltin @_ @uni' @fun' fun
      CompilerBuiltin u -> pure $ evalUniversal u
      Data adt -> case adt of
        MkPair a b -> case go a of
          Left bad -> error (show bad) --  Left ex
          Right a' -> case go b of
            Left bad -> error (show bad) -- Left ex
            Right b' -> pure $ a' :/\ b'
        InL _ l -> case go l of
          Left bad -> error (show bad) -- Left ex
          Right l' -> Right $ L l'
        InR _ r -> case go r of
          Left bad -> error (show bad) -- Left ex
          Right r' -> pure $ R r'
        MkList _ xs -> case traverse go xs of
          Left bad -> error (show bad) -- Left ex
          Right xs' -> pure $ ListVal xs'
      bad -> error (show bad) -- Left ex

