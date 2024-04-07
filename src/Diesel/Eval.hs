{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Diesel.Eval where

import qualified Data.Kind as GHC

import Data.GADT.Compare ( GEq )

import Diesel.Type ( Type((:~>)) )
import Diesel.Uni ( TypeIn(Inner), Inner(Fun), Closed )
import Diesel.Expr ( Expr(Builtin, Constant, App), normalize )
import Data.Maybe (fromMaybe)

{-
   Class for finitely enumerable GADTs indexed by Diesel.Type functions.

   Users define instances of this for the `fun` GADT in their
   `Expr uni fun ty` expressions in order to declare builtins.
-}
type Eval :: forall (t :: GHC.Type). (Type t -> GHC.Type) -> (Type t -> GHC.Type) ->  GHC.Constraint
class GEq fun =>  Eval uni fun  where
  evalBuiltin :: forall a b. fun (a :~> b) -> Inner uni (a :~> b) -- Inner uni a -> Inner uni b

eval :: forall uni fun ty
      . (Closed uni, Eval uni fun)
     => Expr uni fun ty
     -> Either (Expr uni fun ty) (Inner uni ty)
eval e = go $ fromMaybe  e  (normalize e)
  where
    go :: forall uni' fun' ty'
        . (Closed uni', Eval uni' fun')
       => Expr uni' fun' ty'
       -> Either (Expr uni' fun' ty') (Inner uni' ty')
    go ex = case ex of
      Constant x -> pure x
      App f x -> case go f of
        Left _ -> Left ex
        Right (Fun f') -> case go x of
          Left _ -> Left ex
          Right x' -> pure $ f' x'
      Builtin fun -> pure $ evalBuiltin @_ @uni' @fun' fun
      _ -> Left ex
