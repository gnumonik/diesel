{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}


{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Diesel.Expr (
    module EXPORT
  , Lam(..)
  ) where

import qualified Data.Kind as GHC


import Diesel.Type ( Type((:~>)) )
import Diesel.Uni ( TypeIn(rep) )
import Diesel.Expr.Internal
    ( (#),
      bot,
      inL_,
      inR_,
      lam1,
      list,
      maxBV,
      mkPair_,
      normalize,
      subst,
      substADT,
      typeEq,
      typeOf,
      typeOfADT,
      ADT(..),
      ConstantIn(..),
      Expr(..),
      showParens )
import qualified Diesel.Expr.Internal as EXPORT

{-
   Variable argument lambda abstraction. Used like:

   ```
     lam $ \x y z -> (...)
   ```

   Borrowed/adapted from Plutarch (who I think borrowed it from Atkey?).
-}
class Lam uni fun (a :: GHC.Type) b  | a -> b, uni fun b -> a where
  lam :: forall t. (TypeIn uni t, TypeIn uni b) => (Expr uni fun t -> a) -> Expr uni fun (t :~> b)

instance {-# OVERLAPPABLE #-} a' ~ Expr uni fun a => Lam uni fun a' a  where
  lam = lam1 rep

instance ( a' ~ Expr uni fun a
         , TypeIn uni a
         , TypeIn uni b
         , Lam uni fun b' b
         ) => Lam uni fun (a' -> b') (a :~> b)  where
  lam f = lam $ \x -> lam (f x)
