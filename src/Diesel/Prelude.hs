{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE LambdaCase, TemplateHaskell, QuantifiedConstraints #-}

module Diesel.Prelude where

import qualified Data.Kind as GHC
import Data.Type.Equality

import Data.GADT.Compare ( GEq(geq))
import Data.Constraint.Extras

import Diesel.Type
import Diesel.Uni
import Diesel.Expr
import Data.Maybe
import Diesel.TH.Derive
import Diesel.Universal
import Data.Coerce (coerce)
