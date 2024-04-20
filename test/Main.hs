{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}

{-# LANGUAGE LambdaCase, QuantifiedConstraints, OverloadedStrings, TemplateHaskell #-}

module Main (main) where

import qualified Data.Kind as GHC
import Data.Type.Equality ( type (:~:)(Refl) )
import Diesel.TH.Derive

import Data.Either (isRight)

import Data.GADT.Compare ( GEq(geq))
import Data.Constraint.Extras ( Has(..) )

import Diesel
    ( eval,
      (#),
      (#$),
      lam1,
      Eval(..),
      Lam(lam),
      ConstantIn(val),
      Expr(Builtin),
      K,
      T,
      TyRep((:~~>), (:@@)),
      Type((:~>), TyCon, Ty, (:@)),
      Inner(Val, Con1, Fun),
      KnownIn(..),
      TypeIn(rep, Inner) )
import Diesel.Type ( K, T )
import Data.Coerce (coerce)

import Prettyprinter ( (<+>), parens, Doc, Pretty(pretty) )

data U :: GHC.Type  -> GHC.Type where
  UInt :: U (T Int)
  UBool :: U (T Bool)
  UMaybe :: U (K Maybe)

deriveKnownIn ''U
customDeriveArgDict ''U
deriveGEq ''U

instance Show (U t) where
  show = \case
    UInt -> "UInt"
    UBool -> "UBool"
    UMaybe -> "UMaybe"

instance Pretty (U t) where
  pretty = \case
    UInt -> "Int"
    UBool -> "Bool"
    UMaybe -> "Maybe"

type IntT = Ty Int
-- type BoolT = Ty Bool
type MaybeT = TyCon (K Maybe)

data F :: forall t. Type t -> GHC.Type where
  Add :: F (Ty Int :~> Ty Int :~> Ty Int)
  Subtract :: F (Ty Int :~> Ty Int :~> Ty Int)
  IfThenElse :: TyRep U res -> F (Ty Bool :~> res :~> res :~> res)
  EJust :: TyRep U t -> F (t :~> MaybeT :@ t)
  ENothing :: TyRep U t -> F (MaybeT :@ t)
deriveGEq ''F

instance Pretty (F t) where
  pretty = \case
    Add -> "add"
    Subtract -> "subtract"
    IfThenElse _ -> "if"
    EJust rp -> "Just" <+> "@" <> parens (pretty rp)
    ENothing rp -> "Nothing" <+> "@" <> parens (pretty rp)

instance Show (F t) where
  show = \case
    Add -> "Add"
    Subtract -> "Subtract"
    IfThenElse r -> "IfThenElse " <> show r
    EJust r -> "EJust " <> show r
    ENothing r -> "ENothing " <> show r


instance Eval U F where
  evalBuiltin = \case
    Add -> let doAdd :: Int -> Int -> Int
               doAdd = (+)
           in coerce doAdd
    Subtract -> let doMinus :: Int -> Int -> Int
                    doMinus = (-)
                in coerce doMinus
    IfThenElse _ ->  Fun $ \cond -> Fun $ \troo -> Fun $ \fawlse -> if coerce cond then troo else fawlse
    EJust _ -> Fun $ \x -> Con1 $ Just x
    ENothing _ -> Con1 Nothing

plus :: Expr U F (IntT :~> IntT :~> IntT)
plus = Builtin rep  Add

minus :: Expr U F (IntT :~> IntT :~> IntT)
minus = Builtin rep  Subtract

--ifte :: forall t. TyRep U t -> Expr U F (BoolT :~> t :~> t :~> t)
--ifte trep = Builtin (RepT UBool :~~> trep :~~> trep :~~> trep)  (IfThenElse trep)

just :: forall t. TyRep U t ->  Expr U F (t :~> MaybeT :@ t)
just r  = lam1 r  $ \x -> Builtin  (r :~~> (UMaybe :@@ r)) (EJust r) # x

testExpr :: Expr U F (IntT :~> IntT :~>  MaybeT :@ IntT)
testExpr = lam $ \x y -> just rep #$ minus # (plus # x # y) #  (minus # y # x)

result :: Either (Expr U F (MaybeT :@ IntT)) (Inner U (MaybeT :@ IntT))
result = eval $ testExpr # val 1 # val 1

beep :: Doc ann
beep = pretty testExpr

main :: IO ()
main =  do
  if isRight result
    then do
      print beep
    else error "failed"
