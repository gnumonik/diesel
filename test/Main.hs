{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}

{-# LANGUAGE LambdaCase, QuantifiedConstraints, OverloadedStrings #-}

module Main (main) where

import qualified Data.Kind as GHC
import Data.Type.Equality ( type (:~:)(Refl) )

import Data.Either (isRight)

import Data.GADT.Compare ( GEq(geq))
import Data.Constraint.Extras ( Has(argDict) )

import Diesel
import Data.Coerce (coerce)
import Data.Constraint (Dict(Dict))

import Prettyprinter

main :: IO ()
main = do
  if isRight result
    then do
      print beep
    else error "failed"

data U :: GHC.Type  -> GHC.Type where
  UInt :: U (T Int)
  UBool :: U (T Bool)
  UMaybe :: U (K Maybe)

instance (c (T Int), c (T Bool), c (K Maybe)) => Has c U where
  argDict = \case
    UInt -> Dict
    UBool -> Dict
    UMaybe -> Dict

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

instance GEq U where
  geq UInt UInt = Just Refl
  geq UBool UBool = Just Refl
  geq UMaybe UMaybe = Just Refl
  geq _ _ = Nothing

instance KnownIn U (T Int) where
  knownIn = UInt

instance KnownIn U (T Bool) where
  knownIn = UBool

instance  KnownIn U (K Maybe) where
  knownIn = UMaybe

data F :: forall t. Type t -> GHC.Type where
  Add :: F (Ty Int :~> Ty Int :~> Ty Int)
  Subtract :: F (Ty Int :~> Ty Int :~> Ty Int)
  IfThenElse :: TyRep U res -> F (Ty Bool :~> res :~> res :~> res)
  EJust :: TyRep U t -> F (t :~> MaybeT :@ t)
  ENothing :: TyRep U t -> F (MaybeT :@ t)

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

instance GEq F where
 geq Add Add = Just Refl
 geq Subtract Subtract = Just Refl
 geq (IfThenElse r1) (IfThenElse r2) = case geq r1 r2 of
   Just Refl -> Just Refl
   Nothing -> Nothing
 geq (EJust r1) (EJust r2) = case geq r1 r2 of
   Just Refl -> Just Refl
   Nothing -> Nothing
 geq (ENothing r1) (ENothing r2) = case geq r1 r2 of
   Just Refl -> Just Refl
   Nothing -> Nothing
 geq _ _ = Nothing
 --geq (ENothing r1) (ENothing r2)  = case geq r1 r2 of
 --  Just Refl -> Just Refl
 --  Nothing -> Nothing

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
    --ENothing r -> Con1 Nothing


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

-- Need a TypeIn instance for maybe or this won't work. Need a new ctor of Type that can be matched in
-- instances. The value could be a function or a proxy or whatever, doesn't matter
--bop :: String
--bop =  show testExpr

beep :: Doc ann
beep = pretty testExpr
