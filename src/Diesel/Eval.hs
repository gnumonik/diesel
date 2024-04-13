{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE LambdaCase, QuantifiedConstraints, OverloadedStrings #-}

module Diesel.Eval where

import qualified Data.Kind as GHC
import Data.Type.Equality ( type (:~:)(Refl) )

import Data.GADT.Compare ( GEq(geq))
import Data.Constraint.Extras ( Has(argDict) )

import Diesel.Type
    ( Type((:~>), Ty, TyCon, (:@)), K, TyRep((:@@)) )
import Diesel.Uni
    ( Inner(Val, Con1, (:/\), L, R, ListVal, Fun),
      KnownIn(..),
      TypeIn(..) )
import Diesel.Expr
    ( (#),
      lam1,
      normalize,
      ADT(MkList, MkPair, InL, InR),
      ConstantIn(val),
      Expr(..),
      Lam(lam) )
import Data.Maybe ( fromMaybe )
import Diesel.Universal ( Universal(..) )
import Data.Coerce (coerce)
import Data.Constraint (Dict(Dict))

import Prettyprinter

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
type Eval :: forall t. (Type t -> GHC.Type) -> (Type t -> GHC.Type) ->  GHC.Constraint
class GEq fun =>  Eval uni fun  where
  evalBuiltin :: forall a b. fun (a :~> b) -> Inner uni (a :~> b) -- Inner uni a -> Inner uni b

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
      Builtin _ _ fun -> pure $ evalBuiltin @_ @uni' @fun' fun
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

data U :: forall t. Type t -> GHC.Type where
  UInt :: U (Ty Int)
  UBool :: U (Ty Bool)
  UMaybe :: U (TyCon (K Maybe))

instance (c (Ty Int), c (Ty Bool), c (TyCon (K Maybe))) => Has c U where
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
type BoolT = Ty Bool
type MaybeT = TyCon (K Maybe)

instance GEq U where
  geq UInt UInt = Just Refl
  geq UBool UBool = Just Refl
  geq UMaybe UMaybe = Just Refl
  geq _ _ = Nothing

instance KnownIn U (Ty Int) where
  knownIn = UInt

instance KnownIn U (Ty Bool) where
  knownIn = UBool

instance  KnownIn U MaybeT where
  knownIn = UMaybe

data F :: forall t. Type t -> GHC.Type where
  Add :: F (Ty Int :~> Ty Int :~> Ty Int)
  Subtract :: F (Ty Int :~> Ty Int :~> Ty Int)
  EJust :: TyRep U t -> F (t :~> MaybeT :@ t)
  --ENothing ::  TyRep U t -> F (MaybeT :@ t)

instance Pretty (F t) where
  pretty = \case
    Add -> "add"
    Subtract -> "subtract"
    EJust rp -> "Just" <+> "@" <> parens (pretty rp)

instance Show (F t) where
  show = \case
    Add -> "Add"
    Subtract -> "Subtract"
    EJust r -> "EJust " <> show r
    --ENothing r -> "ENothing " <> show r

instance GEq F where
 geq Add Add = Just Refl
 geq Subtract Subtract = Just Refl
 geq (EJust r1) (EJust r2) = case geq r1 r2 of
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
    EJust _ -> Fun $ \x -> Con1 $ Just x
    --ENothing r -> Con1 Nothing


plus :: Expr U F (IntT :~> IntT :~> IntT)
plus = Builtin rep rep Add

minus :: Expr U F (IntT :~> IntT :~> IntT)
minus = Builtin rep rep Subtract

uJust :: forall t. TypeIn U t => TyRep U t ->  Expr U F (t :~> MaybeT :@ t)
uJust r  = lam1 r  $ \x -> Builtin r (UMaybe :@@ r) (EJust r) # x

testExpr :: Expr U F (IntT :~> (IntT :~> IntT))
testExpr = lam $ \x y -> minus # (plus # x # y) #  (minus # y # x)

result :: Either (Expr U F IntT) (Inner U IntT)
result = eval $ testExpr # val 1 # val 1

-- Need a TypeIn instance for maybe or this won't work. Need a new ctor of Type that can be matched in
-- instances. The value could be a function or a proxy or whatever, doesn't matter
bop :: String
bop =  show testExpr

beep :: Doc ann
beep = pretty testExpr
