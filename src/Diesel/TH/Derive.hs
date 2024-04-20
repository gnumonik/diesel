{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module Diesel.TH.Derive where


import Control.Monad
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Syntax
import Data.List (foldl')
import Data.Bifunctor (Bifunctor(..))
import qualified Data.Text.Lazy as TL
import Text.Pretty.Simple (pShow)

{-
data TestUni :: forall (t :: GHC.Type). DT.Type t -> GHC.Type where
  TestUniInt :: TestUni (DT.Ty Int)
  TestUniBool :: TestUni (DT.Ty Bool)
  TestUniList :: TestUni (DT.Ty t) -> TestUni (DT.Ty [t])


testUniInfo :: Q Exp
testUniInfo = do
  dt <- reifyDatatype ''TestUni
  let pretty = TL.unpack (pShow dt)
  pure $ LitE (StringL pretty)
-}

testInfo :: Name -> Q [Dec] -- Exp
testInfo nm = do
  dt <- reifyDatatype nm
  let pretty = TL.unpack (pShow dt)
      body =  LitE (StringL pretty)
  pure [FunD (mkName "mahTestInfo") [Clause [] (NormalB body) []]]
-- This is Semigroup but I definitely don't wanna define weird orphan semigroup instances
-- for TH constructs
class Apply t where
  (##) :: t -> t -> t

instance Apply Exp where
  (##) = AppE

instance Apply Type where
  (##) = AppT
infixl 8 ##

data Kinded a = KK a | KT a deriving (Show, Eq, Functor)

unKinded :: Kinded a -> a
unKinded = \case
  KK a -> a
  KT a -> a

getInnerTy :: Type -> Q (Kinded Type)
getInnerTy = \case
  AppT (AppT EqualityT _) rest -> getInnerTy rest
  AppT (ConT ct) rest | isDieselT ct -> pure (KT rest)
  AppT (ConT ct) rest | isDieselK ct -> pure (KK rest)
  other -> fail $ "Unsupported Uni type parameter: " <> show other
 where
   isDieselMod x = nameModule x == Just "Diesel.Type"
   isDieselK x = nameBase x == "K" && isDieselMod x
   isDieselT x = nameBase x == "T" && isDieselMod x

mkUniverse :: Name -> Q [Dec]
mkUniverse nm = do
  hasDecls <- customDeriveArgDict nm
  knownInDecls <- deriveKnownIn nm
  geqDecls <- deriveGEq nm
  pure $ concat [hasDecls, knownInDecls, geqDecls]


-- we replace un-capturable names w/ capturable ones
collectTyVars :: Kinded Type -> Q ([Name],Kinded Type)
collectTyVars = \case
  KT t -> second KT . snd <$> go ['a'..] t
  KK t -> second KK . snd <$> go ['a'..] t
 where
    go :: String -> Type -> Q (String,([Name],Type))
    go [] _ = error "Ran out of names (this should not happen)"
    go xs@(c:cs) ty = case ty of
      AppT t1 t2 -> do
        (xs',(ns',t1')) <- go xs t1
        (xs'',(ns'',t2')) <- go xs' t2
        let nms = ns' <> ns''
            tx  = AppT t1' t2'
        pure (xs'',(nms,tx))
      VarT _ -> do
        let newNm = mkName [c]
        pure (cs,([newNm],VarT newNm))
      other -> pure (xs,([],other))

{- We need a custom deriver for Has/argDict bc the one from
   constraints-extras won't generate quantified constraints for parameterized
   types.
-}
customDeriveArgDict :: Name -> Q [Dec]
customDeriveArgDict nm = do
  dt@DatatypeInfo{..} <- reifyDatatype nm
  checkIndexKind dt
  -- make the context from the ctors
  instanceCxt <- traverse mkCxtElem datatypeCons

  let instanceType = ConT (mkName "Has") ## VarT constraint ## ConT nm

  methodBodyMatches <- traverse mkMethodBodyMatch datatypeCons

  let methodCase = CaseE xVE methodBodyMatches
      methodDec = FunD (mkName "has") [Clause [xVP,fVP] (NormalB methodCase) []]

  pure  [InstanceD Nothing instanceCxt instanceType [methodDec]]
 where
   constraint = mkName "c"

   f = mkName "f"
   x = mkName "x"
   fVE = VarE f
   fVP = VarP f
   xVE = VarE x
   xVP = VarP x

   mkMethodBodyMatch :: ConstructorInfo -> Q Match
   mkMethodBodyMatch ConstructorInfo{..} = do
     (bound,pat) <- mkPat constructorFields
     body <- mkBody bound
     pure $ Match pat (NormalB body) []
    where
      mkPat = \case
        [] -> pure ([],ConP constructorName [] [])
        xs -> do
          vs <- replicateM (length xs) (newName "x")
          let p = ConP constructorName [] (VarP <$> vs)
          pure  (vs,p)
      mkBody [] = pure fVE
      mkBody (z:zs) = do
        let hasC = AppTypeE (VarE (mkName "has")) (VarT constraint)
            dol  = VarE (mkName "$")
            lhs  = hasC ## VarE z
        UInfixE lhs dol  <$> mkBody zs

   mkCxtElem :: ConstructorInfo -> Q Pred
   mkCxtElem ConstructorInfo{..} = do
     let appC z = VarT constraint ##  z
     innerTy <- getInnerTy $ head constructorContext
     collectTyVars innerTy >>= \case
       ([],t) -> pure $ appC $ mkTy t
       (ns,t) -> do
         let tvBndrs = (`PlainTV` SpecifiedSpec) <$> ns
             cxt     = appC . VarT <$> ns
             rhs     = appC $ mkTy t
         pure $ ForallT tvBndrs cxt rhs


deriveKnownIn :: Name -> Q [Dec]
deriveKnownIn nm = do
  dt@DatatypeInfo{..} <- reifyDatatype nm
  checkIndexKind dt
  traverse mkKnownInInstance datatypeCons
 where
   mkKnownInInstance :: ConstructorInfo -> Q Dec
   mkKnownInInstance ConstructorInfo{..} = do
     let knownInUni x = ConT (mkName "KnownIn") ## ConT nm ## x
     innerTy <- getInnerTy $ head constructorContext
     collectTyVars innerTy >>= \case
       ([],t) -> do
         let knownInClass = knownInUni (mkTy t)
             methodDec = FunD (mkName "knownIn")
                           [Clause [] (NormalB (ConE constructorName)) []]
         pure $ InstanceD Nothing [] knownInClass [methodDec]
       (ns,t) -> do
         let numFields = length constructorFields
             ctx = knownInUni . VarT <$> ns
             tyInstType = knownInUni (mkTy t)
             body = NormalB
                    $ foldl' (##) (ConE  constructorName) $ replicate numFields (VarE $ mkName "knownIn")
             methodDec = FunD (mkName "knownIn")
                         [Clause [] body []]
         pure $ InstanceD Nothing ctx tyInstType [methodDec]


deriveGEq :: Name -> Q [Dec]
deriveGEq nm = do
  DatatypeInfo{..} <- reifyDatatype nm
  clauses <- traverse mkMethodClause datatypeCons
  let catchallClause = Clause [WildP,WildP] (NormalB nothingE) []
      method = FunD (mkName "geq") $ clauses <> [catchallClause]
      geqClass = ConT (mkName "GEq") ## ConT nm
  pure [InstanceD Nothing [] geqClass  [method]]
 where
   justReflE = ConE (mkName "Just") ## ConE (mkName "Refl")
   nothingE  = ConE (mkName "Nothing")

   justReflP = ConP (mkName "Just") [] [ConP (mkName "Refl") [] []]
   nothingP = ConP (mkName "Nothing") [] []

   geqE = VarE (mkName "geq")

   mkCase :: [(Name,Name)] -> Exp
   mkCase [(l,r)] = CaseE (geqE ## VarE l ## VarE r)
                    [ Match nothingP (NormalB nothingE) []
                    , Match justReflP (NormalB justReflE) []
                    ]
   mkCase ((l,r):xs) = CaseE (geqE ## VarE l ## VarE r)
                    [ Match nothingP (NormalB nothingE) []
                    , Match justReflP (NormalB $ mkCase xs) []
                    ]
   mkCase [] = error "Empty list passed to mkCase, should have been caught earlier"

   mkMethodClause :: ConstructorInfo -> Q Clause
   mkMethodClause ConstructorInfo{..}
     | null constructorFields  = do
       let pat = replicate 2 $ ConP constructorName [] []
           body = NormalB $ ConE (mkName "Just") ## ConE (mkName "Refl")
       pure $ Clause pat body []
     | otherwise = do
         let mkArgPairs :: forall x. Char -> x -> (Name,Name)
             mkArgPairs c _ = bimap (mkName . pure)  (mkName . (<> "'") . pure) (c,c)

             argNames = zipWith mkArgPairs ['a'..] constructorFields
             argsL = fst <$> argNames
             argsR = snd <$> argNames

             mkPat names = ConP constructorName [] $ VarP <$> names
             pat = ParensP <$> [mkPat argsL, mkPat argsR]

             body = NormalB $ mkCase argNames
         pure $ Clause pat body []

mkTy :: Kinded Type -> Type
mkTy = \case
           KT z -> ConT (mkName "Diesel.Type.T") ## z
           KK z -> ConT (mkName "Diesel.Type.K") ## z


checkIndexKind :: DatatypeInfo -> Q ()
checkIndexKind  DatatypeInfo{..} = case datatypeVars of
  [ KindedTV _ _ StarT] -> pure ()
  _ -> fail $ "Wrong kind index in universe type '"
                <> nameBase datatypeName
                <> "'. The return kind of a universe GADT must be "
                <> "'GHC.Type -> GHC.Type'"
                <> " your type has return kind index:\n"
                <> show datatypeVars
