{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

module STLC where

import Unbound.Generics.LocallyNameless
import GHC.Generics
import Data.Typeable
import Test.QuickCheck
import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

-- definition of types and syntax

data SNat = SZer | SSuc SNat
    deriving (Eq, Ord, Generic, Typeable)

toSNat :: Int -> SNat
toSNat n 
    | n <= 0    = SZer
    | otherwise = SSuc (toSNat (n-1))

fromSNat :: SNat -> Int
fromSNat  SZer    = 0
fromSNat (SSuc x) = 1 + fromSNat x

prede :: SNat -> SNat
prede  SZer    = SZer
prede (SSuc x) = x

instance Show SNat where
    show = show . fromSNat

data Ty = TNat SNat | Ty :-> Ty
          deriving (Eq, Show, Generic, Typeable)

subtypes :: Int -> Ty -> [Ty]
subtypes k (TNat n)    = [ TNat (toSNat m) | m <- [1..(fromSNat n)] ]
subtypes k (t1 :-> t2) = [ t3 :-> t4 | t3 <- supertypes k t1, t4 <- subtypes k t2 ]

supertypes :: Int -> Ty -> [Ty]
supertypes k (TNat n)    = [ TNat (toSNat m) | m <- [(fromSNat n)..(fromSNat n)+k] ]
supertypes k (t1 :-> t2) = [ t3 :-> t4 | t3 <- subtypes k t1, t4 <- supertypes k t2 ]

isSubType :: Int -> Ty -> Ty -> Bool
isSubType k t1 t2 = t1 `elem` (subtypes k t2)

isSuperType :: Int -> Ty -> Ty -> Bool
isSuperType k t1 t2 = t1 `elem` (supertypes k t2)

data Term = Var (Name Term)
          | Lam (Bind (Name Term, Ty) Term)
          | App Term Term
          | Const Int
          | Match Term Term (Bind (Name Term) Term)
--          | LetRec (Bind (Rec (Name Term, Embed Term)) Term)
          deriving (Show, Generic, Typeable)

-- infrastructure for substitutions

instance Alpha SNat
instance Alpha Ty
instance Alpha Term

instance Subst Term SNat
instance Subst Term Ty

instance Subst Term Term where
   isvar (Var x) = Just (SubstName x)
   isvar _       = Nothing


lam :: Name Term -> Ty -> Term -> Term
lam n t e = Lam (bind (n,t) e)

-- definition of the type checker
type Tc a = ExceptT String (ReaderT Ctx (FreshMT Identity)) a

runTc :: Tc a -> Either String a
runTc m
  = runIdentity $ runFreshMT $ flip runReaderT [] $ runExceptT m

withExtendedCtx :: Name Term -> Ty -> Tc a -> Tc a
withExtendedCtx n t m
  = local ((n, t) : ) m

lookupVar :: Name Term -> Tc Ty
lookupVar v
  = do
      ctx <- ask
      case lookup v ctx of
        Just t -> return t
        Nothing -> throwError "Variable not defined."

infer :: Int -> Term -> Tc Ty
infer k (Const i)
  = return $ TNat (toSNat i)
infer k (Var v)
  = lookupVar v
infer k (Lam b)
  = do
      ((n,t), e) <- unbind b
      t' <- withExtendedCtx n t (infer k e)
      return (t :-> t')
infer k (App e e')
  = do
      t  <- infer k e
      t' <- infer k e'
      case t of
        (t1 :-> t2) | isSubType k t' t1 -> return t2
        _ -> throwError "Type error in application."
infer k (Match e1 e2 b)
  = do
      t1 <- infer k e1
      t2 <- infer k e2
      (n, e3) <- unbind b
      case t1 of
        (TNat x) -> do 
                      t3 <- withExtendedCtx n (TNat x) (infer k e3)
                      if isSubType k t2 t3
                      then return t3 
                      else if isSubType k t3 t2 
                           then return t2
                           else throwError "Type error in application"
        _ -> throwError "Type error in application"  


typeCorrect :: Int -> Term -> Ty -> Bool
typeCorrect k e t
  = case runTc (infer k e) of
      Left  _  -> False
      Right t' -> isSubType k t t'


-- definition of the generator

type VarCounter = Int
type Depth = Int
type Ctx = [(Name Term, Ty)]

type LGen a = (ReaderT Ctx (StateT VarCounter Gen)) a

runLGen :: LGen a -> Gen a
runLGen m
  = fst <$> runStateT (runReaderT m []) 0

oneofM :: [LGen a] -> LGen a
oneofM [] = error "Cannot use on empty list"
oneofM gs
  = do
       v <- lift $ lift $ choose (0, length gs - 1)
       gs !! v

-- -- generate a variable

genNewVar :: LGen (Name Term)
genNewVar
  = do
      v <- lift $ get
      lift $ modify (1 +)
      return (string2Name $ "x_" ++ show v)

-- May's note: subtyping applied here
fromCtx :: Int -> Ty -> LGen [Term]
fromCtx k ty
  = do
      ctx <- ask
      let f p = if isSubType k (snd p) ty then [Var $ fst p] else []
      return (concatMap f ctx)


withNewVar :: Ty -> LGen a -> LGen (Name Term, a)
withNewVar t m
  = do
       v <- genNewVar
       (v,) <$> local ((v, t) :) m

genType :: Depth -> Int -> LGen Ty
genType d k
  | d <= 1    = pure $ TNat (toSNat k)
  | otherwise
     = do
         let d2 = d `div` 2
         t <- oneofM [ pure $ TNat (toSNat k)
                     , (:->) <$> genType d2 k <*>
                                 genType d2 k
                     ]
         return t


instance Arbitrary Ty where
  arbitrary
    = do
         t <- choose (2,10)
         k <- choose (2, 6)
         runLGen (genType t k)


genConst :: Int -> LGen Term
genConst k = lift $ lift $ Const <$> choose (1,k)

genNatTerm :: Depth -> Int -> LGen Term
genNatTerm d k
  | d <= 1
    = do
        vs <- fromCtx k $ TNat (toSNat k)
        c  <- genConst k
        lift $ lift $ elements (c : vs)
  | otherwise
    = genAppTerm d2 d2 k (TNat (toSNat k)) (TNat (toSNat k))
    where
      d2  = d `div` 2

-- May's note: not sure if it follows specification
genAppTerm :: Depth -> Depth -> Int -> Ty -> Ty -> LGen Term
genAppTerm d1 d2 k dom ran
  = App <$> genTerm d1 k (dom :-> ran) <*> genTerm d2 k dom

-- May's note: not sure i it follows specification
genLamTerm :: Depth -> Int -> Ty -> Ty -> LGen Term
genLamTerm d k dom ran
  | d <= 2 = let f (v, e) = lam v dom e
             in f <$> withNewVar dom (genTerm d k ran)
  | otherwise = let f (v, e) = lam v dom e
                    d2 = d `div` 2
                in f <$> withNewVar dom (genTerm d2 k ran)

-- May's note: not sure if it follows specification
genMatchTerm :: Depth -> Int -> Ty -> LGen Term
genMatchTerm d1 k ran
  = do
    let d2 = d1 `div` 2
    e1 <- genTerm d2 k (TNat (toSNat k))
    e2 <- genTerm d2 k ran 
    (n, t)  <- withNewVar (TNat (toSNat (k-1))) (genTerm d2 k ran) 
    return (Match e1 e2 (bind n t))

genTerm :: Depth -> Int -> Ty -> LGen Term
genTerm d k (TNat x)
  | d <= 2    = genNatTerm d k
  | otherwise = oneofM [genNatTerm d k, genMatchTerm d k (TNat x)] 
genTerm d k (t :-> t')
  | d <= 2    = genLamTerm d k t t'
  | otherwise = genLamTerm d2 k t t'
    where
      d2 = d `div` 2

gen :: Depth -> Int -> LGen Term
gen d k
  = do
      t <- genType d k
      genTerm 2 k t

instance Arbitrary Term where
  arbitrary
    = do
         d <- choose (2,4)
         k <- choose (2,6)
         runLGen $ gen d k


-- testing if the generator builds only type correct terms

generatorSound :: Property
generatorSound
  = forAll (arbitrary :: Gen Ty)
           (\ t -> forAll (runLGen $ genTerm 4 6 t)
                   (\ e -> typeCorrect 6 e t == True))

testGenerator :: IO ()
testGenerator
  = quickCheckWith stdArgs {maxSuccess = 1000} generatorSound
