{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Types where

import           Bound.Class
import           Bound.Name
import           Bound.Scope
import           Bound.Term
import           Bound.Var

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Writer.Strict

import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import qualified Data.Text.IO                as Text
import           Data.Vector                 (Vector)
import qualified Data.Vector                 as Vector

import qualified Hedgehog                    as H
import qualified Hedgehog.Gen                as HG
import qualified Hedgehog.Range              as HR

import           Control.Lens
import           Control.Monad
import qualified Data.Deriving
import           Data.Foldable
import           Data.Function
import           Data.Functor
import           Data.Functor.Classes
import           Data.Maybe
import           Data.Semigroup              (Semigroup)
import           Data.Traversable
import           Data.Void
import           Prelude                     hiding (log)

data Comp
  = FstComp
  | SndComp
  deriving (Show, Eq)

type Scope1 = Scope ()

data NameHint
  = NoHint
  | Hint !Text
  deriving (Ord, Show, Eq)

data TT a
  = Var a
  | Set Int
  | SomeSet
  | Unit
  -- Type-formers
  | Sigma !NameHint
          (TT a)
          (Scope1 TT a)
  | Pi !NameHint
       (TT a)
       (Scope1 TT a)
  | Lam !NameHint
        (Scope1 TT a)
  | App (TT a)
        (TT a)
  | Proj Comp
         (TT a)
  -- Datacons
  | MkUnit
  | MkSigma (TT a)
            (TT a)
  deriving (Functor, Foldable, Traversable)

instance Applicative TT where
  pure = return
  (<*>) = ap

instance Monad TT where
  return = Var
  x >>= f = bindTT f x

bindTT :: (a -> TT b) -> TT a -> TT b
bindTT f =
  \case
    Unit -> Unit
    MkUnit -> MkUnit
    SomeSet -> SomeSet
    Set n -> Set n
    Var a -> f a
    MkSigma x y -> MkSigma (bindTT f x) (bindTT f y)
    Proj s u -> Proj s (bindTT f u)
    App x y -> App (bindTT f x) (bindTT f y)
    Lam n x -> Lam n (x >>>= f)
    Sigma n x y -> Sigma n (bindTT f x) (y >>>= f)
    Pi n x y -> Pi n (bindTT f x) (y >>>= f)

$(Data.Deriving.deriveEq1 ''TT)

$(Data.Deriving.deriveShow1 ''TT)

instance Eq a => Eq (TT a) where
  (==) = eq1

instance Show a => Show (TT a) where
  showsPrec = showsPrec1

data DepQuant
  = DepSigma
  | DepPi
  deriving (Eq, Show)

pattern Dep q h t s <- (preview depTT -> Just (q, h, t, s))
  where Dep q h t s = review depTT (q, h, t, s)

pattern Fst t = Proj FstComp t

pattern Snd t = Proj SndComp t

depTT :: Prism' (TT a) (DepQuant, NameHint, TT a, Scope1 TT a)
depTT = prism' fromDep toDep
  where
    toDep (Sigma h t s) = Just (DepSigma, h, t, s)
    toDep (Pi h t s)    = Just (DepPi, h, t, s)
    toDep _             = Nothing
    fromDep (DepSigma, h, t, s) = Sigma h t s
    fromDep (DepPi, h, t, s)    = Pi h t s

lam_ :: Text -> TT Text -> TT Text
lam_ var body = Lam (Hint var) (abstract1 var body)

pi_ var t body = Pi (Hint var) t (abstract1 var body)

sigma_ var t body = Sigma (Hint var) t (abstract1 var body)

newtype TeleVar =
  TeleVar Int
  deriving (Eq, Ord, Show)

unTeleVar :: TeleVar -> Int
unTeleVar (TeleVar i) = i

newtype Tele v =
  Tele (Vector (TeleArg v))
  deriving (Eq, Show, Foldable, Functor, Traversable, Semigroup, Monoid)

data TeleArg v =
  TeleArg !NameHint
          !(TT v)
          !(Scope TeleVar TT v)
  deriving (Eq, Show, Foldable, Functor, Traversable)

unTele :: Tele v -> Vector (TeleArg v)
unTele (Tele xs) = xs

indexTele :: Tele v -> Int -> TcM (TeleArg v)
indexTele t i =
  case unTele t Vector.!? i of
    Just v  -> pure v
    Nothing -> throwError ["Unbound"]

newtype TcM a = TcM
  { unTcM :: ExceptT [Text] (WriterT [Text] (Reader Int)) a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadError [Text]
             , MonadWriter [Text]
             , MonadReader Int
             )

runTcM :: TcM a -> (Either [Text] a, [Text])
runTcM = flip runReader 0 . runWriterT . runExceptT . unTcM

prettyTc a = do
  let (res, out) = runTcM a
  traverse_ Text.putStrLn out
  print res

log :: Text -> TcM ()
log x = do
  lv <- ask
  let msg = Text.replicate lv " " <> x
  -- traceM (Text.unpack msg)
  tell [msg]

logS :: Show a => a -> TcM ()
logS = log . tshow

tshow :: Show a => a -> Text
tshow = Text.pack . show

snocTele (Tele te) v = Tele (Vector.snoc te v)

data InferResult a = InferResult
  { infer_inferredType  :: !(TT a)
  , infer_wellTypedTerm :: !(TT a)
  } deriving (Show)

newtype CheckResult a = CheckResult
  { check_wellTypedTerm :: TT a
  } deriving (Show)

infer :: Tele TeleVar -> TT TeleVar -> TcM (InferResult TeleVar)
infer tele tt =
  local (+ 1) $ do
    log ("tele: " <> tshow tele)
    log ("in: " <> tshow tt)
    res@(InferResult ty red) <- infer' tele tt
    log ("red: " <> tshow red)
    log ("type: " <> tshow ty)
    log ""
    pure res

infer' :: Tele TeleVar -> TT TeleVar -> TcM (InferResult TeleVar)
infer' _ MkUnit = do
  log "rule MkUnit"
  pure (InferResult Unit MkUnit)
infer' _ Unit = do
  log "rule Unit"
  pure (InferResult (Set 0) Unit)
infer' _ (Set i) = do
  log "rule Set"
  pure (InferResult (Set (i + 1)) (Set i))
infer' g var@(Var (TeleVar v)) = do
  log "rule Var"
  TeleArg _ a x <- indexTele g v
  let i = instantiate1 var x
  pure (InferResult a i)
infer' g (App e1 e2) = do
  InferResult a s <- infer g e1
  Pi x b c <- whnf a
  CheckResult t <- check g e2 b
  let c' = instantiate1 t c
  pure (InferResult c' (App s t))
infer' g (Fst e) = do
  InferResult a t <- infer g e
  Sigma _ b _ <- whnf a
  pure (InferResult b (Fst t))
infer' g (Snd e) = do
  InferResult a t <- infer g e
  Sigma _ _ c <- whnf a
  let c' = instantiate1 (Fst t) c
  pure (InferResult c' (Snd t))
infer' g@(Tele v) (Dep q x typ body) = do
  log ("rule " <> tshow q)
  (InferResult c1 a) <- infer g typ
  Set i <- whnf c1
  -- Create a new televar, to go on the end of the telescope.
  let tv = TeleVar (Vector.length v)
  let g' = snocTele g (TeleArg x c1 (pure tv))
  (InferResult c2 b) <- infer g' (instantiate1 (Var tv) body)
  Set j <- whnf c2
  pure (InferResult (Set (max i j)) (Dep q x a (abstract1 tv b)))
infer' _ _ = error "infer: impossible"

check :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM (CheckResult TeleVar)
check tele tt ty =
  local (+ 1) $ do
    log ("tele: " <> tshow tele)
    log ("in: " <> tshow tt)
    res@(CheckResult red) <- check' tele tt ty
    log ("red: " <> tshow red)
    log ""
    pure res

check' :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM (CheckResult TeleVar)
check' g@(Tele v) (Lam h e) a = do
  Pi x b c <- whnf a
  let tv = TeleVar (Vector.length v)
      g' = snocTele g (TeleArg x b (pure tv))
  CheckResult t <- check g' (instantiate1 (Var tv) e) (instantiate1 (Var tv) c)
  pure (CheckResult (Lam h (abstract1 tv t)))
check' g (MkSigma e1 e2) a = do
  Sigma x b c <- whnf a
  CheckResult s <- check g e1 b
  CheckResult t <- check g e2 (instantiate1 s c)
  pure (CheckResult (MkSigma s t))
check' g e a = do
  InferResult b t <- infer g e
  subtype g a b
  pure (CheckResult t)

subtype :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM ()
subtype g a b = do
  a' <- whnf a
  b' <- whnf b
  subtypeWHNF g a' b'

subtypeWHNF :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM ()
subtypeWHNF g a b = subtypeWHNF' g a b

subtypeWHNF' :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM ()
subtypeWHNF' _ (Set i) (Set j)
  | j == i + 1 = pure ()
subtypeWHNF' g (Dep q x a1 b1) (Dep q' _ a2 b2)
  | q /= q' = throwError []
  | q == q' = do
    converts g a1 a2 SomeSet
    let tv = TeleVar (length g)
        g' = snocTele g (TeleArg x a1 (pure tv))
    subtype g' (instantiate1 (Var tv) b1) (instantiate1 (Var tv) b2)
subtypeWHNF' g a b = do
  convertsWHNF g a b SomeSet
  pure ()

converts :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TT TeleVar -> TcM ()
converts g s t a = do
  s' <- whnf s
  t' <- whnf t
  a' <- whnf a
  convertsWHNF g s' t' a'

convertsWHNF :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TT TeleVar -> TcM ()
convertsWHNF g (Set i) (Set j) SomeSet
  | i == j = pure ()
convertsWHNF g (Dep q x a1 b1) (Dep q' _ a2 b2) SomeSet
  | q /= q' = throwError []
  | q == q' = do
    converts g a1 a2 SomeSet
    let tv = TeleVar (length g)
        g' = snocTele g (TeleArg x a1 (pure tv))
    converts g' (instantiate1 (Var tv) b1) (instantiate1 (Var tv) b2) SomeSet
convertsWHNF g s t (Pi x a b) = do
  let tv = TeleVar (length g)
      g' = snocTele g (TeleArg x a (pure tv))
  converts g' (App s (Var tv)) (App t (Var tv)) (instantiate1 (Var tv) b)
convertsWHNF g s t (Sigma x a b) = do
  converts g (Fst s) (Fst t) a
  converts g (Snd s) (Snd t) (instantiate1 (Fst s) b)
convertsWHNF _ _ _ Unit = pure ()
convertsWHNF g s t _ = do
  _ <- neutralEqual g s t
  pure ()

neutralEqual :: Tele TeleVar -> TT TeleVar -> TT TeleVar -> TcM (TT TeleVar)
neutralEqual g var@(Var (TeleVar v)) var' = do
  unless (var == var') (throwError ["boum"])
  TeleArg _ a _ <- indexTele g v
  pure a
neutralEqual g (App s1 t1) (App s2 t2) = do
  a <- neutralEqual g s1 s2
  Pi x b c <- whnf a
  converts g t1 t2 b
  pure (instantiate1 t1 c)
neutralEqual g (Fst s) (Fst t) = do
  a <- neutralEqual g s t
  Sigma _ b _ <- whnf a
  pure b
neutralEqual g (Snd s) (Snd t) = do
  a <- neutralEqual g s t
  Sigma _ _ c <- whnf a
  pure (instantiate1 (Fst s) c)

whnf :: TT a -> TcM (TT a)
whnf = pure . whnf'
  where
    whnf' :: forall b. TT b -> TT b
    whnf' e =
      case e of
        Var {} -> e
        Pi h t s -> Pi h (whnf' t) (onScope whnf' s)
        App f x ->
          case whnf' f of
            Lam _ b -> whnf' (instantiate1 x b) -- what about Pi?
            f'      -> App f' x
        _ -> e

onScope f = toScope . f . fromScope

-- (A : Set) -> A
typ :: TT TeleVar
typ =
  fromMaybe (error "boom") $
  closed $ Pi (Hint "A") (Set 0) (abstract1 "A" (Var "A"))

-- (A : Set) -> (a : A) -> A
idType :: TT TeleVar
idType = closed' $ pi_ "A" (Set 0) $ pi_ "a" (Var "A") (Var "A")

-- (A : Set) -> (a : A) -> a
idType' :: TT TeleVar
idType' = closed' $ pi_ "A" (Set 0) $ pi_ "a" (Var "A") (Var "a")

(-:) = pi_

infixr 8 -:

(-*) = sigma_

infixr 9 -*

(~>) = ($)

infixr 7 ~>

applyType :: TT TeleVar
applyType =
  closed' $
  "A" -: Set 0 ~>
  "B" -: Set 0 ~>
  "a" -: Var "A" ~> "f" -: ("_" -: Var "A" ~> Var "B") ~> Var "B"
applyExpr :: TT TeleVar
applyExpr = 
  closed' $ 
    lam_ "A" $ lam_ "B" $ lam_ "a" $ lam_ "f" $ App (Var "f") (Var "a")

closed' = fromMaybe (error "boom") . closed
