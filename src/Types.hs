{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UndecidableInstances       #-}

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
bindTT f = \case
  Unit        -> Unit
  MkUnit      -> MkUnit
  Set n       -> Set n
  Var a       -> f a
  MkSigma x y -> MkSigma (bindTT f x) (bindTT f y)
  Proj    s u -> Proj s (bindTT f u)
  App     x y -> App (bindTT f x) (bindTT f y)
  Lam     n x -> Lam n (x >>>= f)
  Sigma n x y -> Sigma n (bindTT f x) (y >>>= f)
  Pi    n x y -> Pi n (bindTT f x) (y >>>= f)

lam :: Text -> TT Text -> TT Text
lam var body = Lam (Hint var) (abstract1 var body)

pi :: Text -> TT Text -> TT Text -> TT Text
pi var ty body = Pi (Hint var) ty (abstract1 var body)

$(Data.Deriving.deriveEq1 ''TT)

$(Data.Deriving.deriveShow1 ''TT)

instance Eq a => Eq (TT a) where
  (==) = eq1

instance Show a => Show (TT a) where
  showsPrec = showsPrec1

newtype TeleVar = TeleVar Int
  deriving (Eq, Enum, Ord, Show)

unTeleVar :: TeleVar -> Int
unTeleVar (TeleVar i) = i

newtype Tele v = Tele (Vector (TeleArg v))
  deriving (Eq, Show, Foldable, Functor, Traversable)

data TeleArg v = TeleArg !NameHint !(TT v) !(Scope TeleVar TT v)
  deriving (Eq, Show, Foldable, Functor, Traversable)

unTele :: Tele v -> Vector (TeleArg v)
unTele (Tele xs) = xs

indexTele :: Tele v -> Int -> TcM (TeleArg v)
indexTele t i = case unTele t Vector.!? i of
  Just v  -> pure v
  Nothing -> throwError ["Unbound"]

tele :: Tele TeleVar
tele = Tele $ Vector.fromList []

newtype TcM a = TcM { unTcM :: ExceptT [Text] (WriterT [Text] (Reader Int)) a }
  deriving (Functor, Applicative, Monad, MonadError [Text], MonadWriter [Text], MonadReader Int)

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

logS :: Pretty a => a -> TcM ()
logS = log . ppr

tshow :: Show a => a -> Text
tshow = Text.pack . show

snocTele (Tele te) v = Tele (Vector.snoc te v)

class Pretty a where ppr :: a -> Text

instance Pretty Text where ppr = id

instance Pretty TeleVar where ppr = tshow

instance Pretty Void where ppr v = error "impossible"

-- instance Pretty a => Pretty (TeleArg a) where ppr (TeleArg h  vs) = _ vs
-- instance Pretty a => Pretty (Tele a) where ppr (Tele vs) = _ vs

instance (Show a, Pretty a) => Pretty (TT a) where
  ppr (Var t) = ppr t
  ppr (Pi (Hint h) t s) = "(" <> h <> " : " <> ppr t <> ") -> " <> "(" <> ppr (instantiate1 (Var h) (ppr <$> s)) <> ")"
  ppr x = tshow x


infer :: Tele TeleVar -> TT TeleVar -> TcM (TT TeleVar, TT TeleVar)
infer tele tt = local (+ 1) $ do
  log ("tele: " <> tshow tele)
  log ("in: " <> ppr tt)
  res@(ty, red) <- infer' tele tt
  log ("red: " <> ppr red)
  log ("type: " <> ppr ty)
  log ""
  pure res

infer' :: Tele TeleVar -> TT TeleVar -> TcM (TT TeleVar, TT TeleVar)
infer' _ MkUnit = do
  log "rule MkUnit"
  pure (Unit, MkUnit)
infer' _ Unit = do
  log "rule Unit"
  pure (Set 0, Unit)
infer' _ (Set i) = do
  log "rule Set"
  pure (Set (i + 1), Set i)
infer' g var@(Var (TeleVar v)) = do
  log "rule Var"
  TeleArg _ a x <- indexTele g v
  let i = instantiate1 var x
  pure (a, i)
infer' g@(Tele v) (Sigma x typ body) = do
  log "rule Sigma"
  (c1, a) <- infer g typ
  Set i   <- whnf c1
  let tv = TeleVar (Vector.length v)
  (c2, b) <- infer
    (snocTele g (TeleArg x c1 (abstract (const (Just tv)) (Var tv))))
    (instantiate1 (Var tv) body)
  Set j <- whnf c2
  pure (Set (max i j), Sigma x a (abstract1 tv b))
infer' g@(Tele v) (Pi x typ body) = do
  log "rule Pi"
  (c1, a) <- infer g typ
  Set i   <- whnf c1
  let tv = TeleVar (Vector.length v)
  (c2, b) <- infer
    (snocTele g (TeleArg x c1 (abstract (const (Just tv)) (Var tv))))
    (instantiate1 (Var tv) body)
  Set j <- whnf c2
  pure (Set (max i j), Pi x a (abstract1 tv b))

whnf :: TT a -> TcM (TT a)
whnf = pure . whnf'
 where
  whnf' :: forall b . TT b -> TT b
  whnf' e = case e of
    Var{}    -> e
    Pi h t s -> Pi h (whnf' t) (onScope whnf' s)
    App f x  -> case whnf' f of
      Lam _ b -> whnf' (instantiate1 x b) -- what about Pi?
      f'      -> App f' x
    _ -> e

onScope f = toScope . f . fromScope

-- (A : Set) -> A
typ :: TT TeleVar
typ = fromMaybe (error "boom") $ closed $ Pi (Hint "A")
                                             (Set 0)
                                             (abstract1 "A" (Var "A"))

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
  closed'
    $  "A"
    -: Set 0
    ~> "B"
    -: Set 0
    ~> "a"
    -: Var "A"
    ~> "f"
    -: ("_" -: Var "A" ~> Var "B")
    ~> Var "B"

closed' = fromMaybe (error "boom") . closed

pi_ a t body = Pi (Hint a) t (abstract1 a body)
sigma_ a t body = Sigma (Hint a) t (abstract1 a body)

