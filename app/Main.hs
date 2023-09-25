{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
module Main where

import Control.Applicative (Alternative (empty))
import Control.Monad (MonadPlus, guard, void)
import Data.Functor (($>), (<&>))
import Data.Text (Text)

main :: IO ()
main = putStrLn "Hello, Haskell!"

data Relevance = Relevant | Irrelevant
  deriving (Eq, Ord, Show)

data Termination = Logical | Program
  deriving (Eq, Ord, Show)

data Mode = Mode {rho :: Relevance, theta :: Termination}
  deriving (Eq, Ord, Show)

pattern RL :: Mode
pattern RL = Mode Relevant Logical

data Var ty = Var
  { name :: Text
  , mode :: Mode
  , ty :: ty
  }
  deriving (Eq, Ord, Show)

data Context
  = C_
  | (:&) Context (Var Point)
  deriving (Eq, Ord, Show)

(?) :: (Alternative m) => Context -> Text -> m (Var Point)
context0 ? name = case context0 of
  C_ -> empty
  _ :& v@(Var x _ _) | x == name -> pure v
  c :& _ -> c ? name

infixl 7 -:

(-:) :: (Eq x, MonadPlus m) => m x -> x -> m ()
action -: x = guard . (x ==) =<< action

infixl 9 :>

data Point
  = Star
  | Point Text
  | Pi (Var Point) Point
  | Abs (Var Point) Point
  | App Mode Point Point
  | Equal Termination Point Point
  | Reify Termination Coercion
  | (:>) Point Coercion
  | NN
  | Zero
  | Succ Point
  | Ind Point Point Point (Text, Point)
  deriving (Eq, Ord, Show)

pattern IndN :: Text -> Point -> Point -> Point -> Text -> Point -> Point
pattern IndN x aA a1 a2 y a3 = Ind (Pi (Var x RL NN) aA) a1 a2 (y, a3)

repoint :: Point -> Point -> Text -> Point
repoint point with name = case point of
  Point p | p == name -> with
  Pi (Var x m aA) a ->
    if x == name
      then repoint
        do Pi (Var (x <> name) m aA) (repoint a (Point (x <> name)) x)
        do with
        do name
      else Pi (Var x m aA) (repoint a with name)
  Abs (Var x m aA) a ->
    if x == name
      then repoint
        do Abs (Var (x <> name) m aA) (repoint a (Point (x <> name)) x)
        do with
        do name
      else Abs (Var x m aA) (repoint a with name)
  App mode p0 p1 -> App mode (repoint p0 with name) (repoint p1 with name)
  Equal t p0 p1 -> Equal t (repoint p0 with name) (repoint p1 with name)
  Reify t g -> Reify t (recoerce g with name)
  p :> g -> repoint p with name :> recoerce g with name
  Succ p -> Succ (repoint p with name)
  Ind p p1 p2 (y, p3) -> Ind
    do repoint p with name
    do repoint p1 with name
    do repoint p2 with name
    do
      if y == name
        then
          ( y <> name
          , repoint
              do repoint p3 (Point (y <> name)) y
              do with
              do name
          )
        else (y, repoint p3 with name)
  p -> p

data Coercion
  = Reflect Point
  | Reflex Point
  | Sym Coercion
  | (:::) Coercion Coercion
  | PiCong (Var Coercion) Coercion
  | AbsCong (Var Point) Coercion
  | AppCong Coercion Coercion Coercion
  | AppCongIrrel Coercion Point Point Coercion
  | Reduction Point Point
  | ReifyCong Termination Coercion Coercion
  | Pifst Termination Coercion
  | Pisnd Termination Coercion Coercion Coercion
  | ConvCong Coercion Coercion Coercion
  | EqualCong Termination Coercion Coercion
  | SuccCong Coercion
  | IndCong Point Coercion Coercion (Text, Coercion) Coercion
  deriving (Eq, Ord, Show)

pattern IndNCong ::
  Text ->
  Point ->
  Coercion ->
  Coercion ->
  Text ->
  Coercion ->
  Coercion ->
  Coercion
pattern IndNCong x aA g1 g2 y g3 g =
  IndCong (Pi (Var x RL NN) aA) g1 g2 (y, g3) g

recoerce :: Coercion -> Point -> Text -> Coercion
recoerce coercion with name = case coercion of
  Reflect point -> Reflect (repoint point with name)
  Reflex point -> Reflex (repoint point with name)
  Sym g -> Sym (recoerce g with name)
  g1 ::: g2 -> recoerce g1 with name ::: recoerce g2 with name
  PiCong (Var x m g1) g2 ->
    if x == name
      then recoerce
        do PiCong (Var (x <> name) m g1) (recoerce g1 (Point (x <> name)) x)
        do with
        do name
      else PiCong (Var x m (recoerce g1 with name)) (recoerce g2 with name)
  AbsCong (Var x m aA) g
    | x == name -> recoerce
        do AbsCong (Var (x <> name) m aA) (recoerce g (Point (x <> name)) x)
        do with
        do name
    | otherwise -> AbsCong (Var x m aA) (recoerce g with name)
  AppCong g1 g2 g -> AppCong
    do recoerce g1 with name
    do recoerce g2 with name
    do recoerce g with name
  AppCongIrrel g1 a b g2 -> AppCongIrrel
    do recoerce g1 with name
    do repoint a with name
    do repoint b with name
    do recoerce g2 with name
  Reduction a b -> Reduction (repoint a with name) (repoint b with name)
  ReifyCong t g1 g2 ->
    ReifyCong t (recoerce g1 with name) (recoerce g2 with name)
  Pifst t g -> Pifst t (recoerce g with name)
  Pisnd t g g1 g2 -> (Pisnd t)
    do recoerce g with name
    do recoerce g1 with name
    do recoerce g2 with name
  ConvCong g g1 g2 -> ConvCong
    do recoerce g with name
    do recoerce g1 with name
    do recoerce g2 with name
  EqualCong t g1 g2 ->
    EqualCong t (recoerce g1 with name) (recoerce g2 with name)
  SuccCong g -> SuccCong (recoerce g with name)
  IndCong b g1 g2 (y, g3) g4 -> IndCong
    do repoint b with name
    do recoerce g1 with name
    do recoerce g2 with name
    do (y, recoerce g3 with name)
    do recoerce g4 with name

(∉) :: Text -> Context -> Bool
(∉) x = \case
  C_ -> True
  c :& Var y _ _ -> x /= y && x ∉ c

(+:) :: (MonadPlus m) => Context -> Var Point -> m Context
c +: (Var x (Mode r t) a) = do
  -- T-ConsTm
  infer (resurrect c) t a -: Star
  guard (x ∉ c)
  --
  pure (c :& Var x (Mode r t) a)

resurrect :: Context -> Context
resurrect = \case
  C_ -> C_
  c :& Var x (Mode _ t) a -> resurrect c :& Var x (Mode Relevant t) a

infer :: (MonadPlus m) => Context -> Termination -> Point -> m Point
infer c t = \case
  Star -> case t of
    -- T-TYPE
    Logical -> empty
    Program -> pure Star
  Point x -> do
    -- T-Var
    (Var _ rt0 a) <- c ? x
    guard (rt0 <= Mode Relevant t)
    --
    pure a
  Pi (Var x (Mode _ t0) aA) b -> do
    -- T-Pi
    infer c t aA -: Star
    c' <- c +: Var x (Mode Relevant t0) aA
    infer c' t b -: Star
    --
    pure Star
  Abs xA b -> do
    -- T-Abs
    c' <- c +: xA
    bB <- infer c' t b
    infer (resurrect c) t (Pi xA bB) -: Star
    --
    pure (Pi xA bB)
  App mode b a -> do
    -- T-App
    tyB <- infer c t b
    case tyB of
      Pi (Var x m aA) bB -> do
        guard (m <= mode)
        infer c t a -: aA
        --
        pure (repoint bB a x)
      _ -> empty
  Equal t0 a b -> do
    -- T-Eq
    aA <- infer c t0 a
    infer c t0 b -: aA
    --
    pure Star
  Reify t0 g -> do
    -- T-Reify
    a :==: b <- prove c t0 g
    --
    pure (Equal t0 a b)
  a :> g -> do
    -- T-Conv
    aA :==: bB <- prove (resurrect c) t g
    infer c t a -: aA
    --
    pure bB
  NN -> pure Star -- T-Nat
  Zero -> pure NN -- T-Zero
  Succ a -> do
    -- T-Succ
    infer c t a -: NN
    --
    pure NN
  IndN x aA a1 a2 y a3 -> do
    -- T-Ind
    let x_ ^: n = Var x_ RL n
    infer (resurrect c) Logical (Pi (x ^: NN) aA) -: Star
    infer c Logical a1 -: NN
    infer c Logical a2 -: repoint aA Zero x
    c' <- c +: Var y RL NN
    let ayx = repoint aA (Point y) x
        asyx = repoint aA (Succ $ Point y) x
    infer c' Logical a3 -: Pi (x ^: ayx) asyx
    --
    pure (repoint aA a1 x)
  Ind{} -> empty

infixr 8 :==:

data Path = Point :==: Point
  deriving (Eq, Ord, Show)

prove :: (MonadPlus m) => Context -> Termination -> Coercion -> m Path
prove c t = \case
  Reflect a0@(Equal t0 a b) -> do
    -- E-Reflect
    guard (t0 <= t)
    void (infer c Logical a0)
    aA <- infer c t a
    infer c t b -: aA
    --
    pure (a :==: b)
  Reflect{} -> empty
  Reflex a -> infer c t a $> a :==: a -- E-Reflex
  Sym g -> prove c t g <&> \(a :==: b) -> b :==: a -- E-Sym
  g1 ::: g2 -> do
    -- E-Trans
    x :==: b1 <- prove c t g1
    b2 :==: y <- prove c t g2
    guard (b1 == b2)
    --
    pure (x :==: y)
  PiCong (Var x (Mode r0 t0) g1) g2 -> do
    -- E-PiCong
    a1 :==: a2 <- prove c t g1
    c' <- c +: (Var x (Mode Relevant t0) a1)
    b1 :==: b2 <- prove c' t g2
    infer c t (Pi (Var x (Mode r0 t0) a1) b1) -: Star
    infer c t (Pi (Var x (Mode r0 t0) a1) b2) -: Star
    let b3 = repoint b2 (Point x :> Sym g1) x
    --
    pure (Pi (Var x (Mode r0 t0) a1) b1 :==: Pi (Var x (Mode r0 t0) a2) b3)
  AbsCong l@(Var _ (Mode _ t0) aA) g -> do
    -- E-AbsCong
    infer (resurrect c) t0 aA -: Star
    c' <- c +: l
    a1 :==: a2 <- prove c' t g
    _b <- infer c t (Abs l a2)
    --
    pure (Abs l a1 :==: Abs l a2)
  AppCong g1 g2 g -> do
    -- E-AppCong
    a1 :==: a2 <- prove c t g1
    b1 :==: b2 <- prove c t g2
    a :==: b <- prove (resurrect c) t g
    infer c t (App (Mode Relevant t) a1 b1) -: a
    infer c t (App (Mode Relevant t) a2 b2) -: b
    --
    pure ((App (Mode Relevant t) a1 b1 :> g) :==: App (Mode Relevant t) a2 b2)
  AppCongIrrel g1 b1 b2 g -> do
    -- E-AppCongIrrel
    let rc = resurrect c
        a @ b = App (Mode Irrelevant t) a b
    a1 :==: a2 <- prove c t g1
    aA <- infer rc t b1
    infer rc t b2 -: aA
    bB1 :==: bB2 <- prove rc t g
    infer c t (a1 @ b1) -: bB1
    infer c t (a2 @ b2) -: bB2
    --
    pure (a1 @ b1 :> g :==: a2 @ b2)
  Reduction a b -> do
    -- E-Red
    primitiveReduction c t a -: b
    pure (a :==: b)
  ReifyCong t0 g1 g2 -> do
    -- E-ReifyCong
    p <- prove c t0 g1
    prove c t0 g2 -: p
    --
    pure (Reify t0 g1 :==: Reify t0 g2)
  Pifst t0 g -> do
    -- E-PiFst
    prove c t0 g >>= \case
      Pi (Var _ (Mode _ th) a1) _ :==: Pi (Var _ _ a2) _ -> do
        guard (th <= t)
        --
        pure (a1 :==: a2)
      _ -> empty
  Pisnd t0 g g1 g2 -> do
    -- E-PiSnd
    guard (t0 <= t)
    prove c t0 g >>= \case
      Pi (Var x1 (Mode _ t1) aA1) bB1 :==: Pi (Var x2 _ aA2) bB2 -> do
        a1 :==: a2 <- prove c t1 g1
        infer c t1 a2 -: aA2
        prove c t1 g2 -: aA2 :==: aA1
        --
        pure (repoint bB1 (a1 :> g2) x1 :==: repoint bB2 a2 x2)
      _ -> empty
  ConvCong g g1 g2 -> do
    -- E-ConvCong
    a1 :==: a2 <- prove c t g
    a1A <- infer c t (a1 :> g1)
    infer c t (a2 :> g2) -: a1A
    --
    pure (a1 :> g1 :==: a2 :> g2)
  EqualCong t0 g1 g2 -> do
    -- E-EqCong
    a1 :==: a2 <- prove c t0 g1
    b1 :==: b2 <- prove c t0 g2
    infer c t (Equal t0 a1 b1) -: Star
    --
    pure (Equal t0 a1 b1 :==: Equal t0 a2 b2)
  SuccCong g -> do
    a :==: b <- prove c t g
    infer c t a -: NN
    --
    pure (Succ a :==: Succ b)
  IndNCong x aA g1 g2 y g3 g -> do
    -- E-IndCong
    infer (resurrect c) Logical (Pi (Var x RL NN) aA) -: Star
    a1 :==: b1 <- prove c Logical g1
    a2 :==: b2 <- prove c Logical g2
    c' <- c +: Var y RL NN
    a3 :==: b3 <- prove c' Logical g3
    a0 <- infer c t (IndN x aA a1 a2 y a3)
    b0 <- infer c t (IndN x aA b1 b2 y b3)
    prove c t g -: a0 :==: b0
    --
    pure (IndN x aA a1 a2 y a3 :> g :==: IndN x aA b1 b2 y b3)
  IndCong{} -> empty

primitiveReduction ::
  (MonadPlus m) => Context -> Termination -> Point -> m Point
primitiveReduction c t p =
  infer c t p >> case p of
    App mode (Abs (Var x m _) a) b
      | mode == m ->
          -- aBeta-AppAbs
          pure (repoint a b x)
    Abs l@(Var x (Mode _ t0) _) a1 :> g -> do
      -- aBeta-AbsPush
      guard (t0 <= t) <* infer c t (Abs l a1 :> g)
      prove c t0 g >>= \case
        Pi _ _ :==: Pi (Var y d2 aA2) _ -> do
          let a2 = repoint a1 (Point x :> Sym (Pifst t0 g)) x
          let g2 = Pisnd t0 g (Reflex (Point x)) (Sym (Pifst t0 g))
          --
          pure (Abs (Var y d2 aA2) (a2 :> g2))
        _ -> empty
    a :> g1 :> g2 -> pure (a :> (g1 ::: g2)) -- aBeta-Combine
    a :> g -> do
      -- aBeta-ConvRefl
      aA1 :==: aA2 <- prove c t g
      guard (aA1 == aA2)
      --
      pure a
    IndN _ _ Zero a2 _ _ -> pure a2 -- aBeta-IndZero
    IndN x aA (Succ a1) a2 y a3 ->
      -- aBeta-IndSucc
      pure (App RL (repoint a3 a1 y) (IndN x aA a1 a2 y a3))
    _ -> empty

value :: (MonadPlus m) => Point -> m ()
value = \case
  Star -> pure ()
  Point _ -> pure ()
  Pi _ _ -> pure ()
  Abs _ _ -> pure ()
  Equal{} -> pure ()
  Reify _ _ -> pure ()
  NN -> pure ()
  Zero -> pure ()
  Succ _ -> pure ()
  _ -> empty

covalue :: (MonadPlus m) => Point -> m ()
covalue = \case
  c :> _ -> covalue c
  Succ c -> covalue c
  p -> value p

-- | Computational
--
-- > _ :: Γ |- a ~> b
reduceC1 :: (MonadPlus m) => Context -> Termination -> Point -> m Point
reduceC1 c t = \case
  App d0 a b
    | Just () <- covalue a -> do
        -- R-AppAbs
        reduceA1 c t a >>= \case
          Abs (Var x _ _) a1 -> pure (repoint a1 b x)
          _ -> empty
    | otherwise -> do
        -- R-App
        a2 <- reduceC1 c t a
        pure (App d0 a2 b)
  a1 :> g -> do
    -- R-Conv
    a2 <- reduceC1 c t a1
    pure (a2 :> g)
  ind@(IndN x aA a1 a2 y a3) -> do
    -- R-Ind
    b1 <- reduceC1 c Logical a1
    bB0 <- infer c t ind
    bB1 <- infer c t (IndN x aA b1 a2 y a3)
    prove c t (Reflex bB1) -: bB1 :==: bB0
    pure (IndN x aA b1 a2 y a3 :> Reflex bB1)
  p -> pure p

-- | Administrative reduction
--
-- > _ :: Γ |- a ⇀ b
reduceA1 :: (MonadPlus m) => Context -> Termination -> Point -> m Point
reduceA1 c t = \case
  l@(Abs (Var x (Mode r0 t0) _) a1 :> g) -> do
    -- CR-AbsPush
    guard (t0 <= t)
    void (infer c t l) -- -: A
    prove (resurrect c) t0 g >>= \case
      Pi _ _ :==: Pi (Var _ _ aA2) _ -> do
        let a2 = repoint a1 (Point x :> Sym (Pifst t0 g)) x
            g2 = Pisnd t0 g (Reflex (Point x)) (Sym (Pifst t0 g))
        --
        pure (Abs (Var x (Mode r0 t0) aA2) a2 :> g2)
      _ -> empty
  a :> g1 :> g2 -> pure (a :> (g1 ::: g2)) -- CR-Combine
  a :> g
    -- CR-ConvRefl
    | Just (aA :==: bA) <- prove (resurrect c) t g, aA == bA -> pure a
    -- CR-ConvCong
    | Just b <- reduceA1 c t a -> pure (b :> g)
  Succ a1 -> Succ <$> reduceA1 c t a1 -- CR-Succ
  p -> pure p
