module Language.SystemDE where

import Control.Monad (MonadPlus, unless, void, when)
import Control.Monad.Except (ExceptT)
import Control.Monad.Trans.Except (throwE)
import Data.Functor (($>), (<&>))
import Data.Text (Text)

newtype Id = Id Text
  deriving (Eq, Ord, Show)

data Relevance = Relevant | Irrelevant
  deriving (Eq, Ord, Show)

data Termination = Logical | Program
  deriving (Eq, Ord, Show)

data Mode = Mode {rho :: Relevance, theta :: Termination}
  deriving (Eq, Ord, Show)

pattern RL :: Mode
pattern RL = Mode Relevant Logical

data Var ty = Var
  { name :: Id
  , mode :: Mode
  , ty :: ty
  }
  deriving (Eq, Ord, Show)

data Context
  = C_ -- T-Empty
  | (:&) Context (Var Point)
  deriving (Eq, Ord, Show)

resurrect :: Context -> Context
resurrect = \case
  C_ -> C_
  c :& Var x (Mode _ t) a -> resurrect c :& Var x (Mode Relevant t) a

(~) :: Context -> Context
(~) = resurrect

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
pattern IndN x aA a1 a2 y a3 = Ind (Pi (Var (Id x) RL NN) aA) a1 a2 (y, a3)

-- |
-- @'repoint' point with name@ replaces all occurrences of
-- the pattern @'Point' name@ in @point@ with @with@.
--
-- If @name@ occurs as a function argument in @point@, that argument
-- is first safely 'repoint'ed in its result before 'repoint'ing
-- the outer expression.
--
-- c.f. 'recoerce'
repoint :: Point -> Point -> Text -> Point
repoint point with name = case point of
  Point p | p == name -> with
  Pi (Var (Id x) m aA) a ->
    if x == name
      then repoint
        do Pi (Var (Id do x <> name) m aA) (repoint a (Point (x <> name)) x)
        do with
        do name
      else Pi (Var (Id x) m aA) (repoint a with name)
  Abs (Var (Id x) m aA) a ->
    if x == name
      then repoint
        do Abs (Var (Id do x <> name) m aA) (repoint a (Point (x <> name)) x)
        do with
        do name
      else Abs (Var (Id x) m aA) (repoint a with name)
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
  IndCong (Pi (Var (Id x) RL NN) aA) g1 g2 (y, g3) g

-- |
-- @'recoerce' coercion with name@ replaces all occurrences of
-- the pattern @'Point' name@ in @coercion@ with @with@.
--
-- c.f. 'repoint'
recoerce :: Coercion -> Point -> Text -> Coercion
recoerce coercion with name = case coercion of
  Reflect point -> Reflect (repoint point with name)
  Reflex point -> Reflex (repoint point with name)
  Sym g -> Sym (recoerce g with name)
  g1 ::: g2 -> recoerce g1 with name ::: recoerce g2 with name
  PiCong (Var (Id x) m g1) g2 ->
    if x == name
      then recoerce
        do
          PiCong
            do Var (Id do x <> name) m g1
            do recoerce g1 (Point (x <> name)) x
        do with
        do name
      else PiCong (Var (Id x) m (recoerce g1 with name)) (recoerce g2 with name)
  AbsCong (Var (Id x) m aA) g
    | x == name -> recoerce
        do
          AbsCong
            do Var (Id do x <> name) m aA
            do recoerce g (Point (x <> name)) x
        do with
        do name
    | otherwise -> AbsCong (Var (Id x) m aA) (recoerce g with name)
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
  Pisnd t g g1 g2 -> Pisnd
    do t
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

value :: Point -> Bool
value = \case
  Star{} -> True
  Point{} -> True
  Pi{} -> True
  Abs{} -> True
  Equal{} -> True
  Reify{} -> True
  NN{} -> True
  Zero{} -> True
  Succ{} -> True
  _ -> False

covalue :: Point -> Bool
covalue = \case
  c :> _ -> covalue c
  Succ c -> covalue c
  p -> value p

data InferenceError
  = TypeOfStarLogical
  | NeedsStrongerTermination Termination Termination
  | NeedsStrongerRelevance Relevance Relevance
  | Mismatch Point Point
  | MismatchPath Path Path
  | UnknownIdentifier Id
  | ReusedIdentifier Id (Var Point)
  | ApplicationPatternFailure Point Point
  | InductionPatternFailure Point
  | ApplicationPathPatternFailure Path
  | ReflectionPatternFailure Point
  | InductionCongruencePatternFailure Coercion
  | UtterFailure
instance Semigroup InferenceError where
  (<>) :: InferenceError -> InferenceError -> InferenceError
  (<>) = const
instance Monoid InferenceError where
  mempty :: InferenceError
  mempty = UtterFailure

class (MonadPlus m) => MonadInference m where
  inferenceError :: InferenceError -> m a

instance MonadInference Maybe where
  inferenceError :: InferenceError -> Maybe a
  inferenceError = const Nothing

instance (Monad m) => MonadInference (ExceptT InferenceError m) where
  inferenceError :: InferenceError -> ExceptT InferenceError m a
  inferenceError = throwE

-- read `Var x d0 aA <- name ∈ context` as `context |- x ::d0 aA`
(∈) :: (MonadInference m) => Id -> Context -> m (Var Point)
name ∈ context0 = case context0 of
  C_ -> inferenceError do UnknownIdentifier name
  _ :& v@(Var x _ _) | x == name -> pure v
  c :& _ -> name ∈ c

(∉) :: (MonadInference m) => Id -> Context -> m ()
(∉) x = \case
  C_ -> pure ()
  c :& p@(Var y _ _) -> do
    when (x == y) do inferenceError do ReusedIdentifier x p
    x ∉ c

(+:) :: (MonadInference m) => Context -> Var Point -> m Context
c +: (Var x (Mode r t) a) = do
  -- T-ConsTm
  infer (c ~) t a .= Star
  x ∉ c
  --
  pure (c :& Var x (Mode r t) a)

infixl 7 .=
infixl 7 .==

(.=) :: (MonadInference m) => m Point -> Point -> m ()
action .= x = do
  y <- action
  mismatchUnequal x y

(.==) :: (MonadInference m) => m Path -> Path -> m ()
action .== x = do
  y <- action
  unless (x == y) do inferenceError do MismatchPath x y

terminate :: (MonadInference m) => Termination -> Termination -> m ()
terminate t0 t =
  unless (t0 <= t) do inferenceError do NeedsStrongerTermination t0 t

relieve :: (MonadInference f) => Relevance -> Relevance -> f ()
relieve r0 r =
  unless (r0 <= r) do inferenceError do NeedsStrongerRelevance r0 r

mismatchUnequal :: (MonadInference f) => Point -> Point -> f ()
mismatchUnequal a b = unless (a == b) do inferenceError do Mismatch a b

-- |
-- Type inference algorithm for System DE.
--
-- >>> infer @Maybe C_ Logical Star
-- Nothing
--
-- >>> infer @Maybe C_ Program Star
-- Just Star
infer :: (MonadInference m) => Context -> Termination -> Point -> m Point
infer c t = \case
  -- read `ty <- point` as `point :: ty`
  Star -> case t of
    -- T-TYPE
    Logical -> inferenceError TypeOfStarLogical
    Program -> pure Star
  Point x -> do
    -- T-Var
    Var _ rt0 a <- Id x ∈ c
    terminate rt0.theta t
    relieve rt0.rho Relevant
    --
    pure a
  Pi (Var x (Mode _ t0) aA) b -> do
    -- T-Pi
    infer c t aA .= Star
    c' <- c +: Var x (Mode Relevant t0) aA
    infer c' t b .= Star
    --
    pure Star
  Abs xA b -> do
    -- T-Abs
    c' <- c +: xA
    bB <- infer c' t b
    infer (c ~) t (Pi xA bB) .= Star
    --
    pure (Pi xA bB)
  App mode b a -> do
    -- T-App
    tyB <- infer c t b
    case tyB of
      Pi (Var (Id x) m aA) bB -> do
        terminate m.theta mode.theta
        relieve m.rho mode.rho
        infer c t a .= aA
        --
        pure (repoint bB a x)
      _ -> inferenceError do ApplicationPatternFailure b a
  Equal t0 a b -> do
    -- T-Eq
    aA <- infer c t0 a
    infer c t0 b .= aA
    --
    pure Star
  Reify t0 g -> do
    -- T-Reify
    a :==: b <- prove c t0 g
    --
    pure (Equal t0 a b)
  a :> g -> do
    -- T-Conv
    aA :==: bB <- prove (c ~) t g
    infer c t a .= aA
    --
    pure bB
  NN -> pure Star -- T-Nat
  Zero -> pure NN -- T-Zero
  Succ a -> do
    -- T-Succ
    infer c t a .= NN
    --
    pure NN
  IndN x aA a1 a2 y a3 -> do
    -- T-Ind
    let x_ ^: n = Var (Id x_) RL n
    infer (c ~) Logical (Pi (x ^: NN) aA) .= Star
    infer c Logical a1 .= NN
    infer c Logical a2 .= repoint aA Zero x
    c' <- c +: Var (Id y) RL NN
    let ayx = repoint aA (Point y) x
        asyx = repoint aA (Succ $ Point y) x
    infer c' Logical a3 .= Pi (x ^: ayx) asyx
    --
    pure (repoint aA a1 x)
  p@Ind{} -> inferenceError do InductionPatternFailure p

infixr 8 :==:

data Path = Point :==: Point
  deriving (Eq, Ord, Show)

-- |
-- Prove the equality of two 'Point's along a 'Path' given a 'Coercion'.
prove :: (MonadInference m) => Context -> Termination -> Coercion -> m Path
prove c t = \case
  Reflect a0@(Equal t0 a b) -> do
    -- E-Reflect
    terminate t0 t
    void (infer c Logical a0)
    aA <- infer c t a
    infer c t b .= aA
    --
    pure (a :==: b)
  Reflect p -> inferenceError do ReflectionPatternFailure p
  Reflex a -> infer c t a $> a :==: a -- E-Reflex
  Sym g -> prove c t g <&> \(a :==: b) -> b :==: a -- E-Sym
  g1 ::: g2 -> do
    -- E-Trans
    x :==: b1 <- prove c t g1
    b2 :==: y <- prove c t g2
    mismatchUnequal b1 b2
    --
    pure (x :==: y)
  PiCong (Var (Id x) (Mode r0 t0) g1) g2 -> do
    -- E-PiCong
    a1 :==: a2 <- prove c t g1
    c' <- c +: Var (Id x) (Mode Relevant t0) a1
    b1 :==: b2 <- prove c' t g2
    infer c t (Pi (Var (Id x) (Mode r0 t0) a1) b1) .= Star
    infer c t (Pi (Var (Id x) (Mode r0 t0) a1) b2) .= Star
    let b3 = repoint b2 (Point x :> Sym g1) x
    --
    pure do
      Pi (Var (Id x) (Mode r0 t0) a1) b1 :==: Pi (Var (Id x) (Mode r0 t0) a2) b3
  AbsCong l@(Var _ (Mode _ t0) aA) g -> do
    -- E-AbsCong
    infer (c ~) t0 aA .= Star
    c' <- c +: l
    a1 :==: a2 <- prove c' t g
    _b <- infer c t (Abs l a2)
    --
    pure (Abs l a1 :==: Abs l a2)
  AppCong g1 g2 g -> do
    -- E-AppCong
    a1 :==: a2 <- prove c t g1
    b1 :==: b2 <- prove c t g2
    a :==: b <- prove (c ~) t g
    infer c t (App (Mode Relevant t) a1 b1) .= a
    infer c t (App (Mode Relevant t) a2 b2) .= b
    --
    pure ((App (Mode Relevant t) a1 b1 :> g) :==: App (Mode Relevant t) a2 b2)
  AppCongIrrel g1 b1 b2 g -> do
    -- E-AppCongIrrel
    let c' = resurrect c
        a @ b = App (Mode Irrelevant t) a b
    a1 :==: a2 <- prove c t g1
    aA <- infer c' t b1
    infer c' t b2 .= aA
    bB1 :==: bB2 <- prove c' t g
    infer c t (a1 @ b1) .= bB1
    infer c t (a2 @ b2) .= bB2
    --
    pure (a1 @ b1 :> g :==: a2 @ b2)
  Reduction a b -> do
    -- E-Red
    reducePrim c t a .= b
    pure (a :==: b)
  ReifyCong t0 g1 g2 -> do
    -- E-ReifyCong
    p <- prove c t0 g1
    prove c t0 g2 .== p
    --
    pure (Reify t0 g1 :==: Reify t0 g2)
  Pifst t0 g -> do
    -- E-PiFst
    prove c t0 g >>= \case
      Pi (Var _ (Mode _ th) a1) _ :==: Pi (Var _ _ a2) _ -> do
        terminate th t
        --
        pure (a1 :==: a2)
      p -> inferenceError do ApplicationPathPatternFailure p
  Pisnd t0 g g1 g2 -> do
    -- E-PiSnd
    terminate t0 t
    prove c t0 g >>= \case
      Pi (Var (Id x1) (Mode _ t1) aA1) bB1 :==: Pi (Var (Id x2) _ aA2) bB2 -> do
        a1 :==: a2 <- prove c t1 g1
        infer c t1 a2 .= aA2
        prove c t1 g2 .== aA2 :==: aA1
        --
        pure (repoint bB1 (a1 :> g2) x1 :==: repoint bB2 a2 x2)
      p -> inferenceError do ApplicationPathPatternFailure p
  ConvCong g g1 g2 -> do
    -- E-ConvCong
    a1 :==: a2 <- prove c t g
    a1A <- infer c t (a1 :> g1)
    infer c t (a2 :> g2) .= a1A
    --
    pure (a1 :> g1 :==: a2 :> g2)
  EqualCong t0 g1 g2 -> do
    -- E-EqCong
    a1 :==: a2 <- prove c t0 g1
    b1 :==: b2 <- prove c t0 g2
    infer c t (Equal t0 a1 b1) .= Star
    --
    pure (Equal t0 a1 b1 :==: Equal t0 a2 b2)
  SuccCong g -> do
    -- E-SuccCong
    a :==: b <- prove c t g
    infer c t a .= NN
    --
    pure (Succ a :==: Succ b)
  IndNCong x aA g1 g2 y g3 g -> do
    -- E-IndCong
    infer (c ~) Logical (Pi (Var (Id x) RL NN) aA) .= Star
    a1 :==: b1 <- prove c Logical g1
    a2 :==: b2 <- prove c Logical g2
    c' <- c +: Var (Id y) RL NN
    a3 :==: b3 <- prove c' Logical g3
    a0 <- infer c t (IndN x aA a1 a2 y a3)
    b0 <- infer c t (IndN x aA b1 b2 y b3)
    prove c t g .== a0 :==: b0
    --
    pure (IndN x aA a1 a2 y a3 :> g :==: IndN x aA b1 b2 y b3)
  g@IndCong{} -> inferenceError do InductionCongruencePatternFailure g

reducePrim :: (MonadInference m) => Context -> Termination -> Point -> m Point
reducePrim c t = liftA2 (*>) (infer c t) \case
  -- aBeta-AppAbs
  App mode (Abs (Var (Id x) m _) a) b | mode == m -> pure (repoint a b x)
  Abs l@(Var (Id x) (Mode _ t0) _) a1 :> g -> do
    -- aBeta-AbsPush
    void (infer c t (Abs l a1 :> g))
    terminate t0 t
    prove c t0 g >>= \case
      Pi _ _ :==: Pi (Var (Id y) d2 aA2) _ -> do
        let a2 = repoint a1 (Point x :> Sym (Pifst t0 g)) x
        let g2 = Pisnd t0 g (Reflex (Point x)) (Sym (Pifst t0 g))
        --
        pure (Abs (Var (Id y) d2 aA2) (a2 :> g2))
      p -> inferenceError do ApplicationPathPatternFailure p
  a :> g1 :> g2 -> pure (a :> (g1 ::: g2)) -- aBeta-Combine
  a :> g -> do
    -- aBeta-ConvRefl
    aA1 :==: aA2 <- prove c t g
    mismatchUnequal aA1 aA2
    --
    pure a
  IndN _ _ Zero a2 _ _ -> pure a2 -- aBeta-IndZero
  IndN x aA (Succ a1) a2 y a3 ->
    -- aBeta-IndSucc
    pure (App RL (repoint a3 a1 y) (IndN x aA a1 a2 y a3))
  p -> pure p

-- | Computational
--
-- > _ :: Γ |- a ~> b
reduceC1 :: (MonadInference m) => Context -> Termination -> Point -> m Point
reduceC1 c t = \case
  App d0 a b
    | covalue a -> do
        -- R-AppAbs
        reduceA1 c t a >>= \case
          Abs (Var (Id x) _ _) a1 -> pure (repoint a1 b x)
          _ -> inferenceError do ApplicationPatternFailure a b
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
    -- Proof introduction,
    let g = Reflex bB1 :: Coercion
    -- because reduction is confluent and preserves
    -- Reflex bB0 : bB0 :==: bB0 ~> Reflex bB1 : bB1 :==: bB1.
    prove (c ~) t g .== bB1 :==: bB0
    pure (IndN x aA b1 a2 y a3 :> g)
  p -> pure p

-- | Administrative reduction
--
-- > _ :: Γ |- a ⇀ b
reduceA1 :: (MonadInference m) => Context -> Termination -> Point -> m Point
reduceA1 c t = \case
  l@(Abs (Var (Id x) (Mode r0 t0) _) a1 :> g) -> do
    -- CR-AbsPush
    terminate t0 t
    void (infer c t l) -- .= A
    prove (c ~) t0 g >>= \case
      Pi _ _ :==: Pi (Var _ _ aA2) _ -> do
        let a2 = repoint a1 (Point x :> Sym (Pifst t0 g)) x
            g2 = Pisnd t0 g (Reflex (Point x)) (Sym (Pifst t0 g))
        --
        pure (Abs (Var (Id x) (Mode r0 t0) aA2) a2 :> g2)
      p -> inferenceError do ApplicationPathPatternFailure p
  a :> g1 :> g2 -> pure (a :> (g1 ::: g2)) -- CR-Combine
  a :> g
    -- CR-ConvRefl
    | Just (aA :==: bA) <- prove (c ~) t g, aA == bA -> pure a
    -- CR-ConvCong
    | Just b <- reduceA1 c t a -> pure (b :> g)
  Succ a1 -> Succ <$> reduceA1 c t a1 -- CR-Succ
  p -> pure p
