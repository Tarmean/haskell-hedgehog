{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK not-home #-}

module Hedgehog.Internal.ShrinkMonad (runShrinkerList', Zipper (..), M, StepSize (..), SearchConfig (..), clipDepths, up, toBottom, toTop, forwardSearch, checkpoint, shrinkAllNodes, effCheckpoint, strat1, stratIncEven, runShrinkerPair, zipGen, dropT, avgStrat, stratInc) where

import Control.Applicative
  ( Alternative (empty, (<|>)),
  )
import Control.Monad (MonadPlus)
import Control.Monad.Cont
  ( ContT (..),
    MonadCont (callCC),
    MonadTrans (lift),
  )
import Control.Monad.Reader (MonadReader (ask), ReaderT (..))
import Control.Monad.State (MonadState (..), StateT (..), execStateT, gets, modify)
import qualified Data.Maybe as Maybe
import Hedgehog.Internal.Gen (GenT, freezeTreeT, replaceTreeT)
import qualified Hedgehog.Internal.Tree as T

type M x i o = ReaderT (i -> o) (StateT i (ContT (T.TreeT x o) []))

runM :: forall i o x. Applicative x => (i -> o) -> i -> M x i o () -> [T.TreeT x o]
runM extractFun state0 m = runContT (execStateT (runReaderT m extractFun) state0) (const empty)

data Zipper a = Zipper [a] [a]
  deriving (Eq, Ord, Show)

-- (f >> checkpoint >> g) <|> alts

-- |
-- value -
-- |
-- f - alts -
-- |    |
-- g-
-- |
checkpoint :: Applicative x => M x i o ()
checkpoint = do
  -- grab the current state
  curState <- get
  finalizer <- ask
  callCC $ \finish -> do
    -- 'run' the rest of the computation with the current state
    -- If code follows after checkpoint via (`>>=`), then none of that code is actually run.
    -- Instead, callCC grabs the `a -> m b` out of `m a -> (a -> m b) -> m b`, and hands it to us as `finish :: () -> m [T.TreeT x o]`.
    -- Now we can run it manually and construct the tree node.
    -- We run `finish ()` as a pure computation, giving it a copy of our current state:
    let children = runM finalizer curState (finish ())
    -- Now we must yield a new tree
    --  - with the current state as head
    --  - with the output of the continuations as child nodes
    let newNode = T.fromNodeT $ T.NodeT (finalizer curState) children
    -- Output this tree node. Everything after checkpoint isn't run
    -- - which is good because we already ran it and put the result into newNode.
    -- Laziness means `rest` is only demanded if Hedgehog actually walks down this branch, though
    lift (lift $ yield newNode)

effCheckpoint :: Monad x => x i -> M x i o ()
effCheckpoint x = do
  finalizer <- ask
  callCC $ \finish -> do
    let newNode = T.TreeT $ do
          s' <- x
          let children = runM finalizer s' (finish ())
          pure $ T.NodeT (finalizer s') children
    lift (lift $ yield newNode)

times :: (Applicative x) => M x i o Bool -> Int -> M x i o ()
times step n0 = go n0 False
  where
    go 0 True = checkpoint
    go 0 False = pure ()
    go n a = step >>= \b -> go (n -1) (a || b)

data SearchConfig x i o = SearchConfig
  { searchStep :: M x i o Bool,
    searchSkip :: M x i o (),
    searchLimit :: Int -> M x i o Int,
    stepSize :: StepSize
  }

data StepSize = forall c.
  StepSize
  { szState :: c,
    szSize :: c -> Int,
    szDidConsume :: Int -> c -> c,
    szThenFailed :: c -> c
  }

forwardSearch :: (Applicative x) => SearchConfig x i o -> M x i o ()
forwardSearch conf = do
  n <- nextSize conf
  if n == 0
    then pure ()
    else (times (searchStep conf) n >> forwardSearch (didConsume n conf)) <|> backtrackSearch conf n

backtrackSearch :: (Applicative x) => SearchConfig x i o -> Int -> M x i o ()
backtrackSearch = go
  where
    -- somewhere in the next `i` steps is an element that causes failure when removed
    -- do a binary search to identify the first such element
    go _ 0 = pure ()
    go conf 1 =
      (searchSkip conf *> forwardSearch (foundFailure conf)) <|> pure ()
    go conf i = do
      let t = i `div` 2
      (times (searchStep conf) t *> go (didConsume t conf) (i - t)) <|> go conf t

zipUpDepth :: Zipper a -> Int
zipUpDepth (Zipper _ a) = length a

clipDepths :: Applicative x => Int -> M x (Zipper i) o Int
clipDepths i = do
  leftover <- gets zipDepth
  pure (min leftover i)

-- shrinks, time
-- 22, 2:18
strat1 :: StepSize
strat1 = StepSize 1 id (\_ _ -> 1) (const 1)

-- 10, 1:57
stratInc :: StepSize
stratInc = StepSize 1 id (\_ i -> i + 1) (const 1)

-- 9, 1:39
-- with start 7: 7, 1:57
stratIncEven :: StepSize
stratIncEven = StepSize 10 toEven (\_ i -> i + 1) (\i -> max 2 $ i `div` 2 + 1)
  where
    -- 1,1,2,2,4,4,6,6,8,8
    -- starts high because tail might not be used, continues low
    toEven 1 = 1
    toEven 2 = 1
    toEven i = 2 * (i - 1 `div` 2)

-- 9, 1:57
avgStrat :: Int -> StepSize
avgStrat initial = StepSize initS proj accept failed
  where
    accept i (a, b, c) = (a + 1, b + i, c)
    failed (_, b, c) = (mix b c, 0, Just $ mix b c)
    initS = (initial, 0, Nothing)
    proj (cur, _, _) = cur
    mix b Nothing = b
    mix b (Just c) = floor (0.5 * fromIntegral b + 0.5 * fromIntegral c :: Double)

nextSize :: SearchConfig x i o -> M x i o Int
nextSize SearchConfig {searchLimit, stepSize = StepSize {szState, szSize}} = searchLimit (szSize szState)

didConsume :: Int -> SearchConfig x i o -> SearchConfig x i o
didConsume n s@SearchConfig {stepSize = StepSize {..}} = s {stepSize = StepSize {szState = szDidConsume n szState, ..}}

foundFailure :: SearchConfig x i o -> SearchConfig x i o
foundFailure s@SearchConfig {stepSize = StepSize {..}} = s {stepSize = StepSize {szState = szThenFailed szState, ..}}

zipDepth :: Zipper a0 -> Int
zipDepth (Zipper l _) = length l

-- FIXME: finishing a loop without cut can lead to blowup. Maybe add a type
-- index for sequential vs branching steps?
-- >>> empty <|> pure () <|> pure () >> [1,2,3]
-- [1,2,3,1,2,3]

-- TODO: This has bottom up hardcoded, can we use a combinator?
shrinkChildren :: forall x i o. Monad x => M x (Zipper (T.NodeT x i)) o ()
shrinkChildren = do
  s <- get
  case s of
    Zipper xs (node : r) -> do
      downNode node xs r <|> skipNode node
    _ -> pure ()
  where
    downNode (T.NodeT _ (mx : _)) xs r = do
      effCheckpoint $ do
        x <- T.runTreeT mx
        pure (Zipper xs (x : r))
      shrinkChildren
    downNode _ _ _ = empty

    skipNode (T.NodeT v (_ : ys)) = do
      setNode (T.NodeT v ys)
      shrinkChildren
    skipNode _ = pure ()

shrinkAllNodes :: Monad x => M x (Zipper (T.NodeT x i)) o ()
shrinkAllNodes = do
  i <- gets zipUpDepth
  if i == 0
    then pure ()
    else shrinkChildren *> modify (Maybe.fromJust . down) *> shrinkAllNodes

toBottom :: M x (Zipper i) o ()
toBottom = modify $ \(Zipper l r) -> Zipper (reverse r <> l) []

toTop :: M x (Zipper i) o ()
toTop = modify $ \(Zipper l r) -> Zipper [] (reverse l <> r)

setNode :: i -> M x (Zipper i) o ()
setNode a = do
  s <- get
  case s of
    (Zipper theUp (_ : theDown)) -> put $ Zipper theUp (a : theDown)
    _ -> undefined

runShrinkerList' :: Applicative m => M m (Zipper i) o () -> ([i] -> o) -> [i] -> T.NodeT m o
runShrinkerList' m extract ls = T.NodeT (extract ls) (runM (extract . reconstructZipper) zipper m)
  where
    zipper = Zipper (reverse ls) []

-- dropActions :: Applicative x => StepSize -> SearchConfig x (Action m state) o
-- dropActions :: Applicative x => StepSize -> SearchConfig x (T.NodeT m (Action m state)) o

zipGen :: Monad m => GenT m a -> GenT m b -> GenT m (a, b)
zipGen l r =
  replaceTreeT runShrinkerPairT $
    (,) <$> freezeTreeT l <*> freezeTreeT r
  where
    runShrinkerPairT (l', r') = T.TreeT $ runShrinkerPair <$> T.runTreeT l' <*> T.runTreeT r'

down :: Zipper a -> Maybe (Zipper a)
down (Zipper l (x : xs)) = Just $ Zipper (x : l) xs
down _ = Nothing

up :: Zipper a -> Maybe (Zipper a)
up (Zipper (x : xs) r) = Just $ Zipper xs (x : r)
up _ = Nothing

dropT :: Zipper a -> Maybe (a, Zipper a)
dropT (Zipper (a : xs) r) = Just (a, Zipper xs r)
dropT _ = Nothing

reconstructZipper :: Zipper a -> [a]
reconstructZipper (Zipper l r) = reverse l <> r

yield :: (Applicative m) => r -> ContT r m a
yield r = ContT $ \_ -> pure r

-- FIXME: Remove orphan by creating a ContT copy?
instance Alternative m => Alternative (ContT r m) where
  empty = ContT $ const empty
  l <|> r = ContT $ \w -> runContT l w <|> runContT r w

class Applicative m => FAlternative m where
  (<!?>) :: m a -> m a -> m a

instance FAlternative (ContT r []) where
  (<!?>) :: ContT r [] a -> ContT r [] a -> ContT r [] a
  l <!?> r = ContT $ \w -> case runContT l w of
    [] -> runContT r w
    xs -> xs

instance (Monad m, FAlternative m) => FAlternative (StateT s m) where
  l <!?> r = StateT $ \s -> runStateT l s <!?> runStateT r s

instance FAlternative m => FAlternative (ReaderT s m) where
  l <!?> r = ReaderT $ \s -> runReaderT l s <!?> runReaderT r s

instance Alternative m => MonadPlus (ContT r m)

runShrinkerPair :: Monad m => T.NodeT m a -> T.NodeT m b -> T.NodeT m (a, b)
runShrinkerPair l0 r0 = T.NodeT (extract (l0, r0)) $ runM extract (l0, r0) (stepRight *> checkpoint *> stepLeft)
  where
    shrinkLeft = do
      (T.NodeT _ (mx : _), r) <- get
      effCheckpoint $ do
        x <- T.runTreeT mx
        pure (x, r)
    shrinkRight = do
      (l, T.NodeT _ (mx : _)) <- get
      effCheckpoint $ do
        x <- T.runTreeT mx
        pure (l, x)
    skipLeft = do
      (T.NodeT v (_ : l : ls), r) <- get
      put (T.NodeT v (l : ls), r)
    skipRight = do
      (l, T.NodeT v (_ : r : rs)) <- get
      put (l, T.NodeT v (r : rs))

    stepRight = (shrinkRight *> stepRight) <|> branching skipRight (pure ()) (const stepRight)
    stepLeft = (shrinkLeft *> stepLeft) <|> branching skipLeft (pure ()) (const stepLeft)
    extract (l, r) = (T.nodeValue l, T.nodeValue r)

branching :: (Monad m, FAlternative m) => m a -> m b -> (a -> m b) -> m b
branching m l r = do
  s <- (Just <$> m) <!?> pure Nothing
  maybe l r s
