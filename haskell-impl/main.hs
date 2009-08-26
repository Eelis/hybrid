{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -cpp #-}

-- Run with: "runhaskell main.hs"

-- import Debug.Trace
import qualified Control.Exception

type R = Double

data Range space = Range { left :: space, right :: space } -- invariant: first <= second
  deriving Eq

top, bottom :: Range space -> space
top = left
bottom = right

inf :: Num a => a
inf = 10000

instance Show (Range R) where
  show r | r == empty_range = "empty"
  show r | r == unbounded_range = "(inf, inf)"
  show (Range x y) = show (x, y)


empty_range, unbounded_range :: Num space => Range space

empty_range = Range 1 (-1) -- deliberately breaks invariant
unbounded_range = Range (-inf) inf

overlap :: (Ord space, Num space) => Range space -> Range space -> Bool
overlap r _ | r == empty_range = False
overlap _ r | r == empty_range = False
overlap (Range a_left a_right) (Range b_left b_right) = a_left <= b_right && b_left <= a_right

in_range :: Ord a => a -> Range a -> Bool
in_range v (Range a b) = a <= v && v <= b

data Square space = Square (Range space) (Range space)
  deriving Eq

type Duration = R -- invariant: nonneg

type Flow space = space -> Duration -> space

type PointwiseFlowInv space = space -> space -> Duration
  -- this is a pointwise inverse
type RangeFlowInv space = Range space -> Range space -> Range Duration

x_boundaries :: [R]
x_boundaries = [0, 0.01, 0.5, 1.01, 1.99, 3]

y_boundaries :: [R]
y_boundaries = [4.99, 6, 8, 8.9, 10]

x_range, y_range :: Int -> Range R
x_range i = Range (x_boundaries !! i) (x_boundaries !! (i+1))
y_range i = Range (y_boundaries !! i) (y_boundaries !! (i+1))

s0, s1, s2 :: Square R
s0 = Square (x_range 0) (y_range 0)
s1 = Square (x_range 1) (y_range 0)
s2 = Square (x_range 2) (y_range 0)

constant_flow_inv :: RangeFlowInv R
constant_flow_inv src dest = if overlap src dest then unbounded_range else empty_range

linear_flow_inv :: RangeFlowInv R
linear_flow_inv src dst = Range (left dst - right src) (right dst - left src)

#define assrt (flip Control.Exception.assert (return ()))


-- CONTINOUS TRANSITIONS:

-- the redundancy-specification below is relative to flow going right in a straight line

redundant_ranges :: [RedundantRanges]
redundant_ranges = [(x_range i, x_range (i-1)) | i <- [1..4]]

range_redundant :: Range R -> Range R -> Bool
range_redundant a b = (a, b) `elem` redundant_ranges

squares_redundant :: Square R -> Square R -> Bool
squares_redundant (Square xr yr) (Square xr' yr') = range_redundant xr xr' || range_redundant yr yr'

naive_continuous_abstract_transition :: Square R -> Square R -> RangeFlowInv R -> RangeFlowInv R -> Bool
  -- Works on squares only because continuous transitions don't change location.
naive_continuous_abstract_transition (Square ax ay) (Square bx by)
        x_inv y_inv =
          let xi = x_inv ax bx in
          let yi = y_inv ay by in
            overlap xi yi &&
            overlap xi (Range 0 inf)

type RedundantSquares = (Square R, Square R)
  -- idea: A transition from s to s' is "redundant" if the only way to flow from s to s' is by a continuous transition to a point in s' that is actually already in s.

type RedundantRanges = (Range R, Range R)

hinted_continuous_abstract_transition :: Square R -> Square R -> RangeFlowInv R -> RangeFlowInv R -> (Square R -> Square R -> Bool) -> Bool
hinted_continuous_abstract_transition a b xinv yinv redundancy_detector =
  if redundancy_detector a b then False else naive_continuous_abstract_transition a b xinv yinv


-- DISCRETE TRANSITIONS:

data Location = Heat | Cool | Check

type Point = (R, R)
  -- (clock, temp)

type Guard = Point -> Bool

data ResetFunction
  = OrdinaryResetFunction (R -> R)
  | ConstantFunction R
  | IdentityFunction

eval_reset :: ResetFunction -> (R -> R)
eval_reset (OrdinaryResetFunction f) = f
eval_reset (ConstantFunction v) = const v
eval_reset IdentityFunction = id

data DiscTrans = DiscTrans
  { guard :: Point -> Bool
  , reset_x :: ResetFunction -- was: R -> R
  , reset_y :: ResetFunction -- was: R -> R
      -- invariant: both of these are monotonic
  }

disc_trans :: Location -> Location -> Maybe DiscTrans
disc_trans Heat Cool = Just (DiscTrans
  (const True) -- no guard for now
  (ConstantFunction 0)
  IdentityFunction)
disc_trans _ _ = Nothing -- no other transitions

type AbstractState = (Location, Square R)

instance Functor Range where
  fmap f (Range a b) = Range (f a) (f b)

abstract_discrete_transition :: AbstractState -> AbstractState -> Bool
abstract_discrete_transition (l, (Square xr yr)) (l', (Square xr' yr')) = case disc_trans l l' of
  Nothing -> False
  Just (DiscTrans g res_x res_y) ->
    -- we would need to check whether there's a point in s for which g is true now, but we don't.
    -- we ignore invariants for now
    -- we now check whether there's a point in s which the reset function r maps to a point in s'.
    case res_x of
      OrdinaryResetFunction f -> overlap (fmap f xr) xr'
      IdentityFunction -> xr == xr'
      ConstantFunction v -> v `in_range` xr'
    && case res_y of
      OrdinaryResetFunction f -> overlap (fmap f yr) yr'
      IdentityFunction -> yr == yr'
      ConstantFunction v -> v `in_range` yr'


src, dest, dest', dest'' :: AbstractState

src = (Heat, Square (x_range 3) (y_range 3))
dest = (Cool, Square (x_range 0) (y_range 3))
dest' = (Cool, Square (x_range 0) (y_range 0))
dest'' = (Cool, Square (x_range 0) (y_range 2))

main :: IO ()
main = do
  assrt (naive_continuous_abstract_transition s0 s2 constant_flow_inv constant_flow_inv == False)
  assrt (naive_continuous_abstract_transition s0 s1 linear_flow_inv constant_flow_inv == True)
  assrt (naive_continuous_abstract_transition s0 s2 linear_flow_inv constant_flow_inv == True)
  assrt (hinted_continuous_abstract_transition s1 s0 linear_flow_inv constant_flow_inv squares_redundant == False)
  assrt (abstract_discrete_transition src dest == True)
  assrt (abstract_discrete_transition src dest' == False)
  assrt (abstract_discrete_transition src dest'' == False)
  putStrLn "Ok."
