-- variant of T5327, where we force the newtype to have a wrapper
{-# LANGUAGE GADTs, ExplicitForAll #-}
module T16254 where

newtype Size a b where
  Size :: forall b a. Int -> Size a b

{-# INLINABLE val2 #-}
val2 = Size 17

-- In the core, we should see a comparison against 34#, i.e. constant
-- folding should have happened. We actually see it twice: Once in f's
-- definition, and once in its unfolding.
f n = case val2 of Size s -> s + s > n
