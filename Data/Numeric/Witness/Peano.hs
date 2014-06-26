{- |
Module      :  Data.Numeric.Witness.Peano
Description :  Peano-style natural numbers paired with type-level naturals.
Copyright   :  Copyright (c) 2014 Kenneth Foner

Maintainer  :  kenneth.foner@gmail.com
Stability   :  experimental
Portability :  non-portable

This module defines GADT type witnesses for Peano-style natural numbers.
-}

{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Numeric.Witness.Peano where

data Zero
data Succ n

-- | Natural numbers paired with type-level natural numbers. These terms act as witnesses of a particular natural.
data Natural n where
   Zero :: Natural Zero
   Succ :: Natural n -> Natural (Succ n)
deriving instance Show (Natural n)

-- | Given a context expecting a particular natural, we can manufacture it from the aether.
class ReifyNatural n                               where reifyNatural :: Natural n
instance ReifyNatural Zero                         where reifyNatural = Zero
instance (ReifyNatural n) => ReifyNatural (Succ n) where reifyNatural = Succ (reifyNatural :: Natural n)

-- | Type level less-than-or-equal test.
type family LessThanOrEqual a b where
   LessThanOrEqual Zero     Zero     = True
   LessThanOrEqual Zero     (Succ m) = True
   LessThanOrEqual (Succ n) (Succ m) = LessThanOrEqual n m
   LessThanOrEqual x y               = False

-- | This constraint is a more succinct way of requiring that @a@ be less than or equal to @b@.
type a <= b = (LessThanOrEqual a b ~ True)

-- | Type level less-than test.
type family LessThan a b where
   LessThan Zero     (Succ m) = True
   LessThan (Succ n) (Succ m) = LessThan n m
   LessThan x        y        = False

-- | This constraint is a more succinct way of requiring that @a@ be less than @b@.
type a < b = (LessThan a b ~ True)

-- | Type level addition.
type family x + y where
   x + Zero     = x
   x + (Succ y) = Succ (x + y)

-- | Type level subtraction.
type family x - y where
   x        - Zero     = x
   (Succ x) - (Succ y) = x - y

-- | Addition of naturals at the term and type levels simultaneously.
plus :: Natural a -> Natural b -> Natural (a + b)
plus x Zero     = x
plus x (Succ y) = Succ (plus x y)

-- | Subtraction of naturals at the term and type level simultaneously. Note that it is statically prohibited to subtract
--   a number larger than the number from which it is being subtracted.
minus :: (b <= a) => Natural a -> Natural b -> Natural (a - b)
minus x        Zero     = x
minus (Succ x) (Succ y) = minus x y
minus _ _ = error "minus: the impossible occurred" -- GHC can't prove this is unreachable
