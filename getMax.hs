{-# LANGUAGE TypeApplications #-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--exact-data" @-}

module MightRedBlack where

import Prelude hiding (max)
import Control.Monad 
import Test.QuickCheck hiding (elements)
import Data.List(nub,sort)

data Color = 
   R  -- red
 | B  -- black
 | BB -- double black
 | NB -- negative black
 deriving (Show, Eq)

data RBSet a =
   E  -- black leaf
 | T Color a (RBSet a) (RBSet a)
 deriving (Show, Eq)

-- Helper functions for verification

-- | Trees with value less than X
{-@ type RBSL a X = RBSet {v:a | v < X}  @-}

-- | Trees with value greater than X
{-@ type RBSR a X = RBSet {v:a | X < v}  @-}

{-@ data RBSet a = E 
                 | T { c     :: Color
                     , key   :: a
                     , lt    :: RBSL a key 
                     , rt    :: RBSR a key 
                     }
@-}

{-@ measure max' @-}
{-@ max' :: x:RBSet a -> {v:a | v = fst(getMax x)} @-}
max' :: RBSet a -> a
max' (T _ x _ E) = x
max' (T _ x _ r) = max' r

{-@ removeMax :: x:RBSet a -> {v:RBSet a | v = snd(getMax x)} @-}
removeMax :: RBSet a -> RBSet a
removeMax s@(T _ _ l E) = l
removeMax s@(T color x l r) = T color x l (removeMax r)

{-@ measure getMax @-}
{-@ getMax :: x:RBSet a -> (m :: a, {v : RBSet {w : a | (w < m)} | v /= x }) @-} 
getMax :: RBSet a -> (a, RBSet a)
getMax (T _ m l E) = (m, l) 
getMax (T c x l r) = case getMax r of (m, r') -> (m, T c x l r') 

remove (T color y l r) = T color mx l' r 
    where 
        (mx, l') = getMax l
