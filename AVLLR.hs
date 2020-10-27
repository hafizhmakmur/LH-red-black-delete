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
 | EE -- double black leaf
 | T Color a (RBSet a) (RBSet a)
 deriving (Show, Eq)

-- | Trees with value less than X
{-@ type RBSL a X = RBSet {v:a | v < X}  @-}

-- | Trees with value greater than X
{-@ type RBSR a X = RBSet {v:a | X < v}  @-}

{-@ data RBSet a = E 
                 | EE 
                 | T { c     :: Color
                     , key   :: a
                     , lt    :: RBSL a key 
                     , rt    :: RBSR a key 
                     }
@-}

--{-@ blacken' :: IM a -> RT a @-}    
-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R a x b) = T B a x b
blacken' (T B a x b) = T B a x b

--{-@ redden :: {x:CT a | color' x == B} 
--           -> {v:IM a | blackHeightL v == (blackHeightL x - 1) } @-}
redden :: RBSet a -> RBSet a
redden (T _ x a b) = T R x a b

--{-@ insert :: (Ord a) => a -> RT a -> RT a @-}
--{-@ ins :: (Ord a) => CT a -> IM a @-}
insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins x s)

ins xx E = T R xx E E
ins xx s@(T color y a b) | xx < y     = balance color y (ins xx a) b
                         | xx > y     = balance color y a (ins xx b)
                         | otherwise = s
{-
insert' :: (Ord a) => a -> RBSet a -> RBSet a                    
insert' x s = blacken' (ins' s)
  where
    ins' E = T R x E E
    ins' s@(T color y a b) | x < y     = balance color y (ins' a) b
                         | x > y     = balance color y a (ins' b)
                         | otherwise = s                  
-}
isBB :: RBSet a -> Bool
isBB EE = True
isBB (T BB _ _ _) = True
isBB _ = False

blacker :: Color -> Color
blacker NB = R
blacker R = B
blacker B = BB
blacker BB = undefined --error "too black"

redder :: Color -> Color
redder NB = undefined --error "not black enough"
redder R = NB
redder B = R
redder BB = B

redder' :: RBSet a -> RBSet a
redder' EE = E
redder' (T c l x r) = T (redder c) l x r 

{-@ bubble :: c:Color -> x:a -> l:RBSL a x -> r:RBSR a x -> v:RBSet a @-}
bubble :: Color -> a -> RBSet a -> RBSet a -> RBSet a
bubble color x l r
 | isBB(l) || isBB(r) = balance (blacker color) x (redder' l) (redder' r)
 | otherwise          = balance color x l r 
 
 -- `balance` rotates away coloring conflicts:
{-{-@ balance :: c:Color 
            -> {l:RBSet a | (prop_IM l) || (prop_CT l) } 
            -> x:a 
            -> {r:RBSet a | ((prop_IM l && prop_CT r) ||
                             (prop_CT l && prop_IM r)) 
                         && (blackHeightL l == blackHeightL r)
                         && prop_BST' (T c l x r) } 
            -> {v:RBSet a | (prop_CT v) 
                         && (blackHeightL v == (blackHeightL l + colorValue c))} 
@-}-}
{-@ balance :: c:Color -> x:a -> l:RBSL a x -> r:RBSR a x -> v:RBSet a @-}
-- beware beware blackHeight still dont accept NB
balance :: Color -> a -> RBSet a  -> RBSet a -> RBSet a
{-
 -- Okasaki's original cases:
balance B z (T R y (T R x a b) c) d = T R y (T B x a b) (T B z c d)
balance B z (T R x a (T R y b c)) d = T R y (T B x a b) (T B z c d)
balance B x a (T R z (T R y b c) d) = T R y (T B x a b) (T B z c d)
balance B x a (T R y b (T R z c d)) = T R y (T B x a b) (T B z c d)

 -- Six cases for deletion:
balance BB z (T R y (T R x a b) c) d = T R y (T B x a b) (T B z c d)
balance BB z (T R x a (T R y b c)) d = T R y (T B x a b) (T B z c d)
balance BB x a (T R z (T R y b c) d) = T R y (T B x a b) (T B z c d)
balance BB x a (T R y b (T R z c d)) = T R y (T B x a b) (T B z c d)

balance BB x a (T NB z (T B y b c) d@(T B _ _ _)) 
    = T B y (T B x a b) (balance B z c (redden d))
balance BB z (T NB x a@(T B _ _ _) (T B y b c)) d
    = T B y (balance B x (redden a) b) (T B z c d)
-}
balance color x a b = T color x a b 

