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
 | T Color (RBSet a) a (RBSet a)
 deriving (Show, Eq)

{-@ data RBSet a = 
    E 
  | EE 
  | T { c    :: Color, 
        l    :: RBSet a, 
        val  :: a, 
        r    :: RBSet a } @-}
 
{-@ measure aux @-}
aux :: Ord a => RBSet a -> [a] -> Bool
--aux E acc = acc
--aux (T _ a x b) acc = aux a (x : aux b acc)
--aux _ acc = acc
aux E x = True
aux EE x = True
aux _ x = False

--{-@ measure isBB @-}
{-@ isBB :: rb : RBSet a -> { b : Bool | b <=> isBB' rb } @-}
isBB :: RBSet a -> Bool
isBB EE = True
isBB (T BB _ _ _) = True
isBB _ = False

{-@ measure isBB' @-}
isBB' :: RBSet a -> Bool
isBB' EE = True
isBB' (T c _ _ _) = c == BB
isBB' _ = False

{-      
{-@ inline elements @-}
elements :: Ord a => RBSet a -> [a]
elements t = aux t [] 
      
{-@ inline prop_BST @-}
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

{-@ inline isSortedNoDups @-}
isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub' (sort x) == x
-}

{-@ measure isSortedNoDups' @-}
isSortedNoDups' :: Ord a => [a] -> Bool
isSortedNoDups' [] = True
isSortedNoDups' [x] = True
isSortedNoDups' (x:y:xs) = x < y && isSortedNoDups' (y:xs)
      
{-@ inline prop_BST' @-}
prop_BST' :: RBSet Int -> Bool
prop_BST' t = isSortedNoDups' (elements' t)

{-@ inline elements' @-}
elements' :: Ord a => RBSet a -> [a]
elements' t = undefined --aux t [] 

--aa
