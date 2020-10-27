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
 
{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB

 {-@ inline blackRoot @-}
blackRoot :: RBSet a -> Bool
blackRoot t = color' t == B

{-@ measure noSpecialColor @-}
noSpecialColor :: RBSet a -> Bool
noSpecialColor E = True
noSpecialColor EE = False
noSpecialColor (T c a _ b) = c /= BB &&
                             c /= NB &&
                             noSpecialColor a &&
                             noSpecialColor b
                             
{-@ measure redChildIsBlack @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T B a x b) = redChildIsBlack a && redChildIsBlack b
redChildIsBlack _ = False

{-@ inline prop_CT @-}
prop_CT :: RBSet a -> Bool
prop_CT t = noSpecialColor t && 
            redChildIsBlack t

{-@ inline prop_RBSet @-}
prop_RBSet :: RBSet a -> Bool
prop_RBSet t = prop_CT t &&
               blackRoot t

{-@ measure prop_IM @-}
prop_IM E = True
prop_IM EE = True
prop_IM (T c l x r) = prop_CT l && prop_CT r

{-@ aaa :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IM v} @-}
aaa E = E
aaa t@(T _ l _ r) = t
                  
{-@ bbb :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IM v} @-}
bbb E = E
bbb t@(T _ l _ r) = xxx (bbb l) r -- IM CT

{-@ ccc :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IM v} @-}
ccc E = E
ccc t@(T _ l _ r) = xxx l (ccc r) -- CT IM

{-@ xxx :: {l:RBSet a | (prop_CT l) || (prop_IM l)} 
        -> {r:RBSet a | ((prop_CT l) && (prop_IM r)) || 
                        ((prop_IM l) && (prop_CT r))  }
        -> {v:RBSet a | prop_IM v} @-}
xxx :: RBSet a -> RBSet a -> RBSet a
xxx a b = E


{-@ redden :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IM v} @-}
redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

{-@ blacken' :: {x:RBSet a | prop_IM x} -> {v:RBSet a | prop_RBSet v} @-}    
-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R a x b) = T B a x b
blacken' (T B a x b) = T B a x b

{-@ balance :: c:Color 
            -> {l:RBSet a | prop_CT l || prop_IM l} 
            -> a 
            -> {r:RBSet a | ((prop_CT l) && (prop_IM r)) || 
                            ((prop_IM l) && (prop_CT r))  }
            -> {v:RBSet a | prop_IM v} @-}
balance :: Color -> RBSet a -> a -> RBSet a -> RBSet a

 -- Okasaki's original cases:
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)

 -- Six cases for deletion:
balance BB (T R (T R a x b) y c) z d = T B (T B a x b) y (T B c z d)
balance BB (T R a x (T R b y c)) z d = T B (T B a x b) y (T B c z d)
balance BB a x (T R (T R b y c) z d) = T B (T B a x b) y (T B c z d)
balance BB a x (T R b y (T R c z d)) = T B (T B a x b) y (T B c z d)

balance BB a x (T NB (T B b y c) z d@(T B _ _ _)) 
    = T B (T B a x b) y (balance B c z (redden d))
balance BB (T NB a@(T B _ _ _) x (T B b y c)) z d
    = T B (balance B (redden a) x b) y (T B c z d)

balance color a x b = T color a x b

{-@ insert :: (Ord a) => a -> {x:RBSet a | prop_RBSet x} -> {v:RBSet a | prop_RBSet v} @-}  
{-@ ins :: (Ord a) => {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IM v} @-}
insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins s) 
 where ins E = T R E x E
       ins s@(T color a y b) | x < y     = balance color (ins a) y b
                             | x > y     = balance color a y (ins b)
                             | otherwise = s
            

