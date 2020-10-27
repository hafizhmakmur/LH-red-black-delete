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

{-@ i :: x:a -> {v:RBSet a | redChildIsBlack v} @-}
i x = T R E x (T R E x E)
{-@ j :: {x:RBSet a | redChildIsBlack x} -> {v:Bool | v} @-}
j (T R E x (T _ E y E)) = False
{-@ k :: {x:RBSet a | redChildIsBlack x} -> {v:Bool | v} @-}
k E = False

{-@ l :: x:a -> {v:RBSet a | validBlackHeight v} @-}
l x = T R E x (T B E x E)
{-@ m :: {x:RBSet a | validBlackHeight x} -> {v:Bool | v} @-}
m (T R E x (T _ E y E)) = False
{-@ n :: {x:RBSet a | validBlackHeight x} -> {v:Bool | v} @-}
n E = False

{-@ p  :: x:a -> {v:RBSet a | redChildIsBlack v && validBlackHeight v} @-}
p  x = T R E x (T B E x E)
{-@ p' :: x:a -> {v:RBSet a | redChildIsBlack v && validBlackHeight v} @-}
p' x = T R E x (T R E x E)
{-@ q :: {x:RBSet a | redChildIsBlack x && validBlackHeight x} -> {v:Bool | v} @-}
q (T R E x (T _ E y E)) = False
{-@ r :: {x:RBSet a | redChildIsBlack x && validBlackHeight x} -> {v:Bool | v} @-}
r E = False

{-@ measure redChildIsBlack @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T B a x b) = redChildIsBlack a && redChildIsBlack b
redChildIsBlack _ = False

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB

{-@ measure validBlackHeight @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight EE = True
validBlackHeight (T _ l _ r) = validBlackHeight l && validBlackHeight r
                            && blackHeightL l == blackHeightL r
                            

{-@ measure blackHeightL @-}
blackHeightL :: RBSet a -> Int
blackHeightL E = 1
blackHeightL EE = 2
blackHeightL (T c l _ r) = blackHeightL l
                          + if c == B then 1 else 
                            if c == BB then 2 else 
                            if c == NB then -1 else 0

{-@ measure blackHeightR @-}
blackHeightR :: RBSet a -> Int
blackHeightR E = 1
blackHeightR EE = 2
blackHeightR (T c l _ r) = blackHeightR r
                          + if c == B then 1 else 
                            if c == BB then 2 else 
                            if c == NB then -1 else 0
{-@ measure noSpecialColor @-}
noSpecialColor :: RBSet a -> Bool
noSpecialColor E = True
noSpecialColor EE = False
noSpecialColor (T c a _ b) = c /= BB &&
                             c /= NB &&
                             noSpecialColor a &&
                             noSpecialColor b

{-@ measure emptyTree @-}
emptyTree :: RBSet a -> Bool
emptyTree E = True
emptyTree EE = True
emptyTree _ = False

{-@ xxx :: {x:RBSet a | noSpecialColor x} -> {v:RBSet a | not emptyTree v} @-}
--{-@ xxx :: x:RBSet a -> {v:RBSet a | not emptyTree v} @-}
xxx :: RBSet a -> RBSet a
--xxx E = E
--xxx EE = EE
{-
xxx (T R E x E) = T R E x E 
xxx (T B E x E) = T B E x E
xxx (T B E x (T R a y b)) = T B a x b
xxx (T B EE x (T R a y b)) = T B a x b 
xxx (T B (T R a x b) _ E) = T B a x b
xxx (T B (T R a x b) _ EE) = T B a x b
-}
xxx (T R E x _) = T R E x E
xxx (T B E x _) = T R E x E
xxx (T R _ x E) = T R E x E
xxx (T B _ x E) = T R E x E
--xxx (T _ EE x _) = T R E x E
--xxx (T _ _ x EE) = T R E x E
xxx (T color l y r) = l
            

