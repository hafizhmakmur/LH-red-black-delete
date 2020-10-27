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

{-@ xxx :: {x:RBSet a | prop_CT x} -> {v:RBSet a | not emptyTree v} @-}
xxx :: RBSet a -> RBSet a
xxx (T R E x E) = T R E x E 
xxx (T B E x E) = T B E x E
xxx (T B E x (T R a y b)) = T B a x b 
xxx (T B (T R a y b) x E) = T B a x b
{- Cases that should not have been reached if validBlackHeight
xxx (T R E x _) = E
xxx (T R _ x E) = E 
xxx (T B E x (T B a y b)) = E 
xxx (T B (T B a y b) x E) = E
-}
xxx (T color l y r) = l

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB
                            
{-@ measure emptyTree @-}
emptyTree :: RBSet a -> Bool
emptyTree E = True
emptyTree EE = True
emptyTree _ = False

--{-@ measure blackRoot @-}
{-@ inline blackRoot @-}
blackRoot :: RBSet a -> Bool
--blackRoot E = True
--blackRoot EE = False
--blackRoot (T c _ _ _) = c == B
blackRoot t = color' t == B

{-@ measure noSpecialColor @-}
noSpecialColor :: RBSet a -> Bool
noSpecialColor E = True
noSpecialColor EE = False
noSpecialColor (T c a _ b) = c /= BB &&
                             c /= NB &&
                             noSpecialColor a &&
                             noSpecialColor b
        
{-@ measure noSpecialChild @-}
noSpecialChild :: RBSet a -> Bool
noSpecialChild E = True
noSpecialChild EE = True
noSpecialChild (T _ l _ r) = noSpecialColor l && noSpecialColor r

{-@ measure redChildIsBlack @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T B a x b) = redChildIsBlack a && redChildIsBlack b
redChildIsBlack _ = False


{-@ blackHeightL :: {x:RBSet a | noSpecialColor x} -> { i : Int | i >= 1}  @-}
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
     
{-@ measure validBlackHeight @-}
{-@ validBlackHeight :: {x:RBSet a | noSpecialColor x} -> Bool @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight (T _ l _ r) = validBlackHeight l && validBlackHeight r
                            && blackHeightL l == blackHeightL r           
                            
{-@ inline prop_CT @-}
{-@ prop_CT :: {x:RBSet a | noSpecialColor x} -> Bool @-}
prop_CT :: RBSet a -> Bool
prop_CT t = noSpecialColor t && 
            redChildIsBlack t &&
            validBlackHeight t

{-@ inline prop_RBSet @-}
{-@ prop_RBSet :: {x:RBSet a | noSpecialColor x} -> Bool @-}
prop_RBSet :: RBSet a -> Bool
prop_RBSet t = prop_CT t &&
               blackRoot t
               
{-@ measure prop_IM @-}
{-@ prop_IM :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_IM E = True
prop_IM EE = True
prop_IM t@(T c l x r) = prop_CT l && prop_CT r
                     && blackHeightL l == blackHeightL r

{-@ measure prop_DT @-}
{-@ prop_DT :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_DT E = True
prop_DT EE = True
prop_DT t@(T c l x r) = prop_CT l && prop_CT r
                     && blackHeightL l == blackHeightL r

{-@ measure prop_IR @-}
{-@ prop_IR :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_IR E = False
prop_IR EE = False
prop_IR t@(T c l x r) = prop_CT l && prop_CT r
                     && blackHeightL l == blackHeightL r
