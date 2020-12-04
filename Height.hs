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

-- Helper functions for verification

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

 -- `balance` rotates away coloring conflicts:
{-@ balance :: c:Color 
            -> x:a 
            -> {l:RBSL a x | (prop_IM l) || (prop_CT l) } 
            -> {r:RBSR a x | ((prop_IM l && prop_CT r) ||
                              (prop_CT l && prop_IM r)) 
                          && (blackHeightL l == blackHeightL r) } 
            -> {v:RBSet a | ((c /= B && prop_IM v) || prop_CT v) 
                         && (blackHeightL v == (blackHeightL l + colorValue c))} 
@-} 
balance :: Color -> a -> RBSet a -> RBSet a -> RBSet a

 -- Okasaki's original cases:
balance B z (T R y (T R x a b) c) d = T R y (T B x a b) (T B z c d)
balance B z (T R x a (T R y b c)) d = T R y (T B x a b) (T B z c d)
balance B x a (T R z (T R y b c) d) = T R y (T B x a b) (T B z c d)
balance B x a (T R y b (T R z c d)) = T R y (T B x a b) (T B z c d)
{-
 -- Six cases for deletion:
balance BB z (T R y (T R x a b) c) d = T B y (T B x a b) (T B z c d)
balance BB z (T R x a (T R y b c)) d = T B y (T B x a b) (T B z c d)
balance BB x a (T R z (T R y b c) d) = T B y (T B x a b) (T B z c d)
balance BB x a (T R y b (T R z c d)) = T B y (T B x a b) (T B z c d)

balance BB x a (T NB z (T B y b c) d@(T B _ _ _)) 
    = T B y (T B x a b) (balance B z c (redden d))
balance BB z (T NB x a@(T B _ _ _) (T B y b c)) d   -- problematic lines??
    = T B y (balance B x (redden a) b) (T B z c d) 
-}

balance color x a@(T R _ (T B _ _ _) (T B _ _ _)) 
                b@(T R _ (T B _ _ _) (T B _ _ _)) = T color x a b  
balance color x a@(T R _ (T B _ _ _) (T B _ _ _)) 
                b@(T B _ _ _) = T color x a b
balance color x a@(T R _ (T B _ _ _) (T B _ _ _))  
                b@E = error "Height invariant prevents this" -- It never happens!!! 

balance color x a@(T B _ _ _) 
                b@(T R _ (T B _ _ _) (T B _ _ _)) = T color x a b  
balance color x a@(T B _ _ _) 
                b@(T B _ _ _) = T color x a b
balance color x a@(T B _ _ _)  
                b@E = error "Height invariant prevents this" -- It never happens!!! 

balance color x a@E 
                b@(T R _ (T B _ _ _) (T B _ _ _)) = error "Height invariant prevents this" -- It never happens!!! 
balance color x a@E 
                b@(T B _ _ _) = error "Height invariant prevents this" -- It never happens!!! 
balance color x a@E  
                b@E = T color x a b 

balance color x a b = T color x a b 

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB
                            
{-@ measure normalLeaf @-}
normalLeaf :: RBSet a -> Bool
normalLeaf E = True
normalLeaf _ = False

{-@ inline blackRoot @-}
blackRoot :: RBSet a -> Bool
blackRoot t = color' t == B

{-@ inline noSpecialColor @-}
{-@ noSpecialColor :: x:RBSet a -> {v:Bool | (v => noSpecialChild x) 
                                          && (v => not (isBB' x)) } 
  @-}
noSpecialColor :: RBSet a -> Bool
noSpecialColor t = (color' t /= BB) 
                && (color' t /= NB)
                && noSpecialChild t

{-@ measure noSpecialChild @-}
noSpecialChild :: RBSet a -> Bool
noSpecialChild (T _ _ l r) = noSpecialColor l && noSpecialColor r
noSpecialChild _ = True

{-@ measure redChildIsBlack @-}
{-@ redChildIsBlack :: x:RBSet a 
                    -> {v:Bool | (v => redChildIsBlackNT x)
                              && (((color' x == B) && (redChildIsBlackNT x))
                                  => v)} @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack EE = True
redChildIsBlack (T R _ l r) = color' l == B 
                           && color' r == B 
                           && redChildIsBlack l && redChildIsBlack r
redChildIsBlack (T _ _ l r) = redChildIsBlack l && redChildIsBlack r

{-@ measure redChildIsBlackNT @-}
redChildIsBlackNT :: RBSet a  -> Bool
redChildIsBlackNT (T _ _ l r) = redChildIsBlack l && redChildIsBlack r
redChildIsBlackNT _ = True

{-@ measure colorValue @-}
colorValue :: Color -> Int
colorValue NB = -1
colorValue R = 0
colorValue B = 1
colorValue BB = 2

{-@ measure blackHeightL @-}
{-@ blackHeightL :: {x:RBSet a | noSpecialColor x} -> { i : Int | i >= 1}  @-}
blackHeightL :: RBSet a -> Int
blackHeightL (T c _ l _) = blackHeightL l + colorValue c
blackHeightL t = colorValue $ color' t

{-@ measure validBlackHeight @-}
{-@ validBlackHeight :: {x:RBSet a | noSpecialChild x} -> Bool @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight EE = True
validBlackHeight (T _ _ l r) = validBlackHeight l && validBlackHeight r
                            && blackHeightL l == blackHeightL r           
                            
{-@ inline prop_CT @-}
{-@ prop_CT :: {x:RBSet a | noSpecialColor x} 
            -> {v:Bool | (v => prop_IM x) 
                      && (((color' x == B) && prop_IM x) => v)} @-}
{-@ invariant {t:RBSet a | prop_CT t => prop_IM t} @-} 
prop_CT :: (Ord a) => RBSet a -> Bool
prop_CT t = noSpecialColor t 
         && redChildIsBlack t 
         && validBlackHeight t
{-@ type CT a = {v:RBSet a | prop_CT v} @-}

{-@ inline prop_RBSet @-}
{-@ prop_RBSet :: {x:RBSet a | noSpecialColor x} 
               -> {v:Bool | v => prop_CT x} @-}
prop_RBSet :: (Ord a) => RBSet a -> Bool
prop_RBSet t = prop_CT t 
            && blackRoot t
{-@ type RT a = {v:RBSet a | prop_RBSet v} @-}
        
{-@ inline prop_IM @-}
{-@ prop_IM :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_IM t = noSpecialChild t 
         && redChildIsBlackNT t 
         && validBlackHeight t
{-@ type IM a = {v:RBSet a | prop_IM v} @-}

{-@ measure tooBlack @-}
tooBlack :: Color -> Bool
tooBlack BB = True
tooBlack _ = False

{-@ measure tooRed @-}
tooRed :: Color -> Bool
tooRed NB = True
tooRed _ = False

{-@ inline canBeBlacker @-}
canBeBlacker x = color' x /= BB

{-@ inline isBB' @-}
isBB' t = color' t == BB

 -- Private auxiliary functions --

{-@ redden :: {x:CT a | color' x == B} 
           -> {v:IM a | blackHeightL v == (blackHeightL x - 1) } @-}
redden :: RBSet a -> RBSet a
redden (T _ x a b) = T R x a b

