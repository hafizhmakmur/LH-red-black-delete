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

{-@ inline canBeBubbled @-}
canBeBubbled :: Color -> RBSet a -> RBSet a -> Bool
canBeBubbled c l r = 
    if (isBB' l) || (isBB' r) then
        (not (tooBlack c)) &&
        (canBeRedder l) &&
        (canBeRedder r)
    else True
    
{-@ bbb :: {x:RBSet a | prop_CT x} -> RBSet a @-}
bbb :: RBSet a -> RBSet a
bbb t@(T c l x r) = ccc c l r
 
{-@ bbb' :: {x:RBSet a | prop_CT x} -> RBSet a @-}
bbb' :: RBSet a -> RBSet a
bbb' t@(T c l x r) = ddd c l r

{-@ ccc :: c:Color -> l:RBSet a -> {r:RBSet a | canBeBubbled c l r} -> RBSet a @-}
ccc :: Color -> RBSet a -> RBSet a -> RBSet a
ccc c l r = E

{-@ ddd :: c:Color -> {l:RBSet a | not (isBB' l)} -> {r:RBSet a | not (isBB' r)} -> RBSet a @-}
ddd :: Color -> RBSet a -> RBSet a -> RBSet a
ddd c l r = ccc c l r

{-@ eee :: {x:RBSet a | noSpecialColor x} -> {v:RBSet a | isBB' v} @-}
eee :: RBSet a -> RBSet a
eee t = t

{-@ measure isBB' @-}
isBB' :: RBSet a -> Bool
isBB' EE = True
isBB' (T c _ _ _) = c == BB
isBB' _ = False

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB

{-@ measure noSpecialColor @-}
{-@ noSpecialColor :: x:RBSet a -> {v:Bool | (v => noSpecialChild x) && (v => not (isBB' x))} @-}
{-@ invariant {t:RBSet a | noSpecialColor t => noSpecialChild t} @-} 
{-@ invariant {t:RBSet a | noSpecialColor t => isBB' t} @-} 
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

{-@ invariant {t:RBSet a | noSpecialColor t => noSpecialChild t} @-} 
--{-@ invariant {t:RBSet a | prop_CT t => prop_IM t} @-} 

{-@ measure redChildIsBlack @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack EE = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T _ a x b) = redChildIsBlack a && redChildIsBlack b

{-@ measure blackHeightL @-}
{-@ blackHeightL :: {x:RBSet a | noSpecialColor x} -> { i : Int | i >= 1}  @-}
blackHeightL :: RBSet a -> Int
blackHeightL E = 1
blackHeightL EE = 2
blackHeightL (T c l _ r) = blackHeightL l
                          + if c == B then 1 else 
                            if c == BB then 2 else 
                            if c == NB then -1 else 0

{-@ measure blackHeightR @-}
{-@ blackHeightR :: {x:RBSet a | noSpecialColor x} -> { i : Int | i >= 1}  @-}
blackHeightR :: RBSet a -> Int
blackHeightR E = 1
blackHeightR EE = 2
blackHeightR (T c l _ r) = blackHeightR r
                          + if c == B then 1 else 
                            if c == BB then 2 else 
                            if c == NB then -1 else 0
     
{-@ measure validBlackHeight @-}
{-@ validBlackHeight :: {x:RBSet a | noSpecialChild x} -> Bool @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight EE = True
validBlackHeight (T _ l _ r) = validBlackHeight l && validBlackHeight r
                            && blackHeightL l == blackHeightL r           
                            
{-@ inline prop_CT @-}
{-@ prop_CT :: {x:RBSet a | noSpecialColor x} -> {v:Bool | v => prop_IM x} @-}
prop_CT :: RBSet a -> Bool
prop_CT t = noSpecialColor t 
         && redChildIsBlack t 
         && validBlackHeight t
 
{-@ measure prop_IM @-}
{-@ prop_IM :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_IM E = True
prop_IM EE = True
prop_IM t@(T _ l _ r) = prop_CT l && prop_CT r
                      && blackHeightL l == blackHeightL r
                      
{-@ measure tooBlack @-}
tooBlack :: Color -> Bool
tooBlack BB = True
tooBlack _ = False

{-@ measure tooRed @-}
tooRed :: Color -> Bool
tooRed NB = True
tooRed _ = False

{-@ measure canBeRedder @-}
canBeRedder :: RBSet a -> Bool
canBeRedder E = False
canBeRedder EE = True
canBeRedder (T c l x r) = not (tooRed c)

