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
      
{-@ measure normalLeaf @-}
normalLeaf :: RBSet a -> Bool
normalLeaf E = True
normalLeaf _ = False

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB

{-@ measure noSpecialColor @-}
{-@ noSpecialColor :: x:RBSet a -> {v:Bool | (v => noSpecialChild x) 
                                    } 
                                                   @-}
{-@ invariant {t:RBSet a | noSpecialColor t => noSpecialChild t} @-} 
--{-@ invariant {t:RBSet a | noSpecialColor t => not (isBB' t)} @-} 
--{-@ invariant {t:RBSet a | (noSpecialColor t && not normalLeaf t) 
--                                            => canBeRedder t } @-} 
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
{-@ redChildIsBlack :: x:RBSet a -> {v:Bool | v => redChildIsBlackNT x} @-}
{-@ invariant {t:RBSet a | redChildIsBlack t => redChildIsBlackNT t} @-} 
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack EE = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T _ a x b) = redChildIsBlack a && redChildIsBlack b

{-@ measure redChildIsBlackNT @-}
redChildIsBlackNT :: RBSet a  -> Bool
redChildIsBlackNT E = True
redChildIsBlackNT EE = True
redChildIsBlackNT (T _ a x b) = redChildIsBlack a && redChildIsBlack b

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
{-@ invariant {t:RBSet a | prop_CT t => prop_IM t} @-} 
prop_CT :: RBSet a -> Bool
prop_CT t = noSpecialColor t 
         && redChildIsBlack t 
         && validBlackHeight t

{-@ inline prop_IM @-}
{-@ prop_IM :: {x:RBSet a | noSpecialChild x} -> Bool @-}
prop_IM t = noSpecialChild t 
          && redChildIsBlackNT t 
          && validBlackHeight t 
          
{-@ redden :: {x:RBSet a | prop_CT x && (color' x == B)} 
           -> {v:RBSet a | prop_IM v && (blackHeightL x == (blackHeightL v + 1)) } @-}
redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

{-
{-@ balance :: c:Color 
            -> {l:RBSet a | prop_CT l} 
            -> a 
            -> {r:RBSet a | prop_IM r && (blackHeightL l == blackHeightL r} 
            -> {v:RBSet a | validBlackHeight v} @-} 
-}
--{-@ balance :: c:Color -> {l:RBSet a | prop_IM l} -> a -> {r:RBSet a | prop_CT r} -> {v:RBSet a | prop_IM v} @-} 

{-@ balance :: c:Color 
            -> {l:RBSet a | (prop_IM l) || (prop_CT l) } 
            -> a 
            -> {r:RBSet a | ((prop_IM l && prop_CT r) ||
                             (prop_CT l && prop_IM r)) 
                         && (blackHeightL l == blackHeightL r) } 
            -> {v:RBSet a | prop_IM v} @-} 
-- beware beware blackHeight still dont accept NB
balance :: Color -> RBSet a -> a -> RBSet a -> RBSet a
{-
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
-}
balance BB a x (T NB (T B b y c) z d@(T B _ _ _)) 
    = T B (T B a x b) y (balance B c z (redden d))
--balance BB (T NB a@(T B _ _ _) x (T B b y c)) z d
--    = T B (balance B (redden a) x b) y (T B c z d)

--balance color a x b = T color a x b 
