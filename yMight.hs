-- Implementation of deletion for red black trees by Matt Might

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf
-- Draft paper:
--   http://matt.might.net/tmp/red-black-pearl.pdf

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

-- Helper functions for verification

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ measure emptyTree @-}
emptyTree :: RBSet a -> Bool
emptyTree E = True
emptyTree EE = True
emptyTree _ = False
{-
{-@ measure isBlack @-}
isBlack :: RBSet a -> Bool
isBlack E = True
isBlack EE = True
isBlack (T c _ _ _) = c == B || c == BB
--isBlack x = color x == B || color x == BB

{-@ inline blackChildOfRed @-}
blackChildOfRed :: RBSet a -> Color -> Bool
blackChildOfRed s c = if (c == R || c == NB) then isBlack s else True

{-@ measure countBHeight @-}
countBHeight :: RBSet a -> Int
countBHeight E = 1
countBHeight EE = 2
countBHeight (T c l _ r) = countBHeight l
                           + if c == B then 1 else 
                             if c == BB then 2 else 
                             if c == NB then -1 else 0

{-@ measure isValid @-}
isValid :: RBSet a -> Bool
isValid E = True
isValid EE = False
isValid (T c l _ r) = isValid l && isValid r
                     && blackChildOfRed l c
                     && blackChildOfRed r c
                     && (countBHeight l == countBHeight r)
-}
{-@ measure isBB' @-}
isBB' :: RBSet a -> Bool
isBB' EE = True
isBB' (T c _ _ _) = c == BB
isBB' _ = False

{-@ measure tooBlack @-}
tooBlack :: Color -> Bool
tooBlack BB = True

{-@ measure tooRed @-}
tooRed :: Color -> Bool
tooRed NB = True

{-@ measure canBeBlacker @-}
canBeBlacker :: RBSet a -> Bool
canBeBlacker E = True
canBeBlacker EE = False
canBeBlacker (T c l x r) = not (tooBlack c)
-- canBeBlacker x = color x /= BB

{-@ measure canBeRedder @-}
canBeRedder :: RBSet a -> Bool
canBeRedder E = False
canBeRedder EE = True
canBeRedder (T c l x r) = not (tooRed c)

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B
color' EE = BB

{-@ measure prop_BST' @-}
prop_BST' :: (Ord a) => RBSet a -> Bool
prop_BST' E = True
prop_BST' EE = True
prop_BST' (T _ E x E) = True
prop_BST' (T _ l@(T _ _ xl _) x E) = prop_BST' l && xl < x
prop_BST' (T _ E x r@(T _ _ xr _)) = prop_BST' r && x < xr
prop_BST' (T c l x r) = prop_BST' (T c l x E) && prop_BST' (T c E x r)

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
                             
{-@ measure redChildIsBlack @-}
--{-@ redChildIsBlack :: {x:RBSet a | noSpecialColor x}  -> Bool @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T B a x b) = redChildIsBlack a && redChildIsBlack b
redChildIsBlack _ = False

{-@ measure blackHeight @-}
blackHeight :: RBSet a -> Int
blackHeight E = 1
blackHeight EE = 2
blackHeight (T c l _ r) = blackHeight l
                          + if c == B then 1 else 
                            if c == BB then 2 else 
                            if c == NB then -1 else 0
                             
{-@ inline prop_CT @-}
--{-@ prop_CT :: {x:RBSet a | noSpecialColor x} -> Bool @-}
prop_CT :: RBSet a -> Bool
prop_CT t = noSpecialColor t && 
            redChildIsBlack t
            
{-@ inline prop_RBSet @-}
prop_RBSet :: RBSet a -> Bool
prop_RBSet t = prop_CT t &&
               blackRoot t
            
--{-@ inline prop_IR @-}
{-@ measure prop_IR @-}
prop_IR E = False
prop_IR EE = False
prop_IR (T c l x r) = prop_CT l && prop_CT r

--{-@ inline prop_DT @-}
{-@ measure prop_DT @-}
prop_DT E = True
prop_DT EE = True
prop_DT (T c l x r) = prop_CT l && prop_CT r

 -- Private auxiliary functions --
 
{-@ redden :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_DT v} @-}
redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

--{-@ blacken' :: {x:RBSet a | prop_BST' x} -> {v:RBSet a | prop_BST' v} @-}    
--{-@ blacken' :: x:RBSet a -> {v:RBSet a | blackRoot v} @-}    
{-@ blacken' :: {x:RBSet a | prop_IR x} -> {v:RBSet a | prop_RBSet v} @-}    
-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R a x b) = T B a x b
blacken' (T B a x b) = T B a x b

-- blacken for delete
-- root is never red, could be double black
--{-@ blacken :: x:RBSet a -> {v:RBSet a | blackRoot v} @-}  
{-@ blacken :: {x:RBSet a | prop_DT x} -> {v:RBSet a | prop_RBSet v} @-}    
blacken :: RBSet a -> RBSet a
blacken (T B a x b) = T B a x b
blacken (T BB a x b) = T B a x b
blacken E = E
blacken EE = E

{-@ isBB :: rb : RBSet a -> { b : Bool | b <=> isBB' rb } @-}
isBB :: RBSet a -> Bool
isBB EE = True
isBB (T BB _ _ _) = True
isBB _ = False

{-@ blacker :: {x:Color | not tooBlack x} -> Color @-}
blacker :: Color -> Color
blacker NB = R
blacker R = B
blacker B = BB
blacker BB = error "too black"

{-@ redder :: {x:Color | not tooRed x} -> Color @-}
redder :: Color -> Color
redder NB = error "not black enough"
redder R = NB
redder B = R
redder BB = B

{-@ blacker' :: {x:RBSet a | canBeBlacker x} -> RBSet a @-}
blacker' :: RBSet a -> RBSet a
blacker' E = EE
blacker' (T c l x r) = T (blacker c) l x r

{-@ redder' :: {x:RBSet a | canBeRedder x} -> RBSet a @-}
redder' :: RBSet a -> RBSet a
redder' EE = E
redder' (T c l x r) = T (redder c) l x r 

 -- `balance` rotates away coloring conflicts:
{-@ balance :: c:Color 
            -> {l:RBSet a | prop_CT l || prop_IR l || prop_DT l} 
            -> a 
            -> {r:RBSet a | if (prop_CT l) then ((prop_DT r) || (prop_IR r)) else (prop_CT r) }
            -> v:RBSet a @-}
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

 -- `bubble` "bubbles" double-blackness upward:
{-{-@ bubble :: c:Color -> l:RBSet a -> a -> {r:RBSet a | 
                                                if (isBB' l || isBB' r) then 
                                                    (not tooBlack c) && 
                                                    (canBeRedder l) && 
                                                    (canBeRedder r) 
                                                    else True} 
                                        -> RBSet a @-} -}
{-@ bubble :: c:Color
           -> {l:RBSet a | prop_CT l || prop_DT l}
           -> a
           -> {r:RBSet a | if (prop_CT l) then (prop_DT r) else (prop_CT r) }
           -> {v:RBSet a | prop_DT v} @-}
bubble :: Color -> RBSet a -> a -> RBSet a -> RBSet a
bubble color l x r
 | isBB(l) || isBB(r) = balance (blacker color) (redder' l) x (redder' r)
 | otherwise          = balance color l x r




 -- Public operations --

empty :: RBSet a
empty = E


member :: (Ord a) => a -> RBSet a -> Bool
member x E = False
member x (T _ l y r) | x < y     = member x l
                     | x > y     = member x r
                     | otherwise = True


--{-@ insert :: (Ord a) => a -> {x:RBSet a | prop_BST' x} -> {v:RBSet a | prop_BST' v} @-}    
--{-@ insert :: (Ord a) => a -> {x:RBSet a | blackRoot x && prop_Rb4' x} -> {v:RBSet a | blackRoot v && prop_Rb4' v} @-}  
{-@ insert :: (Ord a) => a -> {x:RBSet a | prop_RBSet x} -> {v:RBSet a | prop_RBSet v} @-}  
{-@ ins :: (Ord a) => {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_IR v} @-}
insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins s) 
 where ins E = T R E x E
       ins s@(T color a y b) | x < y     = balance color (ins a) y b
                             | x > y     = balance color a y (ins b)
                             | otherwise = s
                             
{-@ max :: {x:RBSet a | not emptyTree x && prop_CT x} -> a @-}
max :: RBSet a -> a
max E = error "no largest element"
max (T _ _ x E) = x
max (T _ _ x r) = max r

-- Remove this node: it might leave behind a double black node
{-@ remove :: {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_DT v} @-}
remove :: RBSet a -> RBSet a
-- remove E = E   -- impossible!
-- ; Leaves are easiest to kill:
remove (T R E _ E) = E
remove (T B E _ E) = EE
-- ; Killing a node with one child;
-- ; parent or child is red:
-- remove (T R E _ child) = child
-- remove (T R child _ E) = child
remove (T B E _ (T R a x b)) = T B a x b
remove (T B (T R a x b) _ E) = T B a x b
-- ; Killing a black node with one black child:
-- remove (T B E _ child@(T B _ _ _)) = blacker' child
-- remove (T B child@(T B _ _ _) _ E) = blacker' child
-- ; Killing a node with two sub-trees:
remove (T color l y r) = bubble color l' mx r 
 where mx = max l
       l' = removeMax l

{-@ removeMax :: {x:RBSet a | not emptyTree x && prop_CT x} -> {v:RBSet a | prop_DT v} @-}
removeMax :: RBSet a -> RBSet a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ _ E) = remove s
removeMax s@(T color l x r) = bubble color l x (removeMax r)

--{-@ delete :: (Ord a) => a -> {x:RBSet a | isValid x} -> {v:RBSet a | isValid v} @-}    
--{-@ delete :: (Ord a) => a -> {x:RBSet a | blackRoot x} -> {v:RBSet a | blackRoot v} @-}   
{-@ delete :: (Ord a) => a -> {x:RBSet a | prop_RBSet x} -> {v:RBSet a | prop_RBSet v} @-}   
delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x s = blacken (del x s)

{-@ del :: Ord a => a -> {x:RBSet a | prop_CT x} -> {v:RBSet a | prop_DT v} @-}
del x E = E
del x s@(T color a' y b') | x < y   = bubble color (del x a') y b'
                        | x > y     = bubble color a' y (del x b')
                        | otherwise = remove s

prop_del :: Int -> RBSet Int -> Bool
prop_del x s = color (del x s) `elem` [B, BB]


--- Testing code      
elements :: Ord a => RBSet a -> [a]
elements t = aux t [] where
      aux E acc = acc
      aux (T _ a x b) acc = aux a (x : aux b acc)

instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = liftM (foldr @[] insert empty) arbitrary

{-@ prop_BST :: x:RBSet Int -> {v:Bool | v <=> prop_BST' x} @-}
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

{-@ color :: x:RBSet a -> {v:Color | v = color' x} @-}
color :: RBSet a -> Color
color (T c _ _ _) = c
color E = B
color EE = BB

{-@ prop_Rb2 :: x:RBSet Int -> {v:Bool | v <=> blackRoot x} @-}
prop_Rb2 :: RBSet Int -> Bool
prop_Rb2 t = color t == B

prop_Rb3 :: RBSet Int -> Bool
prop_Rb3 t = fst (aux t) where 
  aux E = (True, 0)
  aux (T c a x b) = (h1 == h2 && b1 && b2, if c == B then h1 + 1 else h1) where
      (b1 , h1) = aux a
      (b2 , h2) = aux b

{-@ prop_Rb4 :: x:RBSet Int  -> {v:Bool | v <=> redChildIsBlack x} @-}
prop_Rb4 :: RBSet Int  -> Bool
prop_Rb4 E = True
prop_Rb4 (T R a x b) = color a == B && color b == B && prop_Rb4 a && prop_Rb4 b
prop_Rb4 (T B a x b) = prop_Rb4 a && prop_Rb4 b

isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x
              
--{-@ prop_delete_spec1 :: {x:RBSet Int | blackRoot x} -> Bool @-}
prop_delete_spec1 :: RBSet Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)
     
prop_delete_spec2 :: RBSet Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
   allpairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete_spec3 :: RBSet Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)
     
prop_delete_bst :: RBSet Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

prop_delete2 :: RBSet Int -> Bool
prop_delete2 t = all (\x -> prop_Rb2 (delete x t)) (elements t)

prop_delete3 :: RBSet Int -> Bool
prop_delete3 t = all (\x -> prop_Rb3 (delete x t)) (elements t)

prop_delete4 :: RBSet Int -> Bool
prop_delete4 t = all (\x -> prop_Rb4 (delete x t)) (elements t)

check_insert = do
    putStrLn "BST property"
    quickCheck prop_BST
    putStrLn "Root is black"
    quickCheck prop_Rb2
    putStrLn "Black height the same"
    quickCheck prop_Rb3
    putStrLn "Red nodes have black children"
    quickCheck prop_Rb4

check_delete = do
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec1
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec2
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec3
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete2
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete3
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete4
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_bst
       

main :: IO ()
main = 
 do
 return $! ()
