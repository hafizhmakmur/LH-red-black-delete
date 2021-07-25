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

 -- Private auxiliary functions --

{-@ redden :: {x:CT a | color x == B} 
           -> {v:IM a | blackHeightL v == (blackHeightL x - 1) } @-}
redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

{-@ blacken' :: IM a -> RT a @-}    
-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R a x b) = T B a x b
blacken' (T B a x b) = T B a x b

-- blacken for delete
-- root is never red, could be double black 
{-@ blacken :: IM a -> RT a @-}    
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

{-@ blacker :: {x:Color | not tooBlack x} 
            -> {v:Color | colorValue v == (colorValue x + 1)} @-}
blacker :: Color -> Color
blacker NB = R
blacker R = B
blacker B = BB
blacker BB = error "too black"

{-@ redder :: {x:Color | not tooRed x} 
           -> {v:Color | (colorValue v == (colorValue x - 1))
                      && ((x == BB) => (v == B)) } @-}
redder :: Color -> Color
redder NB = error "not black enough"
redder R = NB
redder B = R
redder BB = B

{-@ blacker' :: {x:RBSet a | not isBB' x} -> RBSet a @-}
blacker' :: RBSet a -> RBSet a
blacker' E = EE
blacker' (T c l x r) = T (blacker c) l x r

{-@ redder' :: {x:RBSet a | (prop_IM x && isBB' x) || (prop_CT x)} 
            -> {v:RBSet a | ((prop_IM x && isBB' x && prop_CT v) || 
                             (prop_CT x && prop_IM v))
                         && (blackHeightL v == (blackHeightL x - 1)) } @-}
redder' :: RBSet a -> RBSet a
redder' EE = E
redder' (T c l x r) = T (redder c) l x r 

 -- `balance` rotates away coloring conflicts:
{-@ balance :: c:Color 
            -> {l:RBSet a | (prop_IM l) || (prop_CT l) } 
            -> x:a 
            -> {r:RBSet a | ((prop_IM l && prop_CT r) ||
                             (prop_CT l && prop_IM r)) 
                         && (blackHeightL l == blackHeightL r)} 
            -> {v:RBSet a | ((c /= B && prop_IM v) || prop_CT v) 
                         && (blackHeightL v == (blackHeightL l + colorValue c))} 
@-}
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
{-@ bubble :: {c:Color | not (tooBlack c)}
           -> {l:RBSet a | prop_CT l || prop_IM l}
           -> x:a
           -> {r:RBSet a | ((prop_CT l && prop_IM r) || 
                            (prop_IM l && prop_CT r))
                        && (blackHeightL l == blackHeightL r) }
           -> {v:IM a | blackHeightL v == blackHeightL l + (colorValue c) } 
@-}
bubble :: Color -> RBSet a -> a -> RBSet a -> RBSet a
bubble color l x r
 | isBB(l) || isBB(r) = balance (blacker color) (redder' l) x (redder' r)
 | otherwise          = balance color l x r 




 -- Public operations --

{-@ empty :: {v:RT a | normalLeaf v} @-}
empty :: RBSet a
empty = E


{-@ member :: (Ord a) => a -> CT a -> Bool@-}
member :: (Ord a) => a -> RBSet a -> Bool
member x E = False
member x (T _ l y r) | x < y     = member x l
                     | x > y     = member x r
                     | otherwise = True

{-@ insert :: (Ord a) => a -> RT a -> RT a @-}
--{-@ ins :: (Ord a) => x:CT a -> {v:IM a | blackHeightL v == blackHeightL x} @-}
{-@ ins :: (Ord a) => x:IM a -> {v:IM a | blackHeightL v == blackHeightL x} @-}
insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins s) 
 where ins E = T R E x E
       ins s@(T color a y b) | x < y     = balance color (ins a) y b
                             | x > y     = balance color a y (ins b)
                             | otherwise = s
 


{-@ max :: {x:CT a | not normalLeaf x} -> a @-}
max :: RBSet a -> a
max E = error "no largest element"
max (T _ _ x E) = x
max (T _ _ x r) = max r

-- Remove this node: it might leave behind a double black node
{-@ remove :: {x:CT a | not normalLeaf x} 
           -> {v:IM a | blackHeightL v == blackHeightL x} @-}
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

{-@ removeMax :: {x:CT a | not normalLeaf x} 
              -> {v:IM a | blackHeightL v == blackHeightL x} @-}
removeMax :: RBSet a -> RBSet a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ _ E) = remove s
removeMax s@(T color l x r) = bubble color l x (removeMax r)

{-@ delete :: (Ord a) => a -> x:RT a -> v:RT a @-}   
delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x s = blacken (del x s)

{-@ del :: Ord a => a 
                 -> x:CT a 
                 -> {v:IM a | blackHeightL v == blackHeightL x} @-}
del x E = E
del x s@(T color a' y b') | x < y   = bubble color (del x a') y b'
                        | x > y     = bubble color a' y (del x b')
                        | otherwise = remove s

{-@ prop_del :: Int -> RT Int -> Bool @-}
prop_del :: Int -> RBSet Int -> Bool
prop_del x s = color (del x s) `elem` [B, BB]


--- Testing code

{-@ elements :: Ord a => RT a -> [a] @-}
elements :: Ord a => RBSet a -> [a]
elements t = aux t [] where
      aux E acc = acc
      aux (T _ a x b) acc = aux a (x : aux b acc)

instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = liftM (foldr @[] insert empty) arbitrary

{-@ prop_BST :: x:RT Int -> {v:Bool | v <=> prop_BST' x} @-}
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

color :: RBSet a -> Color
color (T c _ _ _) = c
color E = B
color EE = BB

{-@ prop_Rb2 :: x:RT Int -> {v:Bool | v <=> blackRoot x} @-}
prop_Rb2 :: RBSet Int -> Bool
prop_Rb2 t = color t == B

{-@ prop_Rb3 :: x:RT Int -> {v:Bool | v <=> validBlackHeight x} @-}
prop_Rb3 :: RBSet Int -> Bool
prop_Rb3 t = fst (aux t) where 
  aux E = (True, 0)
  aux (T c a x b) = (h1 == h2 && b1 && b2, if c == B then h1 + 1 else h1) where
      (b1 , h1) = aux a
      (b2 , h2) = aux b

{-@ prop_Rb4 :: x:RBSet Int -> {v:Bool | v <=> redChildIsBlack x} @-}
prop_Rb4 :: RBSet Int  -> Bool
prop_Rb4 E = True
prop_Rb4 (T R a x b) = color a == B && color b == B && prop_Rb4 a && prop_Rb4 b
prop_Rb4 (T B a x b) = prop_Rb4 a && prop_Rb4 b


isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x
              

{-@ prop_delete_spec1 :: RT Int -> Bool @-}
prop_delete_spec1 :: RBSet Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

{-@ prop_delete_spec2 :: RT Int -> Bool @-}
prop_delete_spec2 :: RBSet Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
   allpairs = [ (x,y) | x <- elements t, y <- elements t ]

{-@ prop_delete_spec3 :: RT Int -> Int -> Property @-}
prop_delete_spec3 :: RBSet Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)

{-@ prop_delete_bst :: RT Int -> Bool @-}
prop_delete_bst :: RBSet Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

{-@ prop_delete2 :: RT Int -> Bool @-}
prop_delete2 :: RBSet Int -> Bool
prop_delete2 t = all (\x -> prop_Rb2 (delete x t)) (elements t)

{-@ prop_delete3 :: RT Int -> Bool @-}
prop_delete3 :: RBSet Int -> Bool
prop_delete3 t = all (\x -> prop_Rb3 (delete x t)) (elements t)

{-@ prop_delete4 :: RT Int -> Bool @-}
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

-- Helper functions for verification

{-@ measure color @-}
                        
{-@ measure normalLeaf @-}
normalLeaf :: RBSet a -> Bool
normalLeaf E = True
normalLeaf _ = False

{-@ inline blackRoot @-}
blackRoot :: RBSet a -> Bool
blackRoot t = color t == B

{-@ inline noSpecialColor @-}
{-@ noSpecialColor :: x:RBSet a -> {v:Bool | (v => noSpecialChild x) 
                                          && (v => not (isBB' x)) } 
  @-}
noSpecialColor :: RBSet a -> Bool
noSpecialColor t = (color t /= BB) 
                && (color t /= NB)
                && noSpecialChild t

{-@ measure noSpecialChild @-}
noSpecialChild :: RBSet a -> Bool
noSpecialChild (T _ l _ r) = noSpecialColor l && noSpecialColor r
noSpecialChild _ = True

{-@ measure redChildIsBlack @-}
{-@ redChildIsBlack :: x:RBSet a -> {v:Bool | v => redChildIsBlackNT x} @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack EE = True
redChildIsBlack (T R a x b) = color a == B && 
                              color b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T _ a x b) = redChildIsBlack a && redChildIsBlack b

{-@ measure redChildIsBlackNT @-}
redChildIsBlackNT :: RBSet a  -> Bool
redChildIsBlackNT (T _ l _ r) = redChildIsBlack l && redChildIsBlack r
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
blackHeightL (T c l _ _) = blackHeightL l + colorValue c
blackHeightL t = colorValue $ color t

{-@ measure validBlackHeight @-}
{-@ validBlackHeight :: {x:RBSet a | noSpecialChild x} -> Bool @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight EE = True
validBlackHeight (T _ l _ r) = validBlackHeight l && validBlackHeight r
                            && blackHeightL l == blackHeightL r           
                            
{-@ inline prop_CT @-}
{-@ prop_CT :: {x:RBSet a | noSpecialColor x} 
            -> {v:Bool | v => prop_IM x} @-}
{-@ invariant {t:RBSet a | prop_CT t => prop_IM t} @-} 
prop_CT :: (Ord a) => RBSet a -> Bool
prop_CT t = noSpecialColor t 
         && redChildIsBlack t 
         && validBlackHeight t
 --        && prop_BST' t
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
   --      && prop_BST' t
{-@ type IM a = {v:RBSet a | prop_IM v} @-}

{-@ measure tooBlack @-}
tooBlack :: Color -> Bool
tooBlack BB = True
tooBlack _ = False

{-@ measure tooRed @-}
tooRed :: Color -> Bool
tooRed NB = True
tooRed _ = False

{-@ inline isBB' @-}
isBB' t = color t == BB

{-@ measure prop_BST' @-}
prop_BST' :: (Ord a) => RBSet a -> Bool
prop_BST' (T _ l@(T _ _ xl _) x 
               r@(T _ _ xr _)) = (xl < x) && (x < xr)
                              && prop_BST' l 
                              && prop_BST' r
prop_BST' (T _ l@(T _ _ xl _) x r) = (xl < x)
                                  && prop_BST' l
                                  && prop_BST' r
prop_BST' (T _ l x r@(T _ _ xr _)) = (x < xr)
                                  && prop_BST' l
                                  && prop_BST' r
prop_BST' (T _ l x r) = prop_BST' l && prop_BST' r --Why do I need these
prop_BST' _ = True 
