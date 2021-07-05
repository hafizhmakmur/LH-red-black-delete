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
 | T Color a (RBSet a) (RBSet a)
 deriving (Show, Eq)

 -- Private auxiliary functions --

{-@ redden :: {x:CT a | color' x == B} 
           -> {v:IM a | blackHeightL v == (blackHeightL x - 1) } @-}
redden :: RBSet a -> RBSet a
redden (T _ x a b) = T R x a b

{-@ blacken' :: IM a -> RT a @-}    
-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R x a b) = T B x a b
blacken' (T B x a b) = T B x a b

-- blacken for delete
-- root is never red, could be double black 
{-@ blacken :: IM a -> RT a @-}    
blacken :: RBSet a -> RBSet a
blacken (T B x a b) = T B x a b
blacken (T BB x a b) = T B x a b
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
blacker' (T c x l r) = T (blacker c) x l r

{-@ redder' :: {x:RBSet a | (prop_IM x && isBB' x) || (prop_CT x)} 
            -> {v:RBSet a | ((prop_IM x && isBB' x && prop_CT v) || 
                             (prop_CT x && prop_IM v))
                         && (blackHeightL v == (blackHeightL x - 1)) } @-}
redder' :: RBSet a -> RBSet a
redder' EE = E
redder' (T c x l r) = T (redder c) x l r 

 -- `balance` rotates away coloring conflicts:
{-@ balance :: c:Color 
            -> x:a 
            -> {l:RBSL a x | (prop_IM l) || (prop_CT l) } 
            -> {r:RBSR a x | ((prop_IM l && prop_CT r) ||
                              (prop_CT l && prop_IM r)) 
                          && (blackHeightL l == blackHeightL r) } 
            -> {v:RBSet a | ((c /= B && prop_IM v) || prop_CT v) 
                         && (blackHeightL v 
                             == (blackHeightL l + colorValue c))} 
@-} 
-- beware beware blackHeight still dont accept NB
balance :: Color -> a -> RBSet a -> RBSet a -> RBSet a

 -- Okasaki's original cases:
balance B z (T R y (T R x a b) c) d = T R y (T B x a b) (T B z c d)
balance B z (T R x a (T R y b c)) d = T R y (T B x a b) (T B z c d)
balance B x a (T R z (T R y b c) d) = T R y (T B x a b) (T B z c d)
balance B x a (T R y b (T R z c d)) = T R y (T B x a b) (T B z c d)

 -- Six cases for deletion:
balance BB z (T R y (T R x a b) c) d = T B y (T B x a b) (T B z c d)
balance BB z (T R x a (T R y b c)) d = T B y (T B x a b) (T B z c d)
balance BB x a (T R z (T R y b c) d) = T B y (T B x a b) (T B z c d)
balance BB x a (T R y b (T R z c d)) = T B y (T B x a b) (T B z c d)

balance BB x a (T NB z (T B y b c) d@(T B _ _ _)) 
    = T B y (T B x a b) (balance B z c (redden d))
balance BB z (T NB x a@(T B _ _ _) (T B y b c)) d
    = T B y (balance B x (redden a) b) (T B z c d)

-- Semua kasus valid lain yang menghasilkan IM
balance color x a@(T R _ (T B _ _ _) (T B _ _ _)) 
                b@(T R _ (T B _ _ _) (T B _ _ _)) = T color x a b  
balance color x a@(T R _ (T B _ _ _) (T B _ _ _)) 
                b@(T B _ _ _) = T color x a b
balance color x a@(T B _ _ _) 
                b@(T R _ (T B _ _ _) (T B _ _ _)) = T color x a b  
balance color x a@(T B _ _ _) b@(T B _ _ _) = T color x a b
balance color x a@E b@E = T color x a b 

-- fall through cases, should be proven that it's never reached
balance color x a b = T color x a b 


 -- `bubble` "bubbles" double-blackness upward:
{-@ bubble :: {c:Color | not (tooBlack c)}
           -> x:a
           -> {l:RBSL a x | prop_CT l || prop_IM l}
           -> {r:RBSR a x | ((prop_CT l && prop_IM r) || 
                             (prop_IM l && prop_CT r))
                         && (blackHeightL l == blackHeightL r) }
           -> {v:IM a | blackHeightL v == blackHeightL l + (colorValue c) } 
@-}
bubble :: Color -> a -> RBSet a -> RBSet a -> RBSet a
bubble color x l r
 | isBB(l) || isBB(r) = balance (blacker color) x (redder' l) (redder' r)
 | otherwise          = balance color x l r 
 




 -- Public operations --

{-@ empty :: {v:RT a | normalLeaf v} @-}
empty :: RBSet a
empty = E


{-@ member :: (Ord a) => a -> CT a -> Bool@-}
member :: (Ord a) => a -> RBSet a -> Bool
member x E = False
member x (T _ y l r) | x < y     = member x l
                     | x > y     = member x r
                     | otherwise = True
                     
{-@ insert :: (Ord a) => a -> RT a -> RT a @-}
insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins x s)

{-@ ins :: (Ord a) => a 
                   -> x:CT a 
                   -> {v:IM a | blackHeightL v == blackHeightL x} @-}
ins x E = T R x E E
ins x s@(T color y a b) | x < y     = balance color y (ins x a) b
                        | x > y     = balance color y a (ins x b)
                        | otherwise = s 

{-@ max :: {x:CT a | not normalLeaf x} -> {v:a | v = max' x} @-}
max :: RBSet a -> a
max E = error "no largest element"
max (T _ x _ E) = x
max (T _ x _ r) = max r

{-@ measure max' @-}
{-@ max' :: {x:CT a | not normalLeaf x} -> {v:a | v >= key' x} @-}
max' :: RBSet a -> a
max' (T _ x _ E) = x
max' (T _ x _ r) = max' r

{-@ measure key' @-}
key' :: RBSet a -> a
key' (T _ x _ _) = x

{-@ measure rt' @-}
rt' :: RBSet a -> RBSet a
rt' (T _ _ _ r) = r

-- Remove this node: it might leave behind a double black node
{-@ remove :: {x:CT a | not normalLeaf x} 
           -> {v:IM {w:a | (normalLeaf (rt' x)) => (w < key' x) } 
                         | blackHeightL v == blackHeightL x} @-}
remove :: RBSet a -> RBSet a
-- remove E = E   -- impossible!
-- ; Leaves are easiest to kill:
remove (T R _ E E) = E
remove (T B _ E E) = EE
-- ; Killing a node with one child;
-- ; parent or child is red:
-- remove (T R _ E child) = child
remove (T R _ child E) = child -- 
remove (T B _ E (T R a x b)) = T B a x b
remove (T B _ (T R a x b) E) = T B a x b
-- ; Killing a black node with one black child:
-- remove (T B _ E child@(T B _ _ _)) = blacker' child
remove (T B _ child@(T B _ _ _) E) = blacker' child -- 
-- ; Killing a node with two sub-trees:
remove (T color y l r) = bubble color mx l' r 
    where 
        (mx, l') = getMax l
-- where mx = max l
--       l' = removeMax l

{-@ getMax :: {x:CT a | not normalLeaf x} 
           -> (m :: a, 
              {v : IM {w : a | (w < m)} | blackHeightL v == blackHeightL x}) 
@-} 
getMax :: RBSet a -> (a, RBSet a)
getMax s@(T _ m l E) = (m, remove s) 
getMax s@(T c x l r) = case getMax r of (m, r') -> (m, bubble c x l r') 

{-@ removeMax :: {x:CT a | not normalLeaf x} 
              -> {v:IM {w : a | True} | (blackHeightL v == blackHeightL x)} @-}
removeMax :: RBSet a -> RBSet a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ l E) = remove s
removeMax s@(T color x l r) = bubble color x l (removeMax r) 

{-@ delete :: (Ord a) => a -> x:RT a -> v:RT a @-}   
delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x s = blacken (del x s)

{-@ del :: Ord a => a 
                 -> x:CT a 
                 -> {v:IM a | blackHeightL v == blackHeightL x} @-}
del x E = E
del x s@(T color y a' b') | x < y   = bubble color y (del x a') b'
                          | x > y     = bubble color y a' (del x b')
                          | otherwise = remove s

{-@ prop_del :: Int -> RT Int -> Bool @-}
prop_del :: Int -> RBSet Int -> Bool
prop_del x s = color (del x s) `elem` [B, BB]


--- Testing code

--{-@ elements :: Ord a => RT a -> [a] @-}
elements :: Ord a => RBSet a -> [a]
elements t = aux t [] where
      aux E acc = acc
      aux (T _ x a b) acc = aux a (x : aux b acc)

instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = liftM (foldr @[] insert empty) arbitrary

{-@ prop_BST :: x:RT Int -> True @-}
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

{-@ color :: x:RBSet a -> {c:Color | c = color' x} @-}
color :: RBSet a -> Color
color (T c _ _ _) = c
color E = B
color EE = BB

{-@ prop_Rb2 :: x:RT Int -> {v:Bool | v <=> blackRoot x} @-}
prop_Rb2 :: RBSet Int -> Bool
prop_Rb2 t = color t == B

{-@ prop_Rb3 :: x:RT Int -> {v:Bool | v <=> validBlackHeight x} @-}
{-@ aux :: x:RT a 
        -> ( m :: {v:Bool | v <=> validBlackHeight x}
           , n :: b)
@-} 
prop_Rb3 :: RBSet Int -> Bool
prop_Rb3 t = fst (aux t) where 
  aux E = (True, 0)
  aux (T c x a b) = (h1 == h2 && b1 && b2, if c == B then h1 + 1 else h1) where
      (b1 , h1) = aux a
      (b2 , h2) = aux b

{-@ prop_Rb4 :: x:RBSet Int -> {v:Bool | v <=> redChildIsBlack x} @-}
prop_Rb4 :: RBSet Int  -> Bool
prop_Rb4 E = True
prop_Rb4 (T R x a b) = color a == B && color b == B && prop_Rb4 a && prop_Rb4 b
prop_Rb4 (T B x a b) = prop_Rb4 a && prop_Rb4 b


isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x
              

{-@ prop_delete_spec1 :: RT Int -> True @-}
prop_delete_spec1 :: RBSet Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

{-@ prop_delete_spec2 :: RT Int -> True @-}
prop_delete_spec2 :: RBSet Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
   allpairs = [ (x,y) | x <- elements t, y <- elements t ]

{-@ prop_delete_spec3 :: RT Int -> Int -> Property @-}
prop_delete_spec3 :: RBSet Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)

{-@ prop_delete_bst :: RT Int -> True @-}
prop_delete_bst :: RBSet Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

{-@ prop_delete2 :: RT Int -> True @-}
prop_delete2 :: RBSet Int -> Bool
prop_delete2 t = all (\x -> prop_Rb2 (delete x t)) (elements t)

{-@ prop_delete3 :: RT Int -> True @-}
prop_delete3 :: RBSet Int -> Bool
prop_delete3 t = all (\x -> prop_Rb3 (delete x t)) (elements t)

{-@ prop_delete4 :: RT Int -> True @-}
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
{-@ blackHeightL :: {x:RBSet a | noSpecialColor x} -> {i:Int | i >= 1} @-}
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

{-@ inline isBB' @-}
isBB' t = color' t == BB
