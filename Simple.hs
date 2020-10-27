{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--exact-data" @-}

data Color = 
   R  -- red
 | B  -- black
 deriving (Show, Eq)

data RBSet a =
   E  -- black leaf
 | T Color (RBSet a) a (RBSet a)
 deriving (Show, Eq)

{-@ yyy :: {x:RBSet a | redChildIsBlack x && validBlackHeight x} -> {v:Bool | v} @-}
yyy (T R E _ E) = True
--yyy (T R (T B _ _ _) _ E) = False
yyy (T R l _ r) = (not $ emptyTree l)-- && (not $ emptyTree r)

yyy (T B E _ E) = True
yyy (T B E _ (T R _ _ _)) = True 
yyy (T B (T R _ _ _) x E) = True
--yyy (T B (T B _ _ _) _ E) = False
yyy (T _ l _ r) = (not $ emptyTree l)-- && (not $ emptyTree r)

{-@ measure redChildIsBlack @-}
redChildIsBlack :: RBSet a  -> Bool
redChildIsBlack E = True
redChildIsBlack (T R a x b) = color' a == B && 
                              color' b == B && 
                              redChildIsBlack a && redChildIsBlack b
redChildIsBlack (T B a x b) = redChildIsBlack a && redChildIsBlack b

{-@ measure color' @-}
color' :: RBSet a -> Color
color' (T c _ _ _) = c
color' E = B

{-@ measure validBlackHeight @-}
validBlackHeight :: RBSet a -> Bool
validBlackHeight E = True
validBlackHeight (T _ l _ r) = blackHeightL l == blackHeightL r && validBlackHeight l && validBlackHeight r

{-@ measure blackHeightL @-}
{-@ blackHeightL :: RBSet a -> { i : Int | i >= 1} @-}
blackHeightL :: RBSet a -> Int
blackHeightL E = 1
blackHeightL (T c l _ r) = (if c == B then 1 else 0) + blackHeightL l

{-@ measure emptyTree @-}
emptyTree :: RBSet a -> Bool
emptyTree E = True
emptyTree _ = False
