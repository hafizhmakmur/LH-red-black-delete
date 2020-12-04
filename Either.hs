{-@ inline isOdd @-}
isOdd :: Int -> Bool
isOdd x = (mod x 2) == 1

{-@ inline isEven @-}
isEven :: Int -> Bool
isEven x = (mod x 2) == 0

--{-@ odd_plus :: {x:Int | isOdd x} -> {y:Int | isEven y} -> {z:Int | isOdd z} @-}
--{-@ odd_plus :: {x:Int | isEven x} -> {y:Int | isOdd y} -> {z:Int | isOdd z} @-}
{-@ odd_plus :: {x:Int | (isOdd x) || (isEven x)} 
             -> {y:Int | ((isOdd x && isEven y) ||
                          (isEven x && isOdd y)) } 
             -> {z:Int | isOdd z} @-}
odd_plus :: Int -> Int -> Int
odd_plus x y = x + y


{-@ plusOne :: {x:Int | (isOdd x) || (isEven x)} 
            -> {y:Int | ((isOdd x && isEven y) ||
                         (isEven x && isOdd y)) } @-}
plusOne :: Int -> Int 
plusOne x = x + 1

{-@ xxx :: Int -> {x:Int | isOdd x} @-}
xxx :: Int -> Int
xxx x = odd_plus x (plusOne x)

{-@ inline canBeBubbled @-}
canBeBubbled :: Int -> Bool
canBeBubbled x = if (isOdd x) || (isEven x) then False else True
