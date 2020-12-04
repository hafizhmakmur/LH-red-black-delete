{-@ inline isOdd @-}
isOdd :: Int -> Bool
isOdd x = (mod x 2) == 1

{-@ inline isEven @-}
isEven :: Int -> Bool
isEven x = (mod x 2) == 0

{-@ inline aaa @-}
aaa :: Int -> Bool
aaa x = if isOdd x then False else True

{-@ inline jaa @-}
jaa :: Int -> Bool
jaa x = if isOdd x then False else True

{-@ sdsd :: {x:Int | isEven x} -> {v:Bool | aaa x} @-}
sdsd :: Int -> Bool
sdsd x = True
