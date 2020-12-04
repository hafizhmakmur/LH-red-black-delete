{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Fibonacci2 where

{-@ reflect isFib @-}
isFib :: [Int] -> Bool
isFib (x:y:z:rest) = x == y + z && isFib (y:z:rest)
isFib _            = True

{-@ reflect fib @-}
{-@ fib :: {x:Int | x > 0}  -> Nat @-}
fib :: Int -> Int
fib 1 = 0
fib 2 = 1
fib n = fib (n-1) + fib (n-2)

{-@ reflect fibGen @-} 
{-@ fibGen :: Nat -> [Int] @-}
fibGen :: Int -> [Int]
fibGen 0 = []
fibGen n = fib n : fibGen (n-1) 

{-@ thm :: n:Nat -> { isFib (fibGen n) } @-}
thm :: Int -> ()
thm 0 = () 
thm 1 = ()
thm 2 = () 
thm n = thm (n-1) `seq` thm (n-2)








