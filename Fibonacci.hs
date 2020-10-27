{-@ LIQUID "--exact-data" @-}
{-@ LIQUID "--no-termination" @-}

module Fibonacci where

{-@ measure isFibonacci @-}
isFibonacci :: [Int] -> Bool
isFibonacci [] = True
isFibonacci (x:[]) = True
isFibonacci (x:y:[]) = True
isFibonacci (x:y:z:xs) = ((x+y) == z) && (isFibonacci (y:z:xs))

{-@ fibonacci :: {x:Int | x > 0} -> Int @-}
fibonacci :: Int -> Int
fibonacci 1 = 0
fibonacci 2 = 1
fibonacci n = fibonacci (n-1) + fibonacci (n-2)

{-@ fibonacciGen :: {x:Int | x >= 0} -> {v:[Int] | isFibonacci v} @-}
fibonacciGen :: Int -> [Int]
fibonacciGen 0 = []
fibonacciGen n = fibonacciGen (n-1) ++ [fibonacci n]

{-@ fibonacci' :: {v:[Int] | len v > 0} @-}
fibonacci' = 1:2:(zipWith (+) fibonacci' (tail fibonacci'))
{-@ fibonacciGen' :: {x:Int | x >= 0} -> {v:[Int] | isFibonacci v} @-}
fibonacciGen' :: Int -> [Int]
fibonacciGen' n = takeWhile (<= n) fibonacci'
--
