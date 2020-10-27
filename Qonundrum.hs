{-# LANGUAGE InstanceSigs,GADTs, DataKinds, PolyKinds, KindSignatures, MultiParamTypeClasses, FlexibleInstances, TypeFamilies, TypeOperators, ScopedTypeVariables #-}

module Qonundrum where

data Color = Red | Black | DoubleBlack | NegativeBlack

data SColor (c :: Color) where
   R  :: SColor Red -- red
   B  :: SColor Black -- black
   BB :: SColor DoubleBlack -- double black
   NB :: SColor NegativeBlack -- negative black

data CT (c :: Color) (a :: *) where
   E  :: CT Black a
   T  :: Valid c c1 c2 => 
         SColor c -> (CT c1 a) -> a -> (CT c2 a) -> CT c a

class Valid (c :: Color) (c1 :: Color) (c2 :: Color) where
instance Valid Red Black Black 
instance Valid Black c1 c2

redden :: CT c a -> DT a
redden (T B a x y)  = DT R a x y
redden (T BB a x y) = DT B a x y
redden (T R a x y)  = DT NB a x y
redden (T NB a x y)  = error "Nope"

data DT a where
  DT  :: SColor c -> CT c1 a -> a -> CT c2 a -> DT a
  DE  :: DT a
  DEE :: DT a

main :: IO ()
main = 
 do
 return $! ()
