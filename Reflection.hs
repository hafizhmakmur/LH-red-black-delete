import Language.Haskell.Liquid.ProofCombinators

type Proof = ()
{-@ type OnePlusOne = {v: Proof | 1 + 1 == 3} @-}
{-@ type OnePlusOne' = { 1 + 1 == 2 } @-}
{-@ type PlusComm = x:Int -> y:Int -> {x + y == y + x} @-} 

{-@ propOnePlueOne :: _ -> OnePlusOne @-} 
propOnePlueOne _ = trivial *** QED 

{-@ propPlusComm :: PlusComm @-} 
propPlusComm _ _ = trivial *** QED 
