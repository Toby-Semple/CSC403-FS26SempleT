

 module Pair where



     data Nat : Set where 
        zero : Nat       -- zero is a natural number 
        succ : Nat → Nat 

    data Bool : Set where
        true : Bool
        false : Bool 

            
    {-# BUILTIN NATURAL Nat #-}


    data Pair (A B : Set) : Set where
        _,_ : A → B → Pair A B

    curry : {A B C : Set} → (Pair A B → C) → A → B → C
    curry f = \ a → \ b → f (a , b)

    uncurry : {A B C : Set} → (A → B → C) → (Pair A B → C)
    uncurry g (a , b) = g a b

    firstPair : Pair Nat Bool → Nat
    firstPair (n , b) = n

    test : uncurry (curry firstpair) (S, false) = s
    