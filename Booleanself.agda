open import Equality 

module Booleanself where

    data Bool : Set where
        true : Bool
        false : Bool 

    id : Bool → Bool  -- ctrl c ctrl f skips to a hole 
    id true = true -- ctrl c ctrl r attempts to refine
    id false = false

    not : Bool → Bool
    not true = false
    not false = true 

    always-true : Bool → Bool
    always-true b = true 

    always-false : Bool → Bool
    always-false b = false
