module Equality where 

    -- Definition and Properties of Propositional Equality 
    ------------------------------------------------------
    -- Propositional Equality as an Agda datatype  
    -- Type \== for unicode input mode to get ≡ 
    -- The only value is the Reflexive Property of Equality 
    data _≡_ {A : Set} : A → A → Set where 
        refl : {x : A} → x ≡ x -- any x is equal to itself. 
        
        -- for any type 'A', if x is of type A, then x = x, refl x = x
    
    -- This gives operator precedence (manually dictates PEMDAS), 1-20
    infix 4 _≡_  

    -- This identifies our datatype with Agda's builtin equality
    {-# BUILTIN EQUALITY _≡_ #-}

    -- Now that we have defined propositional equality as an identity 
    -- (that is, x is equal to itself for any x), we can derive other
    -- properties of equality 

    -- Equality is symmetric.
    -- Our proof consists of pattern matching on the hypothesis hyp : x ≡ y 
    -- the only value is refl (x ≡ x), so it turns out we only have to prove
    -- that if x ≡ x then x ≡ x.
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x 
    sym refl = refl -- ctrl c ctrl ',' shows both goals and restraints.

    -- An involution is a function that is its own inverse. 
    -- The symmetric property of equality is involutive as a function. 
    sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p 
    sym-involutive refl = refl

    -- Equality is transitive. 
    -- Once again, our proof consists of pattern matching on the equality datatype, but
    -- the only value is refl, so it turns out that we only have to prove that 
    -- if x ≡ x and x ≡ x then x ≡ x 
    trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
    trans refl hyp = hyp 

    -- Functions preserve equality. 
    -- If f is a function and x ≡ y, then f x ≡ f y 
    -- We pattern match on the hypothesis x ≡ x, like above. 
    -- (cong is short for Congruence)
    cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y 
    cong f refl = refl

    -- Substitution Property of Equality 
    -- If x ≡ y then we should be able to substitute y for x 
    subst : ∀ {A : Set} {x y : A} → (C : A → Set) → x ≡ y → C x → C y
    subst C refl cx = cx 

    ------------------------------------------------------

    -- Tools for Equational Reasoning 
    ------------------------------------------------------
    -- These are to help us write proofs in Agda that involve
    -- manipulating equations in a more natural language style. 

    -- To prove a0 == an:
    -- 
    --     proof a0
    --        by reason1
    --    equals a1
    --        by reason2
    --    equals a2
    --       ...
    --        by reasonn
    --    equals an 
    --           ∎

    -- To start a proof, lets write the word proof! 
    -- The argument is the complete equality chain built below.
    proof_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
    proof eq = eq

    -- Make proof_ bind more loosely than the steps inside its proof chain.
    infix 1 proof_

    -- When we end a proof in English, we write QED or make a  "tombstone" marker. 
    -- We will add that here in Agda. Type \qed to make it.
    _∎ : {A : Set} → (x : A) → x ≡ x 
    _∎ x = refl 

    -- Set the binding precedence for qed to end the proof context 
    infix 3 _∎

    -- We want to say "(some expression) by (reason) equals (new expression)"
    -- For example, we might want to write: "x + 0 by additive-identity equals x"
    by-equals : ∀ {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
    by-equals x reason rest = trans reason rest

    -- We have defined the by-equals function, but we really would like 
    -- to match the infix notation like I wrote in the comments.
    -- We can define syntax for Agda like so:
    syntax by-equals x reason rest = x by reason equals rest
    -- Each step associates to the right, ending with _∎.
    infixr 2 by-equals

    -- Sometimes our justification will be "by definition" because
    -- Agda can justify a line with refl. We will have definition 
    -- be a synonym for refl. 
    definition : ∀ {A : Set} → {x : A} → x ≡ x 
    definition = refl 

    ------------------------------------------------------

    -- Comments and Acknowledgements 

    -- The ∀ symbol is typed with \forall 
    -- It is not required in Agda syntax and is merely there to remind the reader
    -- of what is implicit in Agda. 

    -- Peng Fu, Peter Selinger, and Sandy Maquire influenced the development of this document.

    ------------------------------------------------------












    


