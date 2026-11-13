----------------------------------------
-- Quiz : Proofs and Applied Proofs
----------------------------------------
-- Name:
-- Complete the four questions (100 points total).
-- Download this file from Canvas; upload ProofsQuiz.agda to Submitty.
-- Keep the filename, module name, supplied library, and question types.
-- You may change question clauses, split cases, and add function helpers.
-- Do not add imports, postulates, or pragmas, or disable safety checks.
-- Partial credit is awarded by question; unrelated holes do not lose credit.
-- This file is self-contained: no other files or standard library are needed.
--
-- C-c C-l : load       C-c C-, : goal/context
-- C-c C-c : case split (empty input introduces arguments)
-- Unicode: \bot = ⊥, \neg = ¬, \uplus = ⊎, \== = ≡, \ne = ≠

module ProofsQuiz where

----------------------------------------
-- Supplied library : do not change
----------------------------------------
data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x
infix 4 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)
infix 4 _≠_

data _⊎_ (A B : Set) : Set where
    left : A → A ⊎ B
    right : B → A ⊎ B
infixr 4 _⊎_

data Nat : Set where
    zero : Nat
    succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + n = n
succ m + n = succ (m + n)
infixl 6 _+_

add-zero : (n : Nat) → n + zero ≡ n
add-zero zero = refl
add-zero (succ n) = cong succ (add-zero n)

add-succ : (m n : Nat) → m + succ n ≡ succ (m + n)
add-succ zero n = refl
add-succ (succ m) n = cong succ (add-succ m n)

succ-inj : {x y : Nat} → succ x ≡ succ y → x ≡ y
succ-inj refl = refl

succ-eq-add-one : (n : Nat) → succ n ≡ n + 1
succ-eq-add-one n = sym (trans (add-succ n 0) (cong succ (add-zero n)))

----------------------------------------
-- Question 1 (20 points) : Refuting an OR
----------------------------------------
-- If both A and B are false, show that A OR B is false.
-- Use the constructive meaning of negation and the evidence in an OR.
refute-either : {A B : Set} → ¬ A → ¬ B → ¬ (A ⊎ B)
refute-either not-a not-b (left x) = not-a x
refute-either not-a not-b (right x) = not-b x

----------------------------------------
-- Question 2 (25 points) : Equality reasoning
----------------------------------------
-- From x + 0 = y, prove that succ x = succ y.
-- The library includes add-zero, sym, trans, and cong.
lift-equality : (x y : Nat) → x + 0 ≡ y → succ x ≡ succ y
lift-equality x y h = cong succ (trans (sym (add-zero x)) h)

----------------------------------------
-- Question 3 (30 points) : Cancel addition by one
----------------------------------------
-- From x + 1 = y + 1, prove x = y.
-- Use the supplied facts connecting addition by one and successors.
cancel-one : (x y : Nat) → x + 1 ≡ y + 1 → x ≡ y
cancel-one x y h = succ-inj (trans (succ-eq-add-one x) (trans h (sym (succ-eq-add-one y))))

----------------------------------------
-- Question 4 (25 points) : An impossible equality
----------------------------------------
-- Prove that zero differs from every successor.
-- You may introduce arguments and replace the clause with an absurd clause.
zero-not-successor : (n : Nat) → zero ≠ succ n
zero-not-successor n ()
