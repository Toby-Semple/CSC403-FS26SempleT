----------------------------------------
-- Agda Lab 4 : Powers of the Naturals
----------------------------------------

-- Instructions
---------------
-- Complete the following file by filling in the "holes". There are 23
-- guided holes, followed by one final boss problem. Some holes cannot be
-- filled until you have completed earlier ones.
--
-- Keep Equality.agda, Nat-Add-Answers.agda, and Nat-Mul-Answers.agda in
-- the same folder as this file. We will use the results from Labs 2 and 3.
-- If you need a refresher on Agda hot-keys, see your Nat-Add file.
-- Use pattern matching, recursion, and our equational reasoning tools.
-- In the proof chains, fill in the reason for each equality.

open import Equality
open import Nat-Add-Answers
open import Nat-Mul
module Nat-Pow where

--------------------------------
-- Powers on Natural Numbers
--------------------------------

-- Exponentiation is repeated multiplication. This time we recurse on
-- the exponent (the second argument), rather than the base.
-- Define pow so that pow a Z = 1 and pow a (S n) = pow a n * a.
pow : Nat → Nat → Nat
pow a Z = 1
pow a (S n) = (pow a n) * a

-- infix notation
_^_ : Nat → Nat → Nat
a ^ n = pow a n

infixr 8 _^_

-- These two equations hold by definition once pow is complete.
pow-zero : (a : Nat) → a ^ Z ≡ 1
pow-zero a = refl

pow-succ : (a n : Nat) → a ^ S n ≡ (a ^ n) * a
pow-succ a n = refl

-- Try C-c C-n with 2 ^ 3 after completing pow.
-- We keep parentheses around products in sums: in our earlier labs,
-- addition and multiplication were both given precedence 6.

-------------------------------
-- Properties of Powers
-------------------------------

-- Level 1 : Zero to the Zero Power
-- Our definition makes this equal to 1. Can Agda see it directly?
zero-pow-zero : Z ^ Z ≡ 1
zero-pow-zero = refl

-- Level 2 : Zero to a Positive Power
-- Unfold pow and use a property of multiplication from Lab 3.
zero-pow-succ : (n : Nat) → Z ^ S n ≡ Z
zero-pow-succ Z = pow-succ Z Z
zero-pow-succ (S n) = mul-zero (Z ^ S n)

-- (S n) = proof 
--           Z ^ S (S n) by (pow-succ Z (S n)) equals 
--          Z ^ (S n) * Z by mul-zero (Z ^ (S n)) equals Z ∎

-- Level 3 : A First Power
-- After unfolding pow, which identity for multiplication do you need?
pow-one : (a : Nat) → a ^ 1 ≡ a
pow-one Z = refl
pow-one (S a) = cong succ (pow-one a)

-- Level 4 : Powers of One
-- Pattern match on n and use recursion. Lift the recursive hypothesis
-- through multiplication using cong.
one-pow : (n : Nat) → 1 ^ n ≡ 1
one-pow Z = refl
one-pow (S n) = proof
    1 ^ S n
      by definition equals
    (1 ^ n) * 1
      by cong (\t → t * 1) (one-pow n) equals
    1 * 1
      by definition equals
    1 ∎

-- Level 5 : Squaring
-- Use pow-one inside a product. Save this lemma for the final boss!
pow-two : (a : Nat) → a ^ 2 ≡ a * a
pow-two Z = refl
pow-two (S a) = trans (pow-succ (S a) 1) (cong (\t → t * (S a)) (pow-one ((S a))))

-- Level 6 : Adding Exponents
-- We induct on n. Since our addition recurses on its FIRST argument,
-- we need add-succ to expose the successor in m + S n.
pow-add : (a m n : Nat) → a ^ (m + n) ≡ (a ^ m) * (a ^ n)
pow-add a m Z = proof
    a ^ (m + Z)
      -- Use add-zero inside the exponent.
      by cong (\t → a ^ t) (add-zero m) equals
    a ^ m
      -- Use mul-one backwards.
      by sym (trans (cong (\t → (a ^ m) * t) (pow-zero a)) (mul-one (a ^ m))) equals
    (a ^ m) * (a ^ Z) ∎
pow-add a m (S n) = proof
    a ^ (m + S n)
      -- Use add-succ inside the exponent.
      by cong (pow a) (add-succ m  n) equals
    a ^ S (m + n)
      by definition equals
    (a ^ (m + n)) * a
      -- Use cong with the recursive hypothesis pow-add a m n.
      by cong (\t → mul t a) (pow-add a m n) equals
    ((a ^ m) * (a ^ n)) * a
      -- Use associativity of multiplication.
      by mul-assoc (a ^ m) (a ^ n) a equals
    (a ^ m) * ((a ^ n) * a)
      by definition equals
    (a ^ m) * (a ^ S n) ∎

-- Level 7 : A Power of a Product
-- Induct on n again. In the successor case, we need to move a past
-- b ^ n. Associativity changes grouping; commutativity changes order.
mul-pow : (a b n : Nat) → (a * b) ^ n ≡ (a ^ n) * (b ^ n)
mul-pow a b Z = refl
mul-pow a b (S n) = proof
    (a * b) ^ S n
      by definition equals
    ((a * b) ^ n) * (a * b)
      -- Use the recursive hypothesis inside the product.
      by cong (\t → t * (a * b)) (mul-pow a b n) equals
    ((a ^ n) * (b ^ n)) * (a * b)
      -- Regroup the outer product.
      by mul-assoc (a ^ n) (b ^ n) (a * b) equals
    (a ^ n) * ((b ^ n) * (a * b))
      -- Regroup inside multiplication by a ^ n.
      by cong (mul (a ^ n)) (sym (mul-assoc (b ^ n) a b)) equals
    (a ^ n) * (((b ^ n) * a) * b)
      -- Swap b ^ n and a using cong and mul-comm.
      by cong (\t → (a ^ n) * (t * b)) (mul-comm (b ^ n) a ) equals
    (a ^ n) * ((a * (b ^ n)) * b)
      -- Regroup the inner product.
      by cong (mul (a ^ n)) (mul-assoc a (b ^ n) b) equals
    (a ^ n) * (a * ((b ^ n) * b))
      -- Regroup the outer product backwards.
      by sym (mul-assoc (a ^ n) a ((b ^ n) * b)) equals
    ((a ^ n) * a) * ((b ^ n) * b)
      by definition equals
    (a ^ S n) * (b ^ S n) ∎

-- Level 8 : A Power of a Power
-- Induct on n. Use pow-add to combine powers with the same base,
-- then use mul-succ to recognize the exponent m * S n.
pow-pow : (a m n : Nat) → (a ^ m) ^ n ≡ a ^ (m * n)
pow-pow a m Z = proof
    (a ^ m) ^ Z
      by definition equals
    a ^ Z
      -- Use mul-zero backwards inside the exponent.
      by cong (pow a) (sym (mul-zero m)) equals
    a ^ (m * Z) ∎
pow-pow a m (S n) = proof
    (a ^ m) ^ S n
      by definition equals
    ((a ^ m) ^ n) * (a ^ m)
      -- Use the recursive hypothesis.
      by cong (\t → t * (a ^ m)) (pow-pow a m n) equals
    (a ^ (m * n)) * (a ^ m)
      -- Use pow-add backwards.
      by sym ((pow-add a (m * n) m)) equals
    a ^ ((m * n) + m)
      -- Use mul-succ backwards inside the exponent.
      by sym (cong (pow a)  (mul-succ m n)) equals
    a ^ (m * S n) ∎

-------------------------------
-- Preparing for the Boss
-------------------------------

-- Here is a useful fact about doubling, with its proof supplied.
two-mul : (n : Nat) → 2 * n ≡ n + n
two-mul n = proof
    2 * n
      by definition equals
    n + (1 * n)
      by cong (λ t → n + t) (one-mul n) equals
    n + n ∎

-------------------------------
-- Boss Battle
-------------------------------

--Tag-ins

-- zero-equals : (x y : Nat) → (x ≡ Z) → (y ≡ Z) → x ≡ y
-- zero-equals x y px py = trans px (sym py)

-- rev-equals : (x y : Nat) → (y ≡ x) → x ≡ y
-- rev-equals x y pyx = sym pyx

--Preparations


-- Level 9 : The Square of a Sum
-- It is tempting to think that (a + b) ^ 2 = a ^ 2 + b ^ 2,
-- but the cross terms do not disappear!
--
-- Build your own equality chain. Start with pow-two, distribute,
-- and use mul-comm to make the cross terms match. Then regroup
-- and use two-mul to collect the two copies of a * b.
-- You may add helper lemmas if you find them useful.
-- Remember: add-mul x y z expands (y + z) * x.
add-sq : (a b : Nat) → (a + b) ^ 2 ≡ ((a ^ 2) + (b ^ 2)) + ((2 * a) * b)
add-sq a b = proof
    (a + b) ^ 2
      by pow-two (a + b) equals 
    (a + b) * (a + b)
      by mul-add (a + b) a b equals 
    ((a + b) * a) + ((a + b) * b)
      by cong (λ t → t + ((a + b) * b)) (add-mul a a b) equals 
    ((a * a) + (b * a)) + ((a + b) * b)
      by cong (λ t → ((a * a) + t) + ((a + b) * b)) (mul-comm b a) equals 
    ((a * a) + (a * b)) + ((a + b) * b)
      by cong (λ t → ((a * a) + ( a * b)) + t) (add-mul b a b) equals
    ((a * a) + (a * b)) + ((a * b) + (b * b))
      by cong (λ t → (t + (a * b)) + ((a * b) + (b * b))) (sym (pow-two a)) equals
    ((a ^ 2) + (a * b)) + ((a * b) + (b * b))
      by cong (λ t → ( a ^ 2 + (a * b)) + ((a * b) + t)) (sym (pow-two b)) equals
    ((a ^ 2) + (a * b)) + ((a * b) + (b ^ 2))
      by rev-equals {! ((a ^ 2) + (a * b)) + ((a * b) + (b ^ 2))  !} (((a ^ 2) + (b ^ 2)) + ((2 * a) * b)) (proof 
        ((a ^ 2) + (b ^ 2)) + ((2 * a) * b)
          by cong (λ t → (a ^ 2) + (b ^ 2) + t) (mul-assoc 2 a b)equals
        ((a ^ 2) + (b ^ 2)) + (2 * (a * b))
          by cong (λ t → (a ^ 2) + (b ^ 2) + t) (two-mul (a * b)) equals
        ((a ^ 2) + (b ^ 2)) + ((a * b) + (a * b))
          by {! cong (λ t → (a ^ 2) + t ) (add-comm (b ^ 2) ((a * b) + (a * b)))   !} equals
        ((a ^ 2) + ((a * b) + (a * b) + (b ^ 2)))
          by {!   !} equals
        {!   !}
          by {!   !} equals
        ((a ^ 2) + (a * b)) + ((a * b) + (b ^ 2)) ∎ ) equals
    ((a ^ 2) + (b ^ 2)) + ((2 * a) * b)∎

----------------------------------------
-- Acknowledgements
----------------------------------------
-- Exercise progression adapted from Power World in the Natural Number Game.
-- Power World levels were designed by Sian Carey.
-- https://github.com/leanprover-community/NNG4/tree/main/Game/Levels/Power
