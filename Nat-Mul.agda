----------------------------------------
-- Agda Lab 3 : Multiplication of the Naturals
---------------------------------------- 


-- Instructions
---------------
-- Complete the following file by filling in the "holes". There are 23
-- holes, and each of them is a homework problem. There is also a final boss problem. Some holes can't be
-- filled until you have completed earlier ones.
--
-- If you need a refresher on Agda hot-keys, see your Nat-Add file

open import Equality 
open import Nat
module Nat-Mul where 

--------------------------------
-- Multiplication on Natural Numbers
--------------------------------

mul : Nat → Nat → Nat 
mul Z y = Z
mul (S x) y = add y (mul x y)

-- infix notation 
_*_ : Nat → Nat → Nat 
x * y = mul x y 

infixl 6 _*_  

-------------------------------
-- Properties of Multiplication 
-------------------------------

zero-mul : ∀ (n : Nat) → Z * n ≡ Z 
zero-mul n = refl

mul-zero : ∀ (n : Nat) → n * Z ≡ Z 
mul-zero Z = refl
mul-zero (S n) = mul-zero n

-- In the successor case, (S n) * Z reduces to add Z (n * Z),
-- which reduces to n * Z because add Z t = t.
-- Thus the goal becomes n * Z ≡ Z, exactly the type of mul-zero n.


-- this one can be cleared with refl because
-- we defined multiplication this way 
succ-mul : ∀ (x y : Nat) → mul (S x) y ≡ add y (mul x y) 
succ-mul x y = refl 

mul-succ : ∀ (x y : Nat) → x * S y ≡ (x * y) + x
mul-succ Z y = refl
mul-succ (S x) y = proof
    S x * S y
      by definition equals
    S (y + (x * S y))
      -- Use cong with the recursive hypothesis mul-succ x y.
      -- y + ( x * S y) == (x * y) + x
      by cong S (cong (add y) (mul-succ x y)) equals
    S (y + ((x * y) + x))
      -- Use associativity under the successor function
      by cong S (sym (add-assoc y (x * y) x)) equals
    S ((y + (x * y)) + x)
      -- Use add-succ 
      by sym (add-succ (y + ( x * y)) x) equals
    (y + (x * y)) + S x
      by definition equals
    (S x * y) + S x ∎

-- alternatively one could do : trans (cong S (trans (cong (λ t → y + t) (mul-succ x y)) (sym (add-assoc y (x * y) x)))) (sym (add-succ (y + (x * y)) x))

one-mul : ∀ (n : Nat) → (S Z) * n ≡ n 
one-mul Z = refl
one-mul (S n) = cong S (one-mul n)

mul-one : ∀ (n : Nat) → n * (S Z) ≡ n 
mul-one Z = refl
mul-one (S n) = cong S (mul-one n)
 
-- Multiplication of the Naturals is Commutative 
mul-comm : (x y : Nat) → mul x y ≡ mul y x 
mul-comm Z y = sym (mul-zero y)
mul-comm (S x) y = proof
    S x * y
      by definition equals
    y + (x * y)
      -- Use cong with the recursive hypothesis mul-comm x y.
      by cong (y +_) (mul-comm x y) equals
    y + (y * x)
      -- Use commutativity of addition.
      by add-comm y ((y * x)) equals
    (y * x) + y
      -- Use mul-succ backwards.
      by sym (mul-succ y x) equals
    y * S x ∎

-- The Distributive Property of Multiplication on the Left over Addition 
mul-add : (x y z : Nat) → x * (y + z) ≡ (x * y) + (x * z)
mul-add Z y z = refl
mul-add (S x) y z = proof
    S x * (y + z)
      by definition equals
    (y + z) + (x * (y + z))
      -- Use cong with the recursive hypothesis mul-add x y z.
      by cong ((y + z) +_) (mul-add x y z) equals
    (y + z) + ((x * y) + (x * z))
      -- Use associativity of addition 
      by sym (add-assoc (y + z) (x * y) (x * z)) equals
    ((y + z) + (x * y)) + (x * z)
      -- Use add-right-comm 
      by cong (_+ (x * z)) (add-right-comm y z (x * y) ) equals
    ((y + (x * y)) + z) + (x * z)
      -- Use associativity of addition.
      by (add-assoc (y + (x * y)) z (x * z)  ) equals
    (y + (x * y)) + (z + (x * z))
      by definition equals
    (S x * y) + (S x * z) ∎

-- we can prove this using our previously proved theorems, do you see how?
-- The Distributive Property of Multiplication on the Right over Addition 
add-mul : (x y z : Nat) → (y + z) * x ≡ (y * x) + (z * x)
add-mul x y z = proof
    (y + z) * x
      -- Use commutativity of multiplication.
      by (mul-comm (y + z) x) equals
    x * (y + z)
      -- Use mul-add.
      by mul-add x y z equals
    (x * y) + (x * z)
      -- Use cong and mul-comm to swap the first product.
      by cong (_+ (x * z)) (mul-comm x y) equals
    (y * x) + (x * z)
      -- Use cong and mul-comm to swap the second product.
      by cong(( y * x) +_) (mul-comm x z) equals
    (y * x) + (z * x) ∎ 

-- Boss Battle 
-- Multiplication of the Naturals is Associative 
    
--Prep: if two equations both equal zero, then the two equations are equal to each other.
zero-equals : (x y : Nat) → (x ≡ Z) → (y ≡ Z) → x ≡ y
zero-equals x y px py = trans px (sym py)

rev-equals : (x y : Nat) → (y ≡ x) → x ≡ y
rev-equals x y pyx = sym pyx

mul-assoc : (x y z : Nat) → (x * y) * z ≡ x * (y * z) 
mul-assoc x y Z = proof -- Because x and y are assumed to be in parenthese, you can't do anything that involves x without pulling it out of the parentheses, so I'm splitting on 'z' so it's already out of the parentheses and can be brought around with 'mul-comm'
    (x * y) * Z
      by zero-equals ((x * y) * Z) (x * (y * Z)) ((mul-zero (x * y))) (trans (cong (x *_) (mul-zero y)) (mul-zero x)) equals
    x * (y * Z) ∎ 
mul-assoc x y (S z) = proof
    (x * y) * (S z)
      by (mul-comm (x * y) (S z))equals
    (x * y) + (z * (x * y))
      by rev-equals ((x * y) + (z * (x * y))) (x * (y * (S z))) (proof
            x * (y * (S z))
              by (cong (x *_) (trans (mul-succ y z) (add-comm (y * z) y))) equals
            x * (y + (y * z))
              by mul-add x y (y * z) equals
            (x * y) + (x * (y * z))
              by cong (\ z → (x * y) + (x * z)) (mul-comm y z) equals
            (x * y) + (x * (z * y))
              by cong (λ z → x * y + z) (trans (sym (mul-assoc x z y)) (trans (cong (λ z → z * y) (mul-comm x z)) (mul-assoc z x y))) equals
            (x * y) + (z * (x * y))
            ∎) equals
    x * (y * (S z)) ∎

--by {!   !} equals

-- Attempt 3: Thought that multiplication was distributable over itself. Back to Attempt 2.
-- mul-assoc Z y z = zero-equals (Z * y * z) (Z * (y * z)) (trans (cong (_* z) (zero-mul (Z * y))) (zero-mul z)) (zero-mul (y * z))
-- mul-assoc (S x) y z = proof
--       ((S x) * y) * z 
--         by {!  (add-mul ((S x)) y z) !} equals
--       ((S x) * z) * (z * y) 
--         by {!   !} equals
--       (S x) * (y * z) ∎

--Attempt 2.1: Got stuck, realized the solution to second case was to distribute, realize that's probably the intended method. Thought that would be easier
-- mul-assoc x y Z = proof -- Because x and y are assumed to be in parenthese, you can't do anything that involves x without pulling it out of the parentheses, so I'm splitting on 'z' so it's already out of the parentheses and can be brought around with 'mul-comm'
--     (x * y) * Z
--       by zero-equals ((x * y) * Z) (x * (y * Z)) ((mul-zero (x * y))) (trans (cong (x *_) (mul-zero y)) (mul-zero x)) equals
--     x * (y * Z) ∎ 
-- mul-assoc x y (S z) = proof
--     (x * y) * (S z)
--       by (mul-comm (x * y) (S z)) equals
--     (S z) * (x * y)
--       by {!   !} equals
--     (x * y) + (z * (x * y))
--       by {!   !} equals
--     x * (y * (S z)) ∎

-- Attempt 3
-- mul-assoc Z y z = definition
-- mul-assoc (S x) Z z = {! definition  !}
-- mul-assoc (S x) (S y) z = {!   !}

-- Attempt 2 (forgot ∎ , retrying)
-- mul-assoc x y Z = proof
--     (x * y) * Z
--       by {! !} equals
--     x * (y * Z)
-- mul-assoc x y (S z) = {!   !}

-- Attempt 1
-- mul-assoc Z y z = definition
-- mul-assoc (S x) y z = proof
--     ((S x) * y) * z
--       by {!  !} equals
--     (S x) * (y * z) ∎ 
  
