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
      by {!   !} equals
    x * (y + z)
      -- Use mul-add.
      by {!   !} equals
    (x * y) + (x * z)
      -- Use cong and mul-comm to swap the first product.
      by {!   !} equals
    (y * x) + (x * z)
      -- Use cong and mul-comm to swap the second product.
      by {!   !} equals
    (y * x) + (z * x) ∎ 

-- Boss Battle 
-- Multiplication of the Naturals is Associative 
mul-assoc : (x y z : Nat) → x * y * z ≡ x * (y * z) 
mul-assoc x y z = proof
    {!   !}
      by {!   !} equals
    {!   !} ∎
  
