----------------------------------------
-- Agda Lab 2 : The Natural Numbers Part 1 Solutions
---------------------------------------- 

-- Instructions
---------------
-- Complete the following file by filling in the "holes". There are 9
-- holes, and each of them is a homework problem. There is also a final boss problem. Some holes can't be
-- filled until you have completed earlier ones.
--
-- Hint: If you place the cursor in any hole by typing C-c C-f (Control-c followed by Control-f),
-- you can type C-c C-, (Control-c followed by Control-comma) to see the type of the hole,
-- i.e., the proposition you have to prove or the type of the
-- expression you have to write. Moreover, C-c C-, also shows you the
-- current context, i.e., what the types of the relevant variables
-- are.
-- 
-- If you are using Agda Mode for VS Code, viewing the extension page will show you a list of 
-- hotkeys for interacting with Agda. Some important ones are below. The capital C in each command
-- means the Control key. 
-- C-c C-l (load the file)
-- C-c C-f (forward to next hole)
-- C-c C-b (back to previous hole)
-- C-c C-, (see the type of the hole)
-- C-c C-r (refine a hole)
-- C-c C-c (case split on given variable in hole)

open import Equality 
module Nat-Add-Answers where 

-- The Peano Axioms are axioms to define the Natural Numbers ℕ (type \bN to get Blackboard script N) 
-- The original axioms from 19th century mathematician Giuseppe Peano included axioms that we 
-- actually use to describe properties of equality (reflexivity, symmetry, transitivity), but the ones
-- that matter are how we define the Naturals in Agda

data Nat : Set where 
    zero : Nat       -- zero is a natural number 
    succ : Nat → Nat -- for every natural number n, S(n) is a natural number. (The "successor" function.)  

-- Using this definition of the Natural Numbers and Agda's pattern matching and recursion, we will prove
-- the remaining axioms as theorems. But first we have some ground work to lay. 

-------------------------- 
-- Some Basic Constants --
--------------------------

-- Identifying our definition of Nat with the built-in Naturals will allow us to take advantage of machine 
-- efficient representations of positive whole numbers.
{-# BUILTIN NATURAL Nat #-}

-- Fill in the definitions of three and four.
one : Nat 
one = succ zero 

two : Nat 
two = succ (succ zero) 

also-two : Nat 
also-two = succ one 

three : Nat 
three = succ two
four : Nat 
four = succ three

-- writing out zero and succ can sometimes get annoying during proofs
-- so this syntax lets us define synonyms
pattern Z = zero 
pattern S n = succ n

-- try C-c C-n and type in succ zero to see that Agda will resolve it to 1
-- comment out {-# BUILTIN NATURAL Nat #-} in the above line to see that without 
-- invoking built in, Agda just sees succ zero as succ zero. So we do not actually
-- have to define every single natural number we want to use like we would above,
-- but instead just type the numeral as normal. (Make sure you uncomment the BUILTIN pragma after checking!) 

--------------------------------
-- Addition on Natural Numbers
-------------------------------- 

-- Addition is defined recursively 
-- pattern match on x 
add : Nat → Nat → Nat 
add Z y = y
add (S x) y = S (add x y)

-- infix notation for convenience 
_+_ : Nat → Nat → Nat 
x + y = add x y 

infixl 6 _+_  

-- Zero is of course the identity for addition in the natural numbers. Let's prove it. 

-- Zero added on the left 
-- Agda can resolve this one itself because we pattern matched on the left-hand argument 
zero-add : (n : Nat) → zero + n ≡ n 
zero-add Z = refl
zero-add (S n) = refl 

-- Zero added on the right 
-- This is our first 'non-trivial' proof that can't just be resolved with pattern-matching and refl
-- The proof uses 'cong' from the Equality file, which takes two arguments: a function
-- f : A -> B, and a proof that x ≡ y.  It produces a proof of f x ≡ f y.
add-zero : (n : Nat) → n + zero ≡ n 
add-zero Z = refl
add-zero (S n) = cong succ (add-zero n) 

-- Let's take a moment to understand how add-zero-right works to produce a proof that 
-- n + zero ≡ n for any n : Nat  

-- add-zero-right 4 
-- ≡ add-zero-right (S (S (S (S Z))))
-- ≡ cong succ (add-zero-right (S (S (S Z)))) 
-- ≡ cong succ (cong succ (add-zero-right (S (S Z))))
-- ≡ cong succ (cong succ (cong succ (add-zero-right (S Z)))) 
-- ≡ cong succ (cong succ (cong succ (cong succ (add-zero-right Z))))
-- ≡ cong succ (cong succ (cong succ (cong succ ("proof Z ≡ Z" which is refl))))
-- ≡ cong succ (cong succ (cong succ ("proof of S Z ≡ S Z" which is refl)))
-- ≡ cong succ (cong succ ("proof of S (S Z) ≡ S (S Z)" which is refl))
-- ≡ cong succ ("proof of S (S (S Z)) ≡ S (S (S Z))" which is refl)
-- ≡ "proof of S (S (S (S Z))) ≡ S (S (S (S Z)))" which is refl
-- ≡ "proof of 4 + zero ≡ 4"

-- The recursive call gives us a proof that n + zero ≡ n. Applying cong succ to
-- that proof puts S around both sides, giving a proof that S (n + zero) ≡ S n.
-- Since addition pattern matches on its left argument, S n + zero reduces to
-- S (n + zero), so this is exactly the proof required in the successor case.
-- Each recursive call removes one S until reaching Z; then the resulting refl
-- proof is carried back through the same number of applications of cong succ. 

-- Since we use the successor function so often (because it is in the definition of Nat)
-- we can specialize our cong succ to two theorems.

-- Agda resolves this one automatically by definition (that is, refl)
succ-add : (x y : Nat) → S x + y ≡ S (x + y) 
succ-add x y = definition 

-- The other direction requires a little work, but not much.
-- We need to use cong and a recursive call to add-succ after pattern matching on x 
add-succ : (x y : Nat) → x + S y ≡ S (x + y) 
add-succ Z y = refl
add-succ (S x) y = cong succ (add-succ x y)

-- BOSS BATTLE
-- Now we should be able to prove that addition is commutative and associative 

-- Addition is commutative 
-- Pattern match on x and then use recursion 
-- You will need to use sym, trans, and cong from the Equality.agda file
add-comm : (x y : Nat) → x + y ≡ y + x 
add-comm Z y = sym (add-zero y)
add-comm (S x) y = trans (cong succ (add-comm x y)) (sym (add-succ y x))

-- Here is the same proof written out as an equality chain. This version makes
-- the definitional reductions and the use of the recursive hypothesis visible.
-- It can be uncommented and used as an alternative implementation.
--
-- add-comm-expanded : (x y : Nat) → x + y ≡ y + x
-- add-comm-expanded Z y = proof
--     Z + y by zero-add y equals
--     y by sym (add-zero y) equals
--     y + Z ∎
-- add-comm-expanded (S x) y = proof
--     S x + y by refl equals
--     S (x + y) by cong succ (add-comm-expanded x y) equals
--     S (y + x) by sym (add-succ y x) equals
--     y + S x ∎

-- Addition is Associative 
-- Pattern match on x and then use recursion 
-- We will need to use cong
add-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z) 
add-assoc Z y z = refl
add-assoc (S x) y z = cong succ (add-assoc x y z)

-- Here is the same proof written out as an equality chain. The refl steps show
-- where addition reduces by definition, while the cong step shows where the
-- recursive hypothesis is lifted through S.
-- It can be uncommented and used as an alternative implementation.
--
-- add-assoc-expanded : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
-- add-assoc-expanded Z y z = proof
--     (Z + y) + z by refl equals
--     y + z by refl equals
--     Z + (y + z) ∎
-- add-assoc-expanded (S x) y z = proof
--     (S x + y) + z by refl equals
--     S ((x + y) + z) by cong succ (add-assoc-expanded x y z) equals
--     S (x + (y + z)) by refl equals
--     S x + (y + z) ∎

-- Let's try write an equality that uses both associativity and commutativity 
add-right-comm : (x y z : Nat) → (x + y) + z ≡ (x + z) + y 
add-right-comm Z y z = cong (λ x → Z + x) (add-comm y z)
add-right-comm (S x) y z = cong succ (add-right-comm x y z)


