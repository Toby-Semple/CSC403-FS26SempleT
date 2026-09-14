----------------------------------------
-- Agda Lab 2 : The Natural Numbers Part 1
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
module Nat where 

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

-- Writing out zero and succ can sometimes get annoying during proofs,
-- so this syntax lets us define synonyms.
pattern Z = zero 
pattern S n = succ n

-- Try C-c C-n and type in succ zero to see that Agda will resolve it to 1
-- comment out {-# BUILTIN NATURAL Nat #-} in the above line to see that without 
-- invoking built in, Agda just sees succ zero as succ zero. So we do not actually
-- have to define every single natural number we want to use like we would above,
-- but instead just type the numeral as normal. (Make sure you uncomment the BUILTIN pragma after checking!) 

--------------------------------
-- Addition on Natural Numbers
-------------------------------- 

-- Addition is defined recursively 
-- patten match on x 
add : Nat → Nat → Nat 
add Z y = y
add (S x) y = S (add x y)
-- add Z y = y x is either zero, or it came after some other natural number
-- add (S x) y = S (add x y) -- 

-- infix notation for convenience 
_+_ : Nat → Nat → Nat 
x + y = add x y 

infixl 6 _+_  

-- Zero is of course the identity for addition in the natural numbers. Let's prove it. 

-- Zero added on the left 
-- Agda can resolve this one itself because we pattern matched on the left-hand argument 
zero-add : (n : Nat) → zero + n ≡ n 
zero-add n = refl

-- Zero added on the right 
-- This is our first 'non-trivial' proof that can't just be resolved with pattern-matching and refl
-- The proof uses 'cong' from the Equality file, which takes two arguments: a function
-- f : A -> B, and a proof that x ≡ y.  It produces a proof of f x ≡ f y.
add-zero : (n : Nat) → n + zero ≡ n 
add-zero Z = refl
add-zero (S n) = cong S (add-zero n)

-- Agda resolves this one automatically by definition (that is, refl)
succ-add : (x y : Nat) → S x + y ≡ S (x + y) 
succ-add x y = definition 

-- The other direction requires a little work, but not much.
-- We need to use cong and a recursive call to add-succ after pattern matching on x 
add-succ : (x y : Nat) → x + S y ≡ S (x + y) 
add-succ Z y = refl
add-succ (S x) y = cong S (add-succ x y)


-- BOSS BATTLE 
-- Now we should be able to prove that addition is commutative and associative 

-- Addition is commutative 
-- Pattern match on x and then use recursion 
-- You will need to use sym, trans, and cong from the Equality.agda file
add-comm : (x y : Nat) → x + y ≡ y + x 
add-comm x = {!   !}

-- Addition is Associative 
-- Pattern match on x and then use recursion 
-- We will need to use cong
add-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z) 
add-assoc = {! !}

-- Let's try to write an equality that uses both associativity and commutativity 
add-right-comm : (x y z : Nat) → (x + y) + z ≡ (x + z) + y 
add-right-comm = {! !}


