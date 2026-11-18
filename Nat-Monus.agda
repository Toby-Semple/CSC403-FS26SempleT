----------------------------------------
-- Agda Lab : Monus and Algorithms
----------------------------------------

-- Instructions
---------------
-- Complete the 21 numbered exercises by filling in the holes.
-- Later exercises may use earlier definitions and proofs.
-- Do not add postulates or disable termination or positivity checks.
--
-- C-c C-l : load the file       C-c C-f : next hole
-- C-c C-, : goal and context    C-c C-r : refine a hole
-- C-c C-c : case split; with empty input, introduce missing arguments
-- C-c C-n : normalize an expression
-- Type \dotminus for ∸, \bot for ⊥, \top for ⊤, and \qed for ∎.
-- Keep Equality.agda, Proofs-Answers.agda, and Proofs-Applied-Answers.agda
-- alongside this file. We use their completed prerequisite libraries.

module Nat-Monus where

open import Equality
open import Proofs-Answers
open import Proofs-Applied-Answers using
    (Nat; zero; succ; _+_; zero-add; add-zero; add-succ; add-comm; zero-ne-succ)

-- Supplied Unit 2 theorem: addition is associative.
add-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
add-assoc zero b c = refl
add-assoc (succ a) b c = cong succ (add-assoc a b c)

----------------------------------------
-- Predecessor and truncated subtraction
----------------------------------------

-- Ordinary subtraction is not closed on Nat: 3 - 5 would be negative.
-- MONUS is truncated subtraction: m ∸ n = max(m - n, 0).
-- It removes n successors from m, stopping at zero.
-- For example, 5 ∸ 3 = 2, whereas 3 ∸ 5 = 0.
-- Monus is neither commutative nor associative:
-- 5 ∸ 3 differs from 3 ∸ 5, and
-- (5 ∸ 3) ∸ 2 = 0 differs from 5 ∸ (3 ∸ 2) = 4.

-- Exercise 1 : Predecessor
-- The predecessor removes one successor. At zero, it stays at zero.
-- Split on n. Neither branch requires recursion.
pred : Nat → Nat
pred zero = zero
pred (succ n) = n

-- Exercise 2 : Predecessor of a successor
-- Once pred is complete, this equality follows by computation.
pred-succ : (n : Nat) → pred (succ n) ≡ n
pred-succ zero = refl
pred-succ (succ n) = refl

-- Exercise 3 : Recover successor injectivity using pred
-- Given succ m ≡ succ n, apply pred to both sides with cong.
-- Use your predecessor definition, not an imported injectivity theorem.
succ-inj-pred : {m n : Nat} → succ m ≡ succ n → m ≡ n
succ-inj-pred h = cong pred h

-- Exercise 4 : Define monus
-- Use these three equations:
-- m ∸ zero = m
-- zero ∸ succ n = zero
-- succ m ∸ succ n = m ∸ n
-- Split on n first, then on m when n is a successor. In the last case,
-- make a recursive call on the smaller arguments.
_∸_ : Nat → Nat → Nat
m ∸ zero = m
zero ∸ succ n = zero
succ m ∸ succ n = m ∸ n
infixl 6 _∸_

-- After completing monus, normalize 5 ∸ 3, 3 ∸ 5, and (5 ∸ 3) ∸ 2.
-- Like addition, monus computes on concrete constructors. For unknown
-- variables, we may need a case split or a theorem to justify a step.

-- Exercise 5 : Subtracting zero
monus-zero : (n : Nat) → n ∸ zero ≡ n
monus-zero n = refl

-- Exercise 6 : Subtracting from zero
-- Split on n so that monus can compute.
zero-monus : (n : Nat) → zero ∸ n ≡ zero
zero-monus zero = refl
zero-monus (succ n) = refl

-- Exercise 7 : Cancel a successor on both sides of monus
-- This is one of the defining equations, so computation should suffice.
succ-monus-succ : (m n : Nat) → succ m ∸ succ n ≡ m ∸ n
succ-monus-succ m n = refl

-- Exercise 8 : Monus by one is predecessor
-- Split on n to connect the two definitions.
monus-one : (n : Nat) → n ∸ 1 ≡ pred n
monus-one zero = refl
monus-one (succ n) = refl

-- Exercise 9 : Subtracting a number from itself
-- Split on n. In the successor case, use the recursive proof directly:
-- the two successors cancel without needing cong succ.
monus-self : (n : Nat) → n ∸ n ≡ zero
monus-self zero = refl
monus-self (succ n) = monus-self n

-- Exercise 10 : Undo addition with monus
-- Prove (m + n) ∸ n ≡ m by recursion on n.
-- In the zero case, use add-zero m.
-- In the successor case, rewrite m + succ n with add-succ under the
-- function λ t → t ∸ succ n, then cancel successors and recurse.
add-monus-right : (m n : Nat) → (m + n) ∸ n ≡ m
add-monus-right m zero = add-zero m
add-monus-right m (succ n)  = proof
    (m + succ n) ∸ succ n by cong (\ x → x ∸ succ n) (add-succ m n) equals
    succ (m + n) ∸ succ n by definition equals
    (m + n) ∸ n by add-monus-right m n equals
    m ∎

-- Exercise 11 : Subtracting a sum
-- Removing n, then p, has the same result as removing n + p at once.
-- This is a valid monus law; it does not assert associativity of monus.
-- The cases below align the recursive calls with the monus definition.
-- For m = zero and n = succ n, use zero-monus p.
monus-add : (m n p : Nat) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
monus-add m zero p = refl
monus-add zero (succ n) p = zero-monus p
monus-add (succ m) (succ n) p = monus-add m n p

----------------------------------------
-- Rearranging symbolic expressions
----------------------------------------

-- Computation can evaluate 20 + 20, but it cannot exchange arbitrary
-- variables a and b. For symbolic rearrangements, compose named proofs.

-- Exercise 12 : Exchange two adjacent summands
-- Use associativity backwards, commutativity inside the sum with c,
-- then associativity forwards. Complete the equality chain.
add-left-comm : (a b c : Nat) → a + (b + c) ≡ b + (a + c)
add-left-comm a b c = proof
    a + (b + c) by {! !} equals
    (a + b) + c by {! !} equals
    (b + a) + c by {! !} equals
    b + (a + c) ∎

-- Exercise 13 : Rearrange four summands
-- First associate to the right. Use add-left-comm to swap b and c,
-- then add-comm to swap b and d. Finally associate back to the left.
rearrange-four : (a b c d : Nat) → (a + b) + (c + d) ≡ ((a + c) + d) + b
rearrange-four a b c d = proof
    (a + b) + (c + d) by {! !} equals
    a + (b + (c + d)) by {! !} equals
    a + (c + (b + d)) by {! !} equals
    a + (c + (d + b)) by {! !} equals
    (a + c) + (d + b) by {! !} equals
    ((a + c) + d) + b ∎

----------------------------------------
-- Distinguishing constructors with evidence
----------------------------------------

-- The unit type represents a proposition with an immediate proof.
data ⊤ : Set where
    tt : ⊤

-- A type-valued zero test: its result is a proposition, not a Boolean.
-- Evidence for IsZero zero is tt. IsZero (succ n) has no evidence.
IsZero : Nat → Set
IsZero zero = ⊤
IsZero (succ n) = ⊥

-- Exercise 14 : A successor cannot be zero
-- Suppose h : succ n ≡ zero. Transport tt : IsZero zero backwards
-- along h with subst IsZero. The resulting type is IsZero (succ n),
-- which computes to ⊥. Practice this argument rather than an absurd
-- pattern or the previously proved zero-ne-succ theorem.
succ-ne-zero : (n : Nat) → succ n ≠ zero
succ-ne-zero n h = {! !}

-- Exercise 15 : Successors of unequal numbers are unequal
-- Introduce the supposed successor equality, apply succ-inj-pred, and
-- feed the resulting predecessor equality to not-equal.
-- This uses the constructive direction of contraposition.
succ-ne-succ : {m n : Nat} → m ≠ n → succ m ≠ succ n
succ-ne-succ not-equal h = {! !}

----------------------------------------
-- A verified equality algorithm
----------------------------------------

-- Recall Dec A from Proofs: yes contains a proof of A, and no contains
-- a refutation A → ⊥. Here we rebuild the Nat decision procedure using
-- the predecessor and refutation lemmas we have just proved.
-- Its recursive structure is also its correctness argument.

-- Exercise 16 : Decide equality of natural numbers
-- Use yes refl when both numbers are zero. For the mixed cases use
-- zero-ne-succ or succ-ne-zero. Compare predecessors recursively in the
-- last case: lift equality with cong succ, or use succ-ne-succ to lift
-- the refutation. Agda checks that the recursive arguments get smaller.
nat-equality : (m n : Nat) → Dec (m ≡ n)
nat-equality zero zero = {! !}
nat-equality zero (succ n) = {! !}
nat-equality (succ m) zero = {! !}
nat-equality (succ m) (succ n) with nat-equality m n
... | yes h = {! !}
... | no not-equal = {! !}

-- Normalize nat-equality 4 4 and nat-equality 4 5. Notice the proof or
-- refutation stored inside each result, rather than just true or false.

-- Exercise 17 : Decide a negation
-- Split on decision. If A has a proof, refute any proposed proof of ¬ A.
-- If A has a refutation, that refutation is already a proof of ¬ A.
dec-not : {A : Set} → Dec A → Dec (¬ A)
dec-not decision = {! !}

-- To use a decision as a proof, we must know it returned yes.
-- IsYes exposes that requirement as a type: ⊤ for yes, ⊥ for no.
IsYes : {A : Set} → Dec A → Set
IsYes (yes evidence) = ⊤
IsYes (no refutation) = ⊥

-- Exercise 18 : Extract a certified yes answer
-- Split on decision. In the yes branch, return the stored proof.
-- In the no branch, the second argument has type ⊥; eliminate it with
-- an absurd pattern. A Dec A alone cannot always supply a proof of A.
from-yes : {A : Set} → (decision : Dec A) → IsYes decision → A
from-yes decision certificate = {! !}

-- Worked example: the algorithm reduces to yes, so IsYes reduces to ⊤
-- and tt certifies the branch. from-yes extracts the equality proof.
three-monus-five : 3 ∸ 5 ≡ zero
three-monus-five = from-yes (nat-equality (3 ∸ 5) zero) tt

-- Exercise 19 : Certify a computed addition equality
-- Use from-yes with nat-equality and tt, as in the worked example.
-- refl also proves this closed equality by computation, but practice
-- obtaining evidence from the decision procedure here.
twenty-add-twenty : 20 + 20 ≡ 40
twenty-add-twenty = {! !}

-- Exercise 20 : Certify a computed inequality
-- Use nat-equality, then dec-not, then from-yes with tt.
-- This replaces the repeated successor cancellation used earlier.
two-add-two-ne-five-decided : (2 + 2) ≠ 5
two-add-two-ne-five-decided = {! !}

----------------------------------------
-- BOSS BATTLE : Certified monus calculations
----------------------------------------

-- Exercise 21 : Compute and certify both answers
-- Build a pair of proofs with pair. Use the equality algorithm and
-- from-yes to prove that (20 + 20) ∸ 21 is 19, and use dec-not to prove
-- that the same expression is not 20. Monus must stop at the right result,
-- and the decisions must carry evidence for both claims.
-- When a decision returns no, its required certificate type is ⊥
-- instead of ⊤, so Agda rejects tt.
monus-boss : (((20 + 20) ∸ 21) ≡ 19) × (((20 + 20) ∸ 21) ≠ 20)
monus-boss = pair {! !} {! !}

-- Reflection: Why is m ∸ n + n ≡ m false for arbitrary m and n, even
-- though (m + n) ∸ n ≡ m is true? Give a counterexample.
-- Which proofs needed induction, and which evaluated closed expressions?
-- Why does implementing Dec (m ≡ n) avoid assuming general LEM?

-- Selected exercise progression adapted from Algorithm World:
-- https://github.com/leanprover-community/NNG4/tree/main/Game/Levels/Algorithm
