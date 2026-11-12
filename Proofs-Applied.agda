----------------------------------------
-- Agda Lab : Applied Proofs
----------------------------------------

-- Complete the numbered exercises by filling in the holes.
-- Use C-c C-, to inspect the goal/context and C-c C-c to split on a
-- variable or, with empty input, to introduce missing arguments.
-- Earlier proofs may be used in later exercises. Do not add postulates
-- or disable termination or positivity checks.
-- The completed introductory library supplies the logical proof tools.

module Proofs-Applied where

open import Equality
open import Proofs-Answers

-- Supplied Unit 2 prerequisites (not exercises).
data Nat : Set where
    zero : Nat
    succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + n = n
succ m + n = succ (m + n)
infixl 6 _+_

_*_ : Nat → Nat → Nat
zero * n = zero
succ m * n = n + (m * n)
infixl 7 _*_

zero-add : (n : Nat) → zero + n ≡ n
zero-add n = refl

add-zero : (n : Nat) → n + zero ≡ n
add-zero zero = refl
add-zero (succ n) = cong succ (add-zero n)

add-succ : (m n : Nat) → m + succ n ≡ succ (m + n)
add-succ zero n = refl
add-succ (succ m) n = cong succ (add-succ m n)


-- Supplied Unit 2 theorem: addition is commutative.
add-comm : (m n : Nat) → m + n ≡ n + m
add-comm zero n = sym (add-zero n)
add-comm (succ m) n = trans (cong succ (add-comm m n)) (sym (add-succ n m))
----------------------------------------
-- Implication and equality
----------------------------------------

-- Exercise 1 : using a hypothesis
-- Identify the hypothesis with the required type. You do not need h2.
-- Strictly speaking this is returning a hypothesis, not modus ponens.
-- The arrows in the signature express implications; a proof is a function
-- accepting those hypotheses. There is no need for an `exact` tactic:
-- put a term of the required type in the hole.
use-hypothesis : (x y z : Nat) → x + y ≡ 37 → 3 * x + z ≡ 42 → x + y ≡ 37
use-hypothesis x y z h1 h2 = h1

-- Exercise 2 : additional modus ponens practice
-- h2 is a function from the type of h1 to
-- the goal type. Apply it directly, or use modus-ponens.
equation-modus-ponens : (x y : Nat) → x ≡ 37 → (x ≡ 37 → y ≡ 42) → y ≡ 42
equation-modus-ponens x y h1 h2 = h2 h1

-- Exercise 3 : Substitution with an equality chain
-- Recall subst from Equality.agda:
-- subst C : x ≡ y → C x → C y, where C is a family of proposition types.
-- Equal expressions can replace one another inside a proposition.
-- Complete the reasons in the chain below: use zero-add x backwards,
-- then the hypothesis h, then replace 0 + y with y inside addition.
-- For the last step, use cong or subst from Equality.agda.
-- With subst, take C = λ t → (0 + y) + 2 ≡ t + 2 and transport refl
-- along zero-add y. Our addition also makes these zero-add steps hold
-- by definition, but practice using the named equality proofs here.
substitution : (x y : Nat) → 0 + x ≡ (0 + y) + 2 → x ≡ y + 2
substitution x y h = proof
    x by refl equals
    0 + x by h equals
    (0 + y) + 2 by refl equals
    y + 2 ∎

-- Exercise 4 : Successor injectivity
-- This theorem was not proved in our Unit 2 Nat labs.
-- Split on h : succ x ≡ succ y. Its only constructor is refl; Agda
-- identifies the predecessor indices, leaving a reflexive equality.
succ-inj : {x y : Nat} → succ x ≡ succ y → x ≡ y
succ-inj refl = refl

-- Exercise 5 : Successor equals addition by one
-- Use add-succ n 0 and add-zero n, with sym/cong/trans or an equality chain.
-- n + 1 does not reduce to succ n for an unknown n, since addition
-- recurses on its first argument. We need a theorem, not just refl.
succ-eq-add-one : (n : Nat) → succ n ≡ n + 1
succ-eq-add-one zero = refl
succ-eq-add-one (succ n) = proof 
   succ (succ n) by cong succ (succ-eq-add-one n) 
   equals succ n + 1 ∎

-- Exercise 6 : use successor injectivity
-- Transform h into succ x ≡ succ 3, then apply succ-inj.
-- 4 and succ 3 are definitionally equal: no numeral rewrite is needed.
add-one-eq-four : (x : Nat) → x + 1 ≡ 4 → x ≡ 3
add-one-eq-four x h = succ-inj (trans (succ-eq-add-one x) h)

-- Exercise 7 : reason backwards with an equality chain
-- succ-inj reduces the goal to succ x ≡ succ 3. Complete the reasons
-- in the supplied proof/by/equals structure.
add-one-eq-four-chain : (x : Nat) → x + 1 ≡ 4 → x ≡ 3
add-one-eq-four-chain x h = succ-inj (proof
    succ x by succ-eq-add-one x equals
    x + 1 by h equals
    4 by refl equals
    succ 3 ∎)

-- Exercise 8 : introduce an assumption
-- The proof argument is intentionally missing from the left-hand side.
-- In the hole, use C-c C-c with EMPTY input to introduce it. This should
-- produce a clause such as intro-equality x h = ... with h : x ≡ 37.
-- Inspect the new context, then use h. A lambda also proves implication,
-- but practice the editor's argument-introduction command here.
intro-equality : (x : Nat) → x ≡ 37 → x ≡ 37
intro-equality x h = h

-- Exercise 9 : introduce and cancel
-- Again use C-c C-c with empty input to introduce the missing proof.
-- Chain succ-eq-add-one x, the hypothesis, and sym (succ-eq-add-one y),
-- then apply succ-inj.
cancel-add-one : (x y : Nat) → x + 1 ≡ y + 1 → x ≡ y
cancel-add-one x y h = succ-inj (trans (succ-eq-add-one x) (trans h (sym (succ-eq-add-one y))) )

succ-convert : (x : Nat) → succ x ≡ x + 1
succ-convert x = trans (cong succ (sym(add-zero x))) (sym (add-succ x zero)) 

cancel-succ-one : (x y : Nat) → succ x ≡ succ y → x ≡ y
cancel-succ-one x y refl = refl


-- cancel-add-one x y (cong (λ x₁ → {!   !}) {!   !})
----------------------------------------
-- Contradictions and inequalities
----------------------------------------

-- Exercise 10 : contradictory equalities
-- Treat h2 as a function, just as in modus ponens.
equality-contradiction : (x y : Nat) → x ≡ y → x ≠ y → ⊥
equality-contradiction x y h1 h2 = h2 h1

-- Exercise 11 : Apply explosion to the same hypotheses
-- Use equality-contradiction to obtain ⊥ and ex-falso to obtain A.
equality-explosion : {A : Set} → (x y : Nat) → x ≡ y → x ≠ y → A
equality-explosion x y h1 h2 = ex-falso (h2 h1)

-- Exercise 12 : zero is not a successor
-- Prove that zero differs from every successor.
-- Introduce the equality argument, then split on it. zero and succ n are
-- different constructors, so refl is impossible: use an absurd clause.
zero-ne-succ : (n : Nat) → zero ≠ succ n
zero-ne-succ zero = λ ()
zero-ne-succ (succ n) = λ ()

-- Exercise 13 : 0 ≠ 1
-- Specialize zero-ne-succ. Numerals reduce to zero/succ automatically.
zero-ne-one : _≠_ {A = Nat} 0 1
zero-ne-one = λ ()

-- Exercise 14 : 1 ≠ 0
-- Introduce h : 1 ≡ 0, use sym, then apply zero-ne-one.
one-ne-zero : _≠_ {A = Nat} 1 0
one-ne-zero = λ ()

----------------------------------------
-- Deciding natural-number equality
----------------------------------------

-- Exercise 15 : Decide equality of natural numbers
-- The first three cases use refl, zero-ne-succ, and symmetry.
-- The successor case compares the smaller numbers recursively.
-- If they are equal, lift with cong succ. If not, refute equality of
-- their successors using succ-inj. All five branches require proof evidence.
nat-equality : (m n : Nat) → Dec (m ≡ n)
nat-equality zero zero = yes refl
nat-equality zero (succ n) = no λ ()
nat-equality (succ m) zero = no ( λ x → zero-ne-succ m (sym x) )
nat-equality (succ m) (succ n) with nat-equality m n
... | yes h = yes (cong succ h)
... | no not-equal = no (λ x → equality-explosion m n (cancel-succ-one m n x) not-equal )

-- Once completed, normalize nat-equality 4 4 and nat-equality 4 5.
-- What evidence does each answer contain? Why does this algorithm not
-- solve the earlier excluded-middle experiment for every A : Set?

----------------------------------------
-- Cancellation and zero summands
----------------------------------------

-- Exercise 16 : Cancel addition on the right
-- Prove that adding the same n to both sides preserves enough information
-- to recover a ≡ b. Split on n and use recursion on the smaller n.
-- In the zero case use add-zero to connect the hypothesis to the goal.
-- In the successor case use add-succ on both sides, then succ-inj,
-- then the recursive proof. Equality chains can make these steps explicit.

-- cong-rev : {A B : Set} → {x y : A} → (f : A → B) → f x ≡ f y → x ≡ y
-- cong-rev f p =
-- not true becasue if f = const 0, then cong-rev f 1 = f 2 is false.

add-right-cancel : (a b n : Nat) → a + n ≡ b + n → a ≡ b
add-right-cancel a b zero  = λ x → trans (sym (add-zero a)) (trans x (add-zero b))
add-right-cancel a b (succ n) = λ x → add-right-cancel a b n (succ-inj (trans (sym (add-succ a n)) (trans x (add-succ b n))))
-- λ x → (trans {! add-succ a n  !} (trans ((cong (λ x₁ → succ x₁) {!   !})) {!   !}) )


-- Exercise 17 : Cancel addition on the left
-- Use add-comm on both sides of the hypothesis and add-right-cancel.
-- Alternatively, split on n and recursively cancel the leading successors.
add-left-cancel : (a b n : Nat) → n + a ≡ n + b → a ≡ b
add-left-cancel a b n = λ x → add-right-cancel a b n  ( trans (sym (add-comm n a)) (trans x (sym (add-comm b n))) )

-- Exercise 18 : A sum equal to its right summand
-- If x + y ≡ y, then x must be zero. View the right-hand y as 0 + y,
-- and use add-right-cancel. Here 0 + y reduces to y by definition.
add-left-eq-self : (x y : Nat) → x + y ≡ y → x ≡ zero
add-left-eq-self x y = add-right-cancel x 0 y

-- Exercise 19 : A sum equal to its left summand
-- If x + y ≡ x, then y must be zero. Turn the right-hand x into x + 0
-- using add-zero backwards and use add-left-cancel. Another approach
-- uses add-comm and add-left-eq-self.
add-right-eq-self : (x y : Nat) → x + y ≡ x → y ≡ zero
add-right-eq-self x y = λ g → add-left-cancel y 0 x (trans g (sym (add-zero x)))

-- Exercise 20 : A zero sum has a zero left summand
-- Split on b. When b is zero, use add-zero a and the hypothesis.
-- When b is a successor, add-succ turns the sum into a successor.
-- Use zero-ne-succ (after reversing the equality), then ex-falso.
-- A case split alone suffices here: neither case requires recursion.
add-right-eq-zero : (a b : Nat) → a + b ≡ zero → a ≡ zero
add-right-eq-zero a zero = λ h → add-right-cancel a zero zero (trans h (add-zero zero))
add-right-eq-zero a (succ b) = λ x → ex-falso( zero-ne-succ(a + b) (sym (trans (sym (add-succ a b)) x)))

-- Exercise 21 : A zero sum has a zero right summand
-- Use add-comm to exchange a and b, then apply add-right-eq-zero.
-- Together these last two results give both parts of
-- (a ≡ zero) × (b ≡ zero) whenever a + b ≡ zero.
add-left-eq-zero : (a b : Nat) → a + b ≡ zero → b ≡ zero
add-left-eq-zero a b = λ x →  add-right-eq-zero b a (trans (sym (add-comm a b)) x)

-- Reflection: Where did you need recursion, and where was a case split
-- enough? How did the implication proofs become functions on equalities?

----------------------------------------
-- BOSS BATTLE : 2 + 2 ≠ 5
----------------------------------------

-- Exercise 22 : Prove the inequality using the earlier proof tools
-- Introduce the supposed equality h. Addition and numerals compute, so
-- h has type succ (succ (succ (succ zero))) ≡
--            succ (succ (succ (succ (succ zero)))).
-- Apply succ-inj four times, then apply zero-ne-succ.
-- For this exercise, practice that argument instead of using nat-equality
-- or immediately pattern matching on the original impossible equality.
two-add-two-ne-five : (2 + 2) ≠ 5
two-add-two-ne-five = λ x → zero-ne-succ 0 (succ-inj (succ-inj (succ-inj (succ-inj x))))

-- Reflection: Which steps are function application (modus ponens)? Which
-- introduce an assumption? Which equalities hold by computation?
-- How could nat-equality help automate larger numeral inequalities?

-- Exercise progression adapted from the Natural Number Game:
-- https://github.com/leanprover-community/NNG4/tree/main/Game/Levels/Implication
-- https://github.com/leanprover-community/NNG4/tree/main/Game/Levels/AdvAddition