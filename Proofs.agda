----------------------------------------
-- Agda Lab : Introduction to Proofs
----------------------------------------

-- Instructions
---------------
-- Complete the numbered exercises by filling in the holes. Some exercises
-- have several holes; later exercises may use your earlier proofs.
-- The commented LEM/DNE experiments are discussion prompts, not holes to submit.
-- Do not add postulates or disable Agda's termination or positivity checks.
--
-- C-c C-l : load the file       C-c C-f : next hole
-- C-c C-, : goal and context    C-c C-r : refine a hole
-- C-c C-c : case split; with an empty input, introduce missing arguments
-- C-c C-n : normalize an expression
-- Unicode input: \bot gives ⊥, \neg gives ¬, \times gives ×,
-- \uplus gives ⊎, \== gives ≡, \ne gives ≠, and \qed gives ∎.

module Proofs where

open import Equality

----------------------------------------
-- Empty types and logical negation
----------------------------------------

-- An empty type has no constructors. A value of ⊥ would be a contradiction.
data ⊥ : Set where

-- Logical negation is a function that turns any proposed proof of A into
-- a contradiction. It is different from a function that flips a Boolean.
¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_

-- Exercise 1 : Contradiction
-- Given proofs of A and NOT A, apply the latter to the former.
-- not A is the same thing as A → 𝕠t
contradiction : {A : Set} → A → ¬ A → ⊥
contradiction a not-a = not-a a

-- Exercise 2 : Double-negation introduction
-- Given a : A, show that any supposed proof of ¬ A leads to ⊥.
double-negation-intro : {A : Set} → A → ¬ (¬ A)
double-negation-intro a not-a = not-a a

-- double-negation-other-way : {A : Set} → A → ¬ (¬ A)
-- double-negation-other way not-not-a = nothing

-- We need an OR type to state the law of excluded middle (LEM).
-- A proof of A OR B must contain a proof of one particular side.
data _⊎_ (A B : Set) : Set where
    left  : A → A ⊎ B
    right : B → A ⊎ B
infixr 4 _⊎_

-- Constructive/intuitionistic type theory requires proof objects. For an
-- arbitrary A we have no algorithm that always produces either a proof of A
-- or a function A → ⊥. Likewise, a function (A → ⊥) → ⊥ does not in general
-- supply a value of A. Plain Agda does not prove these classical principles.
-- This is not a proof of their negations: we may study them as assumptions.
--
-- Discussion experiment (temporarily uncomment ONE declaration, inspect its
-- goal/context, and then comment it out again before submitting):
-- excluded-middle : (A : Set) → A ⊎ (¬ A)
-- excluded-middle A = {! !}
--
-- double-negation-elim : (A : Set) → ¬ (¬ A) → A
-- double-negation-elim A not-not-a = {! !}
--
-- Why can double-negation-intro be completed, but neither experiment has a
-- general constructive implementation? What evidence is missing in each?

-- Exercise 3 : A constructive double-negation elimination for negations
-- Unlike arbitrary A, a negated proposition is stable under double negation.
-- It may help to remember: NOT A means A IMPLIES FALSE, or A → ⊥.
-- Expanding every negation, the type below is:
-- {A : Set} → (((A → ⊥) → ⊥) → ⊥) → (A → ⊥)
-- Introduce a : A and build ¬ (¬ A) using Exercise 2.
triple-negation-elim : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
triple-negation-elim not-not-not-a a = not-not-not-a (double-negation-intro a)

-- Exercise 4 : The double negation of LEM
-- We can prove ¬ ¬ (A OR ¬ A) without choosing a side of that OR!
-- It may help to remember: NOT A means A IMPLIES FALSE, or A → ⊥.
-- Expanding every negation, the type below is:
-- (A : Set) → ((A ⊎ (A → ⊥)) → ⊥) → ⊥
-- If reject refutes the OR, it refutes left a for each a : A.
-- Use that function as evidence for the right branch, then apply reject.
double-negated-lem : (A : Set) → ¬ (¬ (A ⊎ (¬ A)))
double-negated-lem A reject = reject (right (λ z → reject (left z)))

----------------------------------------
-- Currying and the Curry-Howard correspondence
----------------------------------------

-- A product type is an ordered pair 
data _×_ (A B : Set) : Set where
    pair : A → B → A × B
infixr 5 _×_

-- Exercise 5 : Currying
-- Turn a function on pairs into a function taking one argument at a time.
curry : {A B C : Set} → (A × B → C) → A → B → C
curry f a b = {! !}

-- Exercise 6 : Uncurrying
-- Turn a curried function into a function on pairs. Split on ab.
uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f ab = {! !}

-- Exercise 7 : Uncurry after curry
-- Start with a function on pairs. Currying and then uncurrying it should
-- give the same result as the original function on every input.
-- Split on ab so that uncurry can compute, then prove the equality.
uncurry-curry : {A B C : Set} → (f : A × B → C) → (ab : A × B) →
                uncurry (curry f) ab ≡ f ab
uncurry-curry f ab = {! !}

-- Exercise 8 : Curry after uncurry
-- Start with a curried function and apply both conversions in the other
-- order. Normalize the left-hand side: what happens to the pair?
curry-uncurry : {A B C : Set} → (f : A → B → C) → (a : A) → (b : B) →
                curry (uncurry f) a b ≡ f a b
curry-uncurry f a b = {! !}

-- These equalities compare results on each input (pointwise equality).
-- We do not need an axiom saying that functions equal on all inputs are
-- themselves propositionally equal (function extensionality).

-- Curry-Howard: propositions correspond to types, and proofs to terms.
--
-- Logical connective       ITT proof counterpart
-- A IMPLIES B              A → B          (a function)
-- A AND B                  A × B          (a pair of proofs)
-- A OR B                   A ⊎ B          (a tagged proof of one side)
-- NOT A                    A → ⊥          (a refutation)
--
-- These are constructive interpretations of the connectives used in
-- classical logic; LEM and double-negation elimination do not come for free.
-- A → B → C means A → (B → C). Currying identifies the evidence needed
-- for (A AND B) IMPLIES C with that needed for A IMPLIES (B IMPLIES C).

-- Exercise 9 : Implication elimination (modus ponens)
-- From A IMPLIES B and A, derive B by function application.
modus-ponens : {A B : Set} → (A → B) → A → B
modus-ponens f a = {! !}

-- Exercise 10 : AND introduction
and-intro : {A B : Set} → A → B → A × B
and-intro a b = {! !}

-- Exercise 11 : AND elimination
-- Split on evidence to extract the proof of A.
and-left : {A B : Set} → A × B → A
and-left evidence = {! !}

-- Exercise 12 : AND elimination on the right
-- Split on evidence to extract the proof of B.
and-right : {A B : Set} → A × B → B
and-right evidence = {! !}

-- Exercise 13 : OR introduction
or-right : {A B : Set} → B → A ⊎ B
or-right b = {! !}

-- Exercise 14 : OR introduction on the left
-- Use the left constructor to supply evidence for the A branch.
or-left : {A B : Set} → A → A ⊎ B
or-left a = {! !}

-- Exercise 15 : OR elimination (proof by cases)
-- Split on evidence. In each branch, use the appropriate implication.
or-elim : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
or-elim from-a from-b evidence = {! !}

-- Exercise 16 : NOT and implication (contraposition)
-- Given A → B and ¬ B, construct ¬ A. This direction is constructive.
-- The converse is not available in general in constructive logic:
-- from ¬ B → ¬ A, we cannot generally recover A → B.
-- Given a : A, the converse hypothesis lets us refute every proposed
-- proof of ¬ B, yielding ¬ (¬ B). To obtain B from that requires
-- double-negation elimination for B (for example, if B is decidable).
-- Classical logic allows this extra step, so contraposition is an
-- equivalence there. Plain Agda proves only the forward direction in general.
contrapositive : {A B : Set} → (A → B) → ¬ B → ¬ A
contrapositive implies not-b a = {! !}


----------------------------------------
-- Explosion and decidable propositions
----------------------------------------

-- Exercise 17 : Ex falso (the principle of explosion)
-- From a contradiction, any proposition follows. Split on impossible.
-- There are no constructors to handle; Agda writes the absurd pattern ().
-- An absurd clause has no right-hand side. This is elimination of the
-- empty type, not a way to create an actual contradiction.
ex-falso : {A : Set} → ⊥ → A
ex-falso impossible = {! !}

-- Exercise 18 : LEM implies double-negation elimination for a given A
-- Revisit the earlier discussion: suppose someone supplies A OR ¬ A.
-- Split on choice. Return the A proof in one branch; in the other branch,
-- apply not-not-a to the refutation and eliminate the resulting ⊥.
lem-implies-dne : {A : Set} → A ⊎ (¬ A) → ¬ (¬ A) → A
lem-implies-dne choice not-not-a = {! !}

-- Inequality is a refutation of equality, not a Boolean comparison.
_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)
infix 4 _≠_

-- A decision carries evidence: either a proof or a refutation.
-- This is more informative than returning true or false.
data Dec (A : Set) : Set where
    yes : A → Dec A
    no  : ¬ A → Dec A

----------------------------------------
-- BOSS BATTLE : Decidable propositions satisfy LEM
----------------------------------------

-- Exercise 19 : Decidable propositions satisfy LEM
-- Split on decision and convert its evidence to the appropriate OR branch.
-- This gives LEM for propositions with a decision, not for arbitrary types.
decidable-lem : {A : Set} → Dec A → A ⊎ (¬ A)
decidable-lem decision = {! !}

-- Reflection: What evidence do functions, pairs, and tagged alternatives
-- carry? Why does a decision for a proposition allow classical reasoning
-- about that proposition without deciding every proposition?
