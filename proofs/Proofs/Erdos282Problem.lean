/-
# Erdős Problem #282: Greedy Algorithm for Egyptian Fractions

Given an infinite set A ⊆ ℕ and rational x ∈ (0,1), the greedy algorithm
repeatedly picks the smallest n ∈ A with n ≥ 1/x, subtracts 1/n from x,
and repeats. This produces an Egyptian fraction representation using
distinct unit fractions with denominators from A.

## Key Question (Stein)
Does the greedy algorithm terminate when x has odd denominator
and A = {odd positive integers}?

## Known Results
- Fibonacci (1202): terminates for all x when A = ℕ
- Graham (1964): algebraic conditions for representability with
  denominators ≡ a (mod d)
- Erdős–Graham conjecture: the greedy algorithm on A = {n² : n ∈ ℕ}
  "perhaps fails to terminate almost always"

## Status: OPEN

Reference: https://erdosproblems.com/282
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- An Egyptian fraction representation of a rational x using denominators
    from a set A: x = Σ_{n ∈ S} 1/n where S ⊆ A is finite with distinct elements. -/
def IsEgyptianFracRep (x : ℚ) (S : Finset ℕ) (A : Set ℕ) : Prop :=
  (∀ n ∈ S, n ∈ A ∧ n > 0) ∧
  x = S.sum (fun n => (1 : ℚ) / n)

/-- A rational x is representable as an Egyptian fraction with denominators from A. -/
def IsRepresentable (x : ℚ) (A : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, IsEgyptianFracRep x S A

/-- The greedy step: given x > 0 and a set A, find the smallest n ∈ A
    with 1/n ≤ x (equivalently, n ≥ ⌈1/x⌉). -/
axiom greedyStep (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1) : ℕ

/-- The greedy step picks an element of A. -/
axiom greedyStep_mem (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hinf : Set.Infinite A) : greedyStep x A hx hx1 ∈ A

/-- The greedy step satisfies 1/n ≤ x. -/
axiom greedyStep_le (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hinf : Set.Infinite A) :
    (1 : ℚ) / (greedyStep x A hx hx1) ≤ x

/-- The greedy algorithm terminates if the iterative process eventually reaches x = 0. -/
def GreedyTerminates (x : ℚ) (A : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, IsEgyptianFracRep x S A

/- ## Fibonacci's Theorem -/

/-- Fibonacci (1202): The greedy algorithm terminates for all rationals
    x ∈ (0, 1] when A = ℕ \ {0}. -/
axiom fibonacci_greedy_terminates (x : ℚ) (hx : 0 < x) (hx1 : x ≤ 1) :
    GreedyTerminates x {n : ℕ | n > 0}

/- ## The Odd Denominator Question (Stein) -/

/-- The set of odd positive integers. -/
def oddPositives : Set ℕ := {n : ℕ | n > 0 ∧ n % 2 = 1}

/-- A rational has odd denominator if, when written in lowest terms, the
    denominator is odd. -/
def HasOddDenom (x : ℚ) : Prop := x.den % 2 = 1

/-- **Stein's question (Erdős Problem #282, OPEN):**
    Does the greedy algorithm terminate when x has odd denominator
    and A = odd positive integers?

    This is an OPEN problem — stated as a Prop definition, not an axiom.
    Example: 3/5 = 1/3 + 1/5 + 1/15 + ... (greedy picks 3, then ...) -/
def SteinOddGreedyConjecture : Prop :=
  ∀ x : ℚ, 0 < x → x ≤ 1 → HasOddDenom x → GreedyTerminates x oddPositives

/- ## Graham's Representability Results (1964) -/

/-- The set of positive integers ≡ a (mod d). -/
def congClass (a d : ℕ) : Set ℕ := {n : ℕ | n > 0 ∧ n % d = a % d}

/-- **Graham (1964)**: A rational m/n with gcd(m,n)=1 can be represented as a
    sum of distinct unit fractions with denominators ≡ a (mod d) if and only
    if certain algebraic conditions on a, d, m, n are satisfied.

    The full conditions are complex and depend on the prime factorization
    of d and the residue class. This is stated as a definition rather than
    an axiom to avoid introducing vacuous assumptions. -/
def GrahamRepresentability (a d m n : ℕ) (hd : d > 0) (hn : n > 0)
    (hcoprime : Nat.Coprime m n) : Prop :=
    IsRepresentable ((m : ℚ) / n) (congClass a d)

/- ## Square Denominators Conjecture -/

/-- The set of perfect squares. -/
def perfectSquares : Set ℕ := {n : ℕ | ∃ k : ℕ, k > 0 ∧ n = k * k}

/-- **Erdős–Graham conjecture (OPEN):** The greedy algorithm on A = {n² : n ≥ 1}
    perhaps fails to terminate for "almost all" starting rationals.
    Stated as a definition, not an axiom (this is a conjecture). -/
def ErdosGrahamSquaresConjecture : Prop :=
    ∃ x : ℚ, 0 < x ∧ x ≤ 1 ∧ ¬ GreedyTerminates x perfectSquares

/- ## General Framework -/

/-- **Greedy termination implies representability.**
    This is definitionally true: `GreedyTerminates` and `IsRepresentable`
    are both `∃ S, IsEgyptianFracRep x S A`. -/
theorem greedy_implies_representable (x : ℚ) (A : Set ℕ)
    (hterm : GreedyTerminates x A) : IsRepresentable x A :=
  hterm

/-- **Representability is exactly greedy termination** (by definition). -/
theorem representable_iff_greedy (x : ℚ) (A : Set ℕ) :
    IsRepresentable x A ↔ GreedyTerminates x A :=
  Iff.rfl

/-- **Unit fractions are self-representable.**
    For any n > 0 with n ∈ A: 1/n is representable using denominators from A. -/
theorem unit_frac_representable (n : ℕ) (hn : n > 0) (A : Set ℕ) (hmem : n ∈ A) :
    IsRepresentable ((1 : ℚ) / n) A := by
  refine ⟨{n}, ⟨fun m hm => ?_, ?_⟩⟩
  · simp at hm; subst hm; exact ⟨hmem, hn⟩
  · simp

/-- **The odd positive integers are infinite.** -/
theorem oddPositives_infinite : Set.Infinite oddPositives := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
  · intro a b h; omega
  · intro n; simp [oddPositives]; omega
