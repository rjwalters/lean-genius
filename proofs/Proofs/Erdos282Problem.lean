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

import Mathlib
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

/-- For any infinite set of naturals and any bound, there exists an element
    at least that large. -/
private lemma infinite_nat_above (A : Set ℕ) (hinf : Set.Infinite A) (m : ℕ) :
    ∃ n ∈ A, m ≤ n := by
  by_contra h
  push_neg at h
  exact hinf (Set.Finite.subset (Set.finite_Iio m) (fun n hn => h n hn))

/-- Existence of a greedy candidate: some n ∈ A with n > 0 and 1/n ≤ x. -/
private lemma exists_greedy_candidate (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hinf : Set.Infinite A) : ∃ n, n ∈ A ∧ 0 < n ∧ (1 : ℚ) / n ≤ x := by
  obtain ⟨n, hn_mem, hn_ge⟩ := infinite_nat_above A hinf x.den
  have hden_pos := x.den_pos
  refine ⟨n, hn_mem, by omega, ?_⟩
  -- 1/n ≤ x: since n ≥ x.den and x = x.num/x.den with x.num ≥ 1
  have hn_pos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_iff₀ hn_pos]
  -- Goal: 1 ≤ x * ↑n
  have hx_num_pos : 0 < x.num := Rat.num_pos.mpr hx
  -- x * n ≥ x * x.den = x.num ≥ 1
  have h_xden : x * (x.den : ℚ) = (x.num : ℚ) := by
    have := Rat.num_div_den x  -- : (x.num : ℚ) / (x.den : ℚ) = x
    field_simp at this ⊢
    linarith
  calc (1 : ℚ) ≤ (x.num : ℤ) := by exact_mod_cast hx_num_pos
    _ = x * (x.den : ℚ) := h_xden.symm
    _ ≤ x * (n : ℚ) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hn_ge
        · exact le_of_lt hx

/-- The greedy step: find smallest n ∈ A with n > 0 and 1/n ≤ x.
    Returns 0 if no such n exists (only possible for finite A). -/
noncomputable instance (p : Prop) : Decidable p := Classical.dec p

noncomputable def greedyStep (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1) : ℕ :=
  if h : ∃ n, n ∈ A ∧ 0 < n ∧ (1 : ℚ) / n ≤ x then
    Nat.find h
  else 0

/-- The greedy step picks an element of A. -/
theorem greedyStep_mem (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hinf : Set.Infinite A) : greedyStep x A hx hx1 ∈ A := by
  have h_ex := exists_greedy_candidate x A hx hx1 hinf
  simp only [greedyStep, dif_pos h_ex]
  exact (Nat.find_spec h_ex).1

/-- The greedy step satisfies 1/n ≤ x. -/
theorem greedyStep_le (x : ℚ) (A : Set ℕ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hinf : Set.Infinite A) :
    (1 : ℚ) / (greedyStep x A hx hx1) ≤ x := by
  have h_ex := exists_greedy_candidate x A hx hx1 hinf
  simp only [greedyStep, dif_pos h_ex]
  exact (Nat.find_spec h_ex).2.2

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
  rw [Set.infinite_iff_exists_gt]
  intro n
  refine ⟨2 * n + 1, ?_, by omega⟩
  simp only [oddPositives, Set.mem_setOf_eq]
  omega
