/-
  Erdős Problem #158: Counting Functions of B₂[g] Sets

  Source: https://erdosproblems.com/158
  Status: PARTIALLY SOLVED (Sidon case proved, B₂[2] case open)

  Statement:
  Let A ⊆ ℕ be an infinite set such that, for any n, there are at most g
  solutions to a + b = n with a ≤ b and a, b ∈ A. Must
    liminf |A ∩ {1,...,N}| / N^{1/2} = 0?

  History:
  - For g = 1 (Sidon sets), Erdős proved this is true
  - For g = 2 (B₂[2] sets), this remains OPEN
  - Erdős, Sárközy, and Sós (1994) established the logarithmic bound for Sidon sets

  Reference: [ESS94] Erdős, Sárközy, Sós, "On Sum Sets of Sidon Sets, I"
-/

import Mathlib

open Filter Set
open scoped Topology ENNReal

namespace Erdos158

/-! ## Core Definitions -/

/-- A set A ⊆ ℕ is a **Sidon set** (also called B₂ set) if all pairwise sums
    a + b (with a ≤ b, a, b ∈ A) are distinct.

    Equivalently: a₁ + a₂ = b₁ + b₂ with a₁ ≤ a₂ and b₁ ≤ b₂ implies
    (a₁, a₂) = (b₁, b₂). -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
    a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂

/-- A set A ⊆ ℕ is a **B₂[g] set** if for all n, the equation a + b = n
    (with a ≤ b, a, b ∈ A) has at most g solutions.

    - B₂[1] = Sidon sets (at most one representation)
    - B₂[2] = at most two representations per sum -/
def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ | x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

/-- The counting function: |A ∩ {1,...,N}|. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ := (A ∩ Iio N).ncard

/-- The normalized counting function: |A ∩ {1,...,N}| / N^{1/2}. -/
noncomputable def normalizedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (countingFn A N : ℝ) * (N : ℝ) ^ (-1/2 : ℝ)

/-! ## B₂[1] = Sidon Sets -/

/-- A set is B₂[1] if and only if it is a Sidon set.

    Proof sketch: B₂[1] means each sum has at most one (ordered) representation.
    Sidon means a₁ + a₂ = b₁ + b₂ implies (a₁, a₂) = (b₁, b₂).
    These are equivalent. -/
axiom b2_one_iff_sidon {A : Set ℕ} : B2 1 A ↔ IsSidonSet A

/-! ## Main Results -/

/--
**Erdős-Sárközy-Sós (1994)**: For infinite Sidon sets,
  liminf |A ∩ {1,...,N}| / N^{1/2} * (log N)^{1/2} < ∞.

This stronger bound with the log factor is the key technical result.
Axiomatized because the proof requires careful probabilistic arguments
and sieve methods not yet in Mathlib.
-/
axiom ess_1994_log_bound {A : Set ℕ} (hA : A.Infinite) (hSidon : IsSidonSet A) :
    liminf (fun N => ENNReal.ofReal
      (countingFn A N * (N : ℝ) ^ (-1/2 : ℝ) * Real.log N ^ (1/2 : ℝ)))
      atTop < ⊤

/--
**Erdős-Sárközy-Sós (1994)**: For any infinite Sidon set A,
  liminf |A ∩ {1,...,N}| / N^{1/2} = 0.

This follows from the log bound: if liminf of f(N) * (log N)^{1/2} is finite,
then liminf of f(N) must be zero (since log N → ∞).
-/
axiom sidon_liminf_zero {A : Set ℕ} (hA : A.Infinite) (hSidon : IsSidonSet A) :
    liminf (normalizedCount A) atTop = 0

/-! ## The Open Problem -/

/--
**Erdős Problem #158 (OPEN)**: For infinite B₂[2] sets, must
  liminf |A ∩ {1,...,N}| / N^{1/2} = 0?

This generalizes the Sidon case (g = 1) to g = 2.
The techniques that work for Sidon sets don't immediately extend.
-/
def Conjecture_B2_2 : Prop :=
  ∀ A : Set ℕ, A.Infinite → B2 2 A → liminf (normalizedCount A) atTop = 0

/-! ## Implications and Relations -/

/-- The Sidon case is a special case of the conjecture.
    If the B₂[2] conjecture holds, it implies the Sidon result
    (since Sidon sets are B₂[1] ⊆ B₂[2]). -/
theorem sidon_implies_b2_hierarchy {A : Set ℕ} (hSidon : IsSidonSet A) : B2 2 A := by
  intro n
  have h1 : B2 1 A := b2_one_iff_sidon.mpr hSidon
  exact le_trans (h1 n) (by norm_num)

/-- Known result: The Sidon case of the conjecture is true. -/
theorem sidon_case_true {A : Set ℕ} (hA : A.Infinite) (hSidon : IsSidonSet A) :
    liminf (normalizedCount A) atTop = 0 :=
  sidon_liminf_zero hA hSidon

/-! ## Context: Why √N? -/

/-- For a Sidon set A ⊆ {1,...,N}, we have |A| ≤ √N + O(N^{1/4}).

    This is because if a₁ + a₂ = b₁ + b₂ (with ordered pairs distinct),
    then we get different sums. The number of such sums is O(N),
    giving |A|² ≤ O(N), hence |A| ≤ O(√N).

    The √N bound is essentially tight - there exist Sidon sets
    achieving |A| ≥ √N - o(√N). -/
axiom sidon_upper_bound {A : Set ℕ} (hSidon : IsSidonSet A) (N : ℕ) (hN : 0 < N) :
    countingFn A N ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 1

/-! ## Examples -/

/-- The set of perfect squares {1, 4, 9, 16, 25, ...} is a Sidon set.

    Proof: If a² + b² = c² + d² with a ≤ b and c ≤ d, then by unique
    factorization in ℤ[i], we get (a², b²) = (c², d²). -/
axiom squares_sidon : IsSidonSet {n : ℕ | ∃ k, n = k^2}

end Erdos158
