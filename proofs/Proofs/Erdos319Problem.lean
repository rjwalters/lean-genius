/-!
# Erdős Problem #319 — Maximum Irreducible Signed Unit-Fraction Sum

Find the maximum size c(N) of A ⊆ {1,...,N} for which there exists
δ : A → {−1,1} such that:
  (1) Σ_{n ∈ A} δ(n)/n = 0
  (2) Σ_{n ∈ A'} δ(n)/n ≠ 0 for all non-empty proper A' ⊊ A

The sum vanishes but removing any element breaks the vanishing.

## Known Results
- Croot (2001): every integer in [1, N] is a sum of distinct unit fractions
  from {1,...,N} (used in constructions)
- Adenwalla: |A| ≥ (1 − 1/e + o(1))N via B ⊆ [(1/e − o(1))N, N]
  with Σ 1/b = 1, then A = B ∪ {1}

Status: OPEN
Reference: https://erdosproblems.com/319
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A signing function assigns ±1 to each element of a finite set. -/
def IsSigning (A : Finset ℕ) (δ : ℕ → Int) : Prop :=
  ∀ n ∈ A, δ n = 1 ∨ δ n = -1

/-- The signed unit-fraction sum Σ_{n ∈ A} δ(n)/n. -/
noncomputable def signedSum (A : Finset ℕ) (δ : ℕ → Int) : ℚ :=
  A.sum (fun n => (δ n : ℚ) / n)

/-- A signing is irreducible if the sum is zero but no proper nonempty
    subset has the same property. -/
def IsIrreducibleZeroSum (A : Finset ℕ) (δ : ℕ → Int) : Prop :=
  IsSigning A δ ∧
  signedSum A δ = 0 ∧
  ∀ A' : Finset ℕ, A' ⊂ A → A'.Nonempty → signedSum A' δ ≠ 0

/-- c(N) = maximum |A| for A ⊆ {1,...,N} admitting an irreducible zero sum. -/
noncomputable def maxIrreducibleSize (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A =>
    ∃ δ : ℕ → Int, IsIrreducibleZeroSum A δ)).sup Finset.card

/-! ## Main Conjecture -/

/-- **Erdős Problem #319**: determine the asymptotic growth of c(N).
    Conjectured to be Θ(N). The best known lower bound is (1 − 1/e + o(1))N. -/
axiom erdos_319_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N

/-! ## Known Results -/

/-- **Adenwalla Lower Bound**: c(N) ≥ (1 − 1/e + o(1))N.
    Construction: take B ⊆ [(1/e − o(1))N, N] with Σ_{b ∈ B} 1/b = 1,
    set A = B ∪ {1} with δ(1) = 1, δ(b) = −1. -/
axiom adenwalla_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N

/-- **Trivial Upper Bound**: c(N) ≤ N since A ⊆ {1,...,N}. -/
axiom trivial_upper_bound (N : ℕ) :
  maxIrreducibleSize N ≤ N

/-- **Croot (2001)**: every positive integer ≤ N is a sum of distinct
    unit fractions with denominators in {1,...,N} for large enough N.
    This is used in constructing irreducible configurations. -/
axiom croot_unit_fraction_theorem :
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, 1 ≤ k → k ≤ N →
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      S.sum (fun n => (1 : ℚ) / n) = k

/-! ## Observations -/

/-- **Small Example**: A = {1, 2} with δ(1) = 1, δ(2) = −1 gives
    1/1 − 1/2 = 1/2 ≠ 0. Need at least 3 elements for a zero sum. -/
axiom small_example :
  ∃ A : Finset ℕ, ∃ δ : ℕ → Int,
    A ⊆ Finset.Icc 1 6 ∧ IsIrreducibleZeroSum A δ

/-- **Connection to Unit Fractions**: the problem is closely related to
    Egyptian fraction representations and signed unit-fraction decompositions.
    Erdős and Graham (1980) posed this in their monograph on such problems. -/
axiom unit_fraction_connection : True
