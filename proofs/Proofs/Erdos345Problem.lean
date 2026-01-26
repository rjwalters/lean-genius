/-!
# Erdős Problem 345: Completeness Thresholds for Power Sequences

Let `A ⊆ ℕ` be a complete sequence, meaning the subset sums `P(A)`
contain all sufficiently large integers. The threshold `T(A)` is the
least `m` such that all `n ≥ m` are in `P(A)`.

**Question:** Are there infinitely many `k` with `T(n^k) > T(n^{k+1})`?

Known values: `T(n) = 1`, `T(n²) = 128`, `T(n³) = 12758`,
`T(n⁴) = 5134240`, `T(n⁵) = 67898771`.

*Reference:* [erdosproblems.com/345](https://www.erdosproblems.com/345)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-! ## Subset sums and completeness -/

/-- The set of finite subset sums of `A ⊆ ℕ`. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
    { s | ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧ S.sum id = s }

/-- A sequence `A` is complete if all sufficiently large integers are
in `P(A)`. -/
def IsComplete (A : Set ℕ) : Prop :=
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → n ∈ subsetSums A

/-! ## Completeness threshold -/

/-- The threshold of completeness `T(A)`: the least `m` such that all
`n ≥ m` are subset sums of `A`. Axiomatised since computing the
minimum requires decidability. -/
axiom threshold : Set ℕ → ℕ

/-- `threshold A` is correct: all `n ≥ T(A)` are in `P(A)`. -/
axiom threshold_spec (A : Set ℕ) (hA : IsComplete A) :
    ∀ n : ℕ, threshold A ≤ n → n ∈ subsetSums A

/-- `threshold A` is minimal: some `n < T(A)` is not in `P(A)`,
unless `T(A) = 0`. -/
axiom threshold_minimal (A : Set ℕ) (hA : IsComplete A)
    (ht : 0 < threshold A) :
    ∃ n : ℕ, n < threshold A ∧ n ∉ subsetSums A

/-! ## Power sequences -/

/-- The set of `k`-th powers: `{n^k : n ≥ 1}`. -/
def powerSeq (k : ℕ) : Set ℕ :=
    { m | ∃ n : ℕ, 1 ≤ n ∧ m = n ^ k }

/-- The sequence of natural numbers is complete with `T(n) = 1`. -/
axiom powerSeq_1_complete : IsComplete (powerSeq 1)
axiom threshold_powerSeq_1 : threshold (powerSeq 1) = 1

/-! ## Known threshold values -/

/-- `T(n²) = 128`. -/
axiom threshold_squares : threshold (powerSeq 2) = 128

/-- `T(n³) = 12758`. -/
axiom threshold_cubes : threshold (powerSeq 3) = 12758

/-- `T(n⁴) = 5134240`. -/
axiom threshold_fourth : threshold (powerSeq 4) = 5134240

/-- `T(n⁵) = 67898771`. -/
axiom threshold_fifth : threshold (powerSeq 5) = 67898771

/-! ## Completeness of power sequences -/

/-- Power sequences `{n^k}` are complete for all `k ≥ 1`
(Waring's problem guarantees this). -/
axiom powerSeq_complete (k : ℕ) (hk : 1 ≤ k) :
    IsComplete (powerSeq k)

/-! ## Main conjecture -/

/-- Erdős Problem 345: Are there infinitely many `k` with
`T(n^k) > T(n^{k+1})`? -/
def ErdosProblem345 : Prop :=
    ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      threshold (powerSeq (k + 1)) < threshold (powerSeq k)

/-! ## Monotonicity observations -/

/-- The known values suggest `T(n^k)` is rapidly increasing, but the
conjecture asks whether the sequence ever decreases. -/
axiom threshold_mono_small :
    threshold (powerSeq 1) < threshold (powerSeq 2) ∧
    threshold (powerSeq 2) < threshold (powerSeq 3) ∧
    threshold (powerSeq 3) < threshold (powerSeq 4) ∧
    threshold (powerSeq 4) < threshold (powerSeq 5)
