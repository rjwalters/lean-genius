/-
# Erdős Problem 345: Completeness Thresholds for Power Sequences

Let `A ⊆ ℕ` be a complete sequence, meaning the subset sums `P(A)`
contain all sufficiently large integers. The threshold `T(A)` is the
least `m` such that all `n ≥ m` are in `P(A)`.

**Question:** Are there infinitely many `k` with `T(n^k) > T(n^{k+1})`?

Known values (under the "least `m`" convention used by `threshold` here):
`T(n) = 1`, `T(n²) = 129`, `T(n³) = 12759`,
`T(n⁴) = 5134241`, `T(n⁵) = 67898772`.

Equivalently, the largest non-representable integers are `0, 128, 12758,
5134240, 67898771` (cf. OEIS A001661); under our `IsCompleteSeq`
definition the threshold is "largest non-representable + 1".

*Reference:* [erdosproblems.com/345](https://www.erdosproblems.com/345)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Erdos345

/- ## Subset sums and completeness -/

/-- The set of finite nonempty subset sums of `A ⊆ ℕ`.
    We require `S.Nonempty` to match the standard convention where
    the empty sum (0) is not counted as a representation. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
    { s | ∃ (S : Finset ℕ), S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ S.sum id = s }

/-- A sequence `A` is complete if all sufficiently large integers are
in `P(A)`. -/
def IsCompleteSeq (A : Set ℕ) : Prop :=
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → n ∈ subsetSums A

/- ## Completeness threshold -/

/-- The threshold of completeness `T(A)`: the least `m` such that all
    `n ≥ m` are in `P(A)`. Defined via `Nat.find` when `A` is complete. -/
open Classical in
noncomputable def threshold (A : Set ℕ) : ℕ :=
    if h : IsCompleteSeq A then Nat.find h else 0

/-- `threshold A` is correct: all `n ≥ T(A)` are in `P(A)`. -/
theorem threshold_spec (A : Set ℕ) (hA : IsCompleteSeq A) :
    ∀ n : ℕ, threshold A ≤ n → n ∈ subsetSums A := by
  simp only [threshold, dif_pos hA]
  exact Nat.find_spec hA

/-- `threshold A` is minimal: some `n < T(A)` is not in `P(A)`,
unless `T(A) = 0`. -/
theorem threshold_minimal (A : Set ℕ) (hA : IsCompleteSeq A)
    (ht : 0 < threshold A) :
    ∃ n : ℕ, n < threshold A ∧ n ∉ subsetSums A := by
  simp only [threshold, dif_pos hA] at ht ⊢
  -- Nat.find hA > 0, so Nat.find hA - 1 < Nat.find hA
  have hlt : Nat.find hA - 1 < Nat.find hA := by omega
  have hmin := Nat.find_min hA hlt
  -- ¬(∀ n ≥ Nat.find hA - 1, n ∈ subsetSums A)
  push_neg at hmin
  obtain ⟨n, hn_ge, hn_not⟩ := hmin
  refine ⟨n, ?_, hn_not⟩
  -- n ∉ subsetSums A, but all n ≥ Nat.find hA are in subsetSums A
  by_contra h
  push_neg at h
  exact hn_not (Nat.find_spec hA n h)

/- ## Monotonicity of subset sums -/

/-- If A ⊆ B, then every subset sum of A is a subset sum of B. -/
theorem subsetSums_mono {A B : Set ℕ} (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  intro s ⟨S, hne, hS_sub, hS_sum⟩
  exact ⟨S, hne, Set.Subset.trans hS_sub h, hS_sum⟩

/-- If A ⊆ B and A is complete, then B is complete. -/
theorem isComplete_of_subset {A B : Set ℕ} (h : A ⊆ B)
    (hA : IsCompleteSeq A) : IsCompleteSeq B := by
  obtain ⟨m, hm⟩ := hA
  exact ⟨m, fun n hn => subsetSums_mono h (hm n hn)⟩

/-- Threshold monotonicity: A ⊆ B implies T(B) ≤ T(A).
    More elements means more subset sums, so completeness is reached sooner. -/
theorem threshold_le_of_subset {A B : Set ℕ} (h : A ⊆ B)
    (hA : IsCompleteSeq A) :
    threshold B ≤ threshold A := by
  have hB := isComplete_of_subset h hA
  simp only [threshold, dif_pos hA, dif_pos hB]
  apply Nat.find_min'
  intro n hn
  exact subsetSums_mono h (Nat.find_spec hA n hn)

/- ## Power sequences -/

/-- The set of `k`-th powers: `{n^k : n ≥ 1}`. -/
def powerSeq (k : ℕ) : Set ℕ :=
    { m | ∃ n : ℕ, 1 ≤ n ∧ m = n ^ k }

/-- Every k-th power (k ≥ 1) is a 1st power: powerSeq k ⊆ powerSeq 1.
    Since n^k ≥ 1 when n ≥ 1, we have n^k = (n^k)^1 ∈ powerSeq 1. -/
theorem powerSeq_subset_powerSeq_1 (k : ℕ) (hk : 1 ≤ k) :
    powerSeq k ⊆ powerSeq 1 := by
  intro m ⟨n, hn, hm⟩
  exact ⟨m, by rw [hm]; exact Nat.one_le_pow k n hn, pow_one m⟩

/-- Combining monotonicity with powerSeq_1_complete: every powerSeq k
    (k ≥ 1) is complete, assuming powerSeq 1 completeness. -/
theorem powerSeq_complete_from_1 (k : ℕ) (hk : 1 ≤ k) :
    IsCompleteSeq (powerSeq k) → threshold (powerSeq 1) ≤ threshold (powerSeq k) :=
  fun hc => threshold_le_of_subset (powerSeq_subset_powerSeq_1 k hk) hc

/-- The sequence of natural numbers is complete with `T(n) = 1`.
    Every n ≥ 1 is a subset sum of {1^1, 2^1, 3^1, ...} via the singleton {n}. -/
theorem powerSeq_1_complete : IsCompleteSeq (powerSeq 1) := by
  refine ⟨1, fun n hn => ?_⟩
  refine ⟨{n}, Finset.singleton_nonempty n, ?_, ?_⟩
  · simp only [Finset.coe_singleton, Set.singleton_subset_iff]
    exact ⟨n, hn, (pow_one n).symm⟩
  · simp

/-- `T(n) = 1`: the threshold of {1, 2, 3, ...} is 1.
    Proof: all n ≥ 1 are subset sums (singletons), and 0 is not a nonempty
    subset sum (every element of powerSeq 1 is ≥ 1). -/
theorem threshold_powerSeq_1 : threshold (powerSeq 1) = 1 := by
  simp only [threshold, dif_pos powerSeq_1_complete]
  apply Nat.find_eq_iff.mpr
  constructor
  · -- All n ≥ 1 are in subsetSums(powerSeq 1)
    exact fun n hn => (powerSeq_1_complete).choose_spec n hn
  · -- For m = 0: not all n ≥ 0 are in subsetSums(powerSeq 1)
    intro m hm
    interval_cases m
    -- Show ¬(∀ n ≥ 0, n ∈ subsetSums(powerSeq 1))
    intro h0
    have h := h0 0 (le_refl 0)
    obtain ⟨S, hne, hS_sub, hS_sum⟩ := h
    -- S is nonempty, S ⊆ powerSeq 1, S.sum id = 0
    -- But every element of S is in powerSeq 1, so every element ≥ 1
    -- Therefore S.sum id ≥ 1, contradicting S.sum id = 0
    obtain ⟨x, hx_mem⟩ := hne
    have hx_in : x ∈ (↑S : Set ℕ) := Finset.mem_coe.mpr hx_mem
    have ⟨n, hn_pos, hn_eq⟩ := hS_sub hx_in
    have hx_pos : 1 ≤ x := by rw [hn_eq, pow_one]; exact hn_pos
    have := Finset.single_le_sum (fun a _ => Nat.zero_le a) hx_mem
    simp [id] at this
    omega

/- ## Known threshold values -/

/-- `T(n²) = 129`. Every integer ≥ 129 is a sum of distinct non-zero squares
    (Sprague 1948). 128 is the largest non-representable integer. -/
axiom threshold_squares : threshold (powerSeq 2) = 129

/-- `T(n³) = 12759`. Every integer ≥ 12759 is a sum of distinct positive cubes;
    12758 is the largest non-representable integer (OEIS A001661). -/
axiom threshold_cubes : threshold (powerSeq 3) = 12759

/-- `T(n⁴) = 5134241`. 5134240 is the largest non-representable integer
    (OEIS A001661). -/
axiom threshold_fourth : threshold (powerSeq 4) = 5134241

/-- `T(n⁵) = 67898772`. 67898771 is the largest non-representable integer
    (OEIS A001661). -/
axiom threshold_fifth : threshold (powerSeq 5) = 67898772

/- ## Completeness derived from threshold values -/

/-- `powerSeq 2` is complete: if it weren't, `threshold (powerSeq 2) = 0`
    by definition, contradicting `threshold_squares = 129`. -/
theorem powerSeq_2_complete : IsCompleteSeq (powerSeq 2) := by
  by_contra h
  simp only [threshold, dif_neg h] at threshold_squares
  norm_num at threshold_squares

/-- `powerSeq 3` is complete: derived from `threshold_cubes = 12759`. -/
theorem powerSeq_3_complete : IsCompleteSeq (powerSeq 3) := by
  by_contra h
  simp only [threshold, dif_neg h] at threshold_cubes
  norm_num at threshold_cubes

/-- `powerSeq 4` is complete: derived from `threshold_fourth = 5134241`. -/
theorem powerSeq_4_complete : IsCompleteSeq (powerSeq 4) := by
  by_contra h
  simp only [threshold, dif_neg h] at threshold_fourth
  norm_num at threshold_fourth

/-- `powerSeq 5` is complete: derived from `threshold_fifth = 67898772`. -/
theorem powerSeq_5_complete : IsCompleteSeq (powerSeq 5) := by
  by_contra h
  simp only [threshold, dif_neg h] at threshold_fifth
  norm_num at threshold_fifth

/- ## Completeness of power sequences (general) -/

/-- Power sequences `{n^k}` are complete for all `k ≥ 1`
(Waring's problem guarantees this; for k = 1–5 derived above). -/
axiom powerSeq_complete (k : ℕ) (hk : 1 ≤ k) :
    IsCompleteSeq (powerSeq k)

/- ## Main conjecture -/

/-- Erdős Problem 345: Are there infinitely many `k` with
`T(n^k) > T(n^{k+1})`? -/
def ErdosProblem345 : Prop :=
    ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      threshold (powerSeq (k + 1)) < threshold (powerSeq k)

/- ## Monotonicity observations -/

/-- The known values show `T(n^k)` is rapidly increasing for small k:
    1 < 129 < 12759 < 5134241 < 67898772. -/
theorem threshold_mono_small :
    threshold (powerSeq 1) < threshold (powerSeq 2) ∧
    threshold (powerSeq 2) < threshold (powerSeq 3) ∧
    threshold (powerSeq 3) < threshold (powerSeq 4) ∧
    threshold (powerSeq 4) < threshold (powerSeq 5) := by
  rw [threshold_powerSeq_1, threshold_squares, threshold_cubes,
      threshold_fourth, threshold_fifth]
  omega

end Erdos345
