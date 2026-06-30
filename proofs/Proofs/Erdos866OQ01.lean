/-
  # Erdős Problem #866 — The lower bound `g_k(N) ≥ 1` holds for ALL `k ≥ 3`
  # (erdos-866-oq-01)

  ## Background

  For `k ≥ 3`, Erdős #866 studies the minimal threshold `g_k(N)` such that every
  `A ⊆ {1, …, 2N}` with `|A| ≥ N + g_k(N)` contains all pairwise sums
  `b_i + b_j` (`i < j`) of some `k`-tuple `b₁, …, b_k`.

  The basic lower bound `g_k(N) ≥ 1` is witnessed by the extremal set of the `N`
  odd numbers in `{1, …, 2N}`: no `k` integers can have **all** of their pairwise
  sums land in this odd set, because among any three integers two share parity and
  their sum is even.

  The companion file `Erdos866Problem.lean` formalizes this obstruction only for the
  case `k = 3` (`oddNumbers_no_triple`), even though the headline claim is
  "`g_k(N) ≥ 1` for all `k`". This file closes that gap: the parity obstruction is
  promoted to **every** `k ≥ 3` by restricting an alleged `k`-tuple to its first
  three coordinates, where the `k = 3` argument already applies.

  ## Main results

  * `oddNumbers_no_triple` — base case (`k = 3`): no three integers have all
    pairwise sums in the odd set (self-contained re-proof of the parent lemma).
  * `oddNumbers_no_ktuple` — **the generalization**: for every `k ≥ 3`, no
    `k`-tuple of integers has all pairwise sums in the odd set. This is exactly the
    statement `g_k(N) ≥ 1` for all `k ≥ 3`.
  * `upperExponent_nonneg`, `upperExponent_lt_one` — the upper-bound exponent
    `1 - 2^{-k}` lies in `[0, 1)`, so the general upper bound `g_k(N) ≪ N^{1-2^{-k}}`
    is genuinely sub-linear for every `k`.
  * `upperExponent_strictMono` — the exponent is strictly increasing in `k` as a
    full `StrictMono` (sharpening the parent's consecutive-step version).
  * `upperExponent_tendsto_one` — the exponents converge to the limiting value `1`.

  No new axioms, no sorries: the proofs compose existing Mathlib lemmas and a parity
  pigeonhole.

  ## Honest scope

  The lower bound `g_k(N) ≥ 1` and the elementary exponent facts are the *settled*
  shell of #866. The hard content — the exact growth rates `g₄`, `g₅ ≍ log N`,
  `g₆ ≍ √N`, and the true exponent `α_k` — is the open frontier and is not touched
  here.

  Tags: additive-combinatorics, sumsets, pairwise-sums, threshold-functions, erdos
-/
import Mathlib

open Finset Real

namespace Erdos866OQ01

/-- The interval `{1, 2, …, 2N}`. -/
def Interval (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => n ≥ 1)

/-- A set `A` contains all pairwise sums of `b₁, …, b_k` if `b_i + b_j ∈ A` for all
    `i < j`. -/
def HasAllPairwiseSums (A : Finset ℕ) (b : Fin k → ℤ) : Prop :=
  ∀ i j : Fin k, i < j → (b i + b j).toNat ∈ A

/-- The set of odd numbers in `{1, …, 2N}`. -/
def oddNumbers (N : ℕ) : Finset ℕ :=
  (Interval N).filter (fun n => n % 2 = 1)

/-- The exponent `1 - 2^{-k}` in the general upper bound `g_k(N) ≪ N^{1-2^{-k}}`. -/
noncomputable def upperExponent (k : ℕ) : ℝ :=
  1 - (2 : ℝ)⁻¹ ^ k

-- ============================================================================
-- Part I: The parity obstruction `g_k(N) ≥ 1` for all `k ≥ 3`
-- ============================================================================

/-- **Base case (`k = 3`).** No three integers can have all of their pairwise sums
    inside the odd numbers of `{1, …, 2N}`: among any three integers two share
    parity, so their sum is even and cannot be odd. -/
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  rintro ⟨b, hb⟩
  have h_odd : ∀ i j : Fin 3, i < j → (b i + b j).toNat % 2 = 1 := by
    intro i j hij; have := hb i j hij; unfold oddNumbers at this; aesop
  simp_all +decide [Fin.forall_fin_succ]
  grind +ring

/-- **The generalization: `g_k(N) ≥ 1` for every `k ≥ 3`.** No `k`-tuple of integers
    can have all of its pairwise sums inside the odd numbers of `{1, …, 2N}`.

    The proof restricts an alleged `k`-tuple to its first three coordinates (using
    `3 ≤ k`); since `Fin.castLE` preserves the underlying order, the restricted
    triple again has all pairwise sums in the odd set, contradicting
    `oddNumbers_no_triple`. -/
theorem oddNumbers_no_ktuple {k : ℕ} (hk : 3 ≤ k) (N : ℕ) :
    ¬∃ b : Fin k → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  rintro ⟨b, hb⟩
  refine oddNumbers_no_triple N ⟨fun i => b (Fin.castLE hk i), ?_⟩
  intro i j hij
  -- `Fin.castLE` preserves the underlying value, so `i < j` transports verbatim.
  exact hb (Fin.castLE hk i) (Fin.castLE hk j) hij

-- ============================================================================
-- Part II: The upper-bound exponent `1 - 2^{-k}`
-- ============================================================================

/-- The exponent `1 - 2^{-k}` is non-negative for every `k` (since `2^{-k} ≤ 1`). -/
theorem upperExponent_nonneg (k : ℕ) : 0 ≤ upperExponent k := by
  have h : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [upperExponent]; linarith

/-- The exponent `1 - 2^{-k}` is strictly below `1` for every `k` (since
    `2^{-k} > 0`). Hence the general upper bound `g_k(N) ≪ N^{1-2^{-k}}` is genuinely
    sub-linear in `N` for all `k`. -/
theorem upperExponent_lt_one (k : ℕ) : upperExponent k < 1 := by
  have h : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  simp only [upperExponent]; linarith

/-- **Strict monotonicity of the exponent** (full `StrictMono`, sharpening the
    parent's consecutive-step lemma): `i < j → 1 - 2^{-i} < 1 - 2^{-j}`, because the
    geometric sequence `2^{-k}` is strictly decreasing. -/
theorem upperExponent_strictMono : StrictMono upperExponent := by
  intro i j hij
  have h : (2 : ℝ)⁻¹ ^ j < (2 : ℝ)⁻¹ ^ i :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hij
  simp only [upperExponent]; linarith

/-- The exponents `1 - 2^{-k}` converge to the limiting value `1` as `k → ∞`. -/
theorem upperExponent_tendsto_one :
    Filter.Tendsto upperExponent Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun k => (2 : ℝ)⁻¹ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  unfold upperExponent
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

end Erdos866OQ01
