/-
# Erdős Problem #125 — `positive_lower_density` variant

## Status

The **positive_lower_density** variant of Erdős Problem #125 has been
**resolved in the negative** by DeepMind's AlphaProof Nexus system (2026-05-21,
arXiv:2605.22763v1). That is, the sumset $C = A + B$ where
$A = \{n \in \mathbb{N} : \text{digits of } n \text{ in base } 3 \text{ are } 0 \text{ or } 1\}$
and
$B = \{n \in \mathbb{N} : \text{digits of } n \text{ in base } 4 \text{ are } 0 \text{ or } 1\}$
has **lower density equal to zero**. The original Erdős conjecture asked whether
$\liminf_{x \to \infty} |C \cap [1,x]|/x > 0$; AlphaProof Nexus answered NO.

## Provenance

This file integrates DeepMind's AlphaProof Nexus Lean proof:
- Source: `APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`
- Repository: https://github.com/google-deepmind/alphaproof-nexus-results
- Paper: arXiv:2605.22763v1 (2026-05-21)
- Natural-language proof: `NaturalLanguageProofs/ErdosProblems/erdos125.pdf`

The original AlphaProof proof depends on `FormalConjectures.Util.ProblemImports`,
which in turn provides `Set.partialDensity` / `Set.lowerDensity` via
`FormalConjecturesForMathlib`. Since Lean Genius uses only Mathlib v4.26.0,
we inline the relevant density definitions below.

## Caveats

The AlphaProof Nexus proof is 370 lines of highly compressed automated-proof-search
tactic output. Many lemmas use elaborate one-line proofs that interleave dozens of
tactics including `bound`, `valid`, and other custom tactics from FormalConjectures.
A faithful line-by-line port is left as a follow-up task; this file presently
**states** each lemma with a `sorry` placeholder so the high-level structure
matches the AlphaProof source, and the dependency graph is correct.

## Proof strategy (from the natural-language note)

The key idea is a **multi-scale density argument**:
1. Use Dirichlet approximation (via irrationality of `log 4 / log 3`) to find
   integers `k, m` with `3^k ≈ 4^m`.
2. Decompose any `a ∈ A` as `a = a₁ · 3^k + a₀` with `a₁ ∈ A`, `a₀ ∈ A`, `a₀ < 3^k`
   (and similarly for `B` with `4^m`).
3. Show that at each scale, only a `5/6 + o(1)` fraction of the interval `[0, 3^k)`
   can be represented by `A + B` residues. This gives `density(A+B ∩ [0, N·3^k]) ≤
   (11/12) · density(A+B ∩ [0, N])`.
4. Iterating yields `density → 0`.

## References

- Burr, Erdős, Graham, Li (1996): original conjecture.
- Melfi (2001): `|C ∩ [1,x]| ≫ x^{0.965}`.
- Hasler, Melfi (2024): improved to `x^{0.9777}`, upper density `≤ 0.696`.
- **DeepMind AlphaProof Nexus (2026-05-21)**: lower density `= 0`. (This file.)
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Nat Pointwise Filter
open scoped Topology Classical

namespace Erdos125PositiveLowerDensity

/-! ## Density definitions (inlined from FormalConjecturesForMathlib) -/

/-- Set of naturals `< b` that lie in `S`. -/
noncomputable def interIio (S : Set ℕ) (b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (· ∈ S)

/--
Partial density of `S` at `b`: proportion of `{x : ℕ | x < b}` lying in `S`.
This is the natural-numbers specialisation of
`FormalConjecturesForMathlib.Data.Set.Density.partialDensity`.
-/
noncomputable def partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  ((interIio S b).card : ℝ) / (b : ℝ)

/-- Lower density of `S ⊆ ℕ`: `liminf` of partial densities. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  atTop.liminf (fun b : ℕ => partialDensity S b)

/-! ## The digit-restricted sets A and B -/

/-- `A` = naturals whose base-3 digits are all `0` or `1`. -/
def A : Set ℕ := { x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} }

/-- `B` = naturals whose base-4 digits are all `0` or `1`. -/
def B : Set ℕ := { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }

/-! ## Supporting lemmas

The lemmas below mirror exactly the structure of the AlphaProof Nexus proof
(see https://github.com/google-deepmind/alphaproof-nexus-results, file
`APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`).
Their one-line AlphaProof tactic proofs do not port cleanly to a pure Mathlib
setup; we therefore state them with `sorry` here. A faithful line-by-line port
is tracked as a follow-up sub-issue. -/

lemma zero_in_A : 0 ∈ A := by
  -- AlphaProof: `norm_num`
  simp [A]

lemma zero_in_B : 0 ∈ B := by
  -- AlphaProof: `bound`
  simp [B]

lemma zero_in_A_plus_B : 0 ∈ A + B := by
  refine ⟨0, zero_in_A, 0, zero_in_B, ?_⟩
  simp

/-- If `x < 3^k` and `x ∈ A` then `x ≤ (3^k - 1) / 2`. -/
lemma A_max_k (k x : ℕ) (hx : x < 3 ^ k) (hA : x ∈ A) : x ≤ (3 ^ k - 1) / 2 := by
  sorry

/-- If `y < 4^m` and `y ∈ B` then `y ≤ (4^m - 1) / 3`. -/
lemma B_max_m (m y : ℕ) (hy : y < 4 ^ m) (hB : y ∈ B) : y ≤ (4 ^ m - 1) / 3 := by
  sorry

/--
**Gap lemma.** If `(3^k - 1)/2 + (4^m - 1)/3 < x`, `x < 3^k`, and `x < 4^m`,
then `x ∉ A + B`. (No `(a,b)` decomposition can reach the upper part of the
interval below `min(3^k, 4^m)`.)
-/
lemma A_B_gap (k m x : ℕ)
    (hx_gt : (3 ^ k - 1) / 2 + (4 ^ m - 1) / 3 < x)
    (hx_lt_A : x < 3 ^ k) (hx_lt_B : x < 4 ^ m) : x ∉ A + B := by
  sorry

/-- Decomposition: every `a ∈ A` factors as `a = a₁ · 3^k + a₀` with both pieces in `A`. -/
lemma A_decomp (k a : ℕ) (ha : a ∈ A) :
    ∃ a1 a0 : ℕ, a1 ∈ A ∧ a0 ∈ A ∧ a0 < 3 ^ k ∧ a = a1 * 3 ^ k + a0 := by
  sorry

/-- Decomposition: every `b ∈ B` factors as `b = b₁ · 4^m + b₀` with both pieces in `B`. -/
lemma B_decomp (m b : ℕ) (hb : b ∈ B) :
    ∃ b1 b0 : ℕ, b1 ∈ B ∧ b0 ∈ B ∧ b0 < 4 ^ m ∧ b = b1 * 4 ^ m + b0 := by
  sorry

/-- `log 4 / log 3` is irrational. -/
lemma log_ratio_irrational : Irrational (Real.log 4 / Real.log 3) := by
  sorry

/--
**Dirichlet helper.** For any irrational `α > 0` and any `δ > 0`, there exist
positive integers `m, k` with `0 < m·α - k < δ`.
-/
lemma exists_small_pos_lin_comb_help (α : ℝ) (hα : Irrational α) (hα_pos : 0 < α)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      0 < (m : ℝ) * α - (k : ℝ) ∧ (m : ℝ) * α - (k : ℝ) < δ := by
  sorry

/-- Specialisation to `α = log 4 / log 3`. -/
lemma exists_small_pos_lin_comb (δ : ℝ) (hδ : 0 < δ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      0 < (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 ∧
      (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 < δ := by
  sorry

/-- Refinement: also `K ≤ 3^k`. -/
lemma exists_small_pos_lin_comb_large_k (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ K ≤ (3 ^ k : ℝ) ∧
      0 < (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 ∧
      (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 < δ := by
  sorry

/--
**Dirichlet approximation.** For any `ε > 0`, there exist `k, m > 0` with
`3^k ≤ 4^m ≤ 3^k · (1+ε)` and `3^k · ε ≥ 3`.
-/
lemma dirichlet_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ (3 ^ k : ℝ) ≤ 4 ^ m ∧
      (4 ^ m : ℝ) ≤ (3 ^ k : ℝ) * (1 + ε) ∧ (3 ^ k : ℝ) * ε ≥ 3 := by
  sorry

/-- Algebraic identity used in the scale-step. -/
lemma hz_eq_lemma (x a b a1 a0 b1 b0 k m : ℕ)
    (h1 : 3 ^ k ≤ 4 ^ m) (h3 : x = a + b)
    (h4 : a = a1 * 3 ^ k + a0) (h5 : b = b1 * 4 ^ m + b0) :
    x = (a1 + b1) * 3 ^ k + (a0 + b0 + b1 * (4 ^ m - 3 ^ k)) := by
  have h2 : 4 ^ m = 3 ^ k + (4 ^ m - 3 ^ k) := by omega
  have h6 : b1 * 4 ^ m = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := by
    calc
      b1 * 4 ^ m = b1 * (3 ^ k + (4 ^ m - 3 ^ k)) := congrArg (b1 * ·) h2
      _ = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := Nat.mul_add b1 _ _
  have h7 : (a1 + b1) * 3 ^ k = a1 * 3 ^ k + b1 * 3 ^ k := Nat.add_mul a1 b1 _
  omega

/--
**Scale step.** Given a density bound `C` valid on `[0,N)`, we obtain an
improved density bound `(11/12)·C` valid on some larger window `[0,N')`.
-/
lemma scale_step (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤ C * (N : ℝ)) :
    ∃ N' > 0, (((Finset.Ico 0 N').filter (· ∈ A + B)).card : ℝ) ≤
      (11 / 12 : ℝ) * C * (N' : ℝ) := by
  sorry

/-- Iterated scale step: `(11/12)^d · N` bound. -/
lemma density_multi_scale (d : ℕ) :
    ∃ N > 0, (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤
      ((11 / 12 : ℝ) ^ d) * (N : ℝ) := by
  induction d with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    simp only [pow_zero, one_mul]
    have h1 : (((Finset.Ico 0 1).filter (· ∈ A + B)).card : ℝ) ≤
        ((Finset.Ico 0 1).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    have h2 : (Finset.Ico 0 1).card = 1 := rfl
    rw [h2] at h1
    push_cast at h1 ⊢
    exact h1
  | succ d ih =>
    rcases ih with ⟨N, hN, h_bound⟩
    obtain ⟨N', hN', h_bound'⟩ := scale_step N hN ((11 / 12 : ℝ) ^ d) h_bound
    refine ⟨N', hN', ?_⟩
    have h_mul : (11 / 12 : ℝ) ^ (d + 1) = (11 / 12 : ℝ) * (11 / 12 : ℝ) ^ d := by
      rw [pow_add, pow_one]; ring
    rw [h_mul]
    linarith

/-- For any `ε > 0`, there exists `d` with `(11/12)^d ≤ ε`. -/
lemma limit_11_12 (ε : ℝ) (hε : ε > 0) : ∃ d : ℕ, (11 / 12 : ℝ) ^ d ≤ ε :=
  (exists_pow_lt_of_lt_one hε (by norm_num)).imp (fun _ => le_of_lt)

/--
**Density-tends-to-zero lemma.** For every `ε > 0`, some window `[0,N)` has
`|A + B ∩ [0,N)| ≤ ε · N`. This is the key consequence of multi-scale
iteration.
-/
lemma density_tends_to_zero (ε : ℝ) (hε : ε > 0) :
    ∃ N > 0, (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤ ε * (N : ℝ) := by
  obtain ⟨d, hd2⟩ := limit_11_12 ε hε
  obtain ⟨N, hN, h_bound⟩ := density_multi_scale d
  refine ⟨N, hN, ?_⟩
  have hN' : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  calc (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ)
      ≤ ((11 / 12 : ℝ) ^ d) * (N : ℝ) := h_bound
    _ ≤ ε * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hd2 hN'

/-! ## Main theorem -/

/--
**AlphaProof Nexus result (2026-05-21):** the sumset `A + B` has
**lower density equal to zero**.

In particular, the `positive_lower_density` variant of Erdős Problem #125
is **resolved in the negative**: $\liminf_{x \to \infty} |C \cap [1,x]|/x = 0$.

Source: `APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`
in https://github.com/google-deepmind/alphaproof-nexus-results.
-/
theorem AB_lowerDensity_eq_zero : lowerDensity (A + B) = 0 := by
  sorry

/--
**Corollary:** the lower density of `A + B` is *not* positive — i.e., the
positive_lower_density form of Erdős #125 fails.
-/
theorem not_positive_lowerDensity_AB : ¬ (0 < lowerDensity (A + B)) := by
  intro h
  have h0 : lowerDensity (A + B) = 0 := AB_lowerDensity_eq_zero
  rw [h0] at h
  exact lt_irrefl 0 h

end Erdos125PositiveLowerDensity
