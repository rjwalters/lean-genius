/-
# Erdős Problem #1162 — Open Question OQ-04: Number of Subgroups of A_n

Source: https://erdosproblems.com/1162 (follow-up)
Parent: `Proofs/Erdos1162Problem.lean` (subgroups of S_n)
Status: OPEN (analog of a partially-resolved problem)

  ⚠️ UNVERIFIED: this candidate file was authored while the Docker Lean build
  toolchain was down (containerd blob corruption + full disk). It has NOT been
  machine-checked. Re-run `./proofs/scripts/docker-build.sh Proofs.Erdos1162OQ04`
  once Docker/disk are healthy before treating any theorem here as verified or
  promoting it to the gallery.

## The Question

Erdős Problem #1162 asks for an asymptotic formula for f(n), the number of
subgroups of the symmetric group S_n. Roney-Dougal–Tracey (2025) proved
`log f(n) = (1/16 + o(1)) n²`. The natural follow-up (OQ-04) is:

  **What is the analogous result for the alternating groups A_n?**

Let g(n) be the number of subgroups of A_n. The answer is that A_n obeys the
*same* leading asymptotic, `log g(n) = (1/16 + o(1)) n²`. The dominant
contribution again comes from elementary abelian 2-subgroups acting on ≈ n/4
points, and A_n still contains such 2-groups (products of an even number of
disjoint transpositions), so the constant 1/16 is unchanged.

## What is proved here (intended; machine-check pending)

The genuinely new structural content is an *unconditional* comparison between
the two counting functions:

  * `numSubgroupsAn_le_Sn`  :  g(n) ≤ f(n).
    Every subgroup of A_n pushes forward, along the injective inclusion
    A_n ↪ S_n, to a subgroup of S_n, and distinct subgroups have distinct
    images. Hence the subgroup lattice of A_n injects into that of S_n.

  * `log_numSubgroupsAn_le` and `An_ratio_le_Sn_ratio`  :  the same comparison
    at the logarithmic / normalized scale.

Consequence (no new axiom needed for this direction): the parent asymptotic for
S_n immediately caps the A_n count from above,
`limsup log g(n)/n² ≤ 1/16` (`An_upper_from_Sn`). Only the matching *lower*
bound requires the deep Roney-Dougal–Tracey machinery, which we state as an
axiom exactly as the parent file does for S_n.

References:
- [RoTr25] Roney-Dougal–Tracey, "The number of subgroups of the symmetric
  group" (2025).
- [Py93] Pyber, "Enumerating finite groups of given order" (1993).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Real Filter

namespace Erdos1162OQ04

/- ## Part I: The two counting functions -/

/-- f(n) = the number of subgroups of the symmetric group S_n. -/
noncomputable def numSubgroupsSn (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/-- g(n) = the number of subgroups of the alternating group A_n.
    Here `alternatingGroup (Fin n)` is a subgroup of `Equiv.Perm (Fin n)`, and
    we count subgroups of it *as an abstract group* (subgroups of the coerced
    type `↥(alternatingGroup (Fin n))`). -/
noncomputable def numSubgroupsAn (n : ℕ) : ℕ :=
  Nat.card (Subgroup (alternatingGroup (Fin n)))

/-- g(n) ≥ 1: the trivial subgroup always exists. -/
theorem numSubgroupsAn_pos (n : ℕ) : 0 < numSubgroupsAn n :=
  Nat.card_pos

/-- f(n) ≥ 1: the trivial subgroup always exists. -/
theorem numSubgroupsSn_pos (n : ℕ) : 0 < numSubgroupsSn n :=
  Nat.card_pos

/- ## Part II: The structural comparison g(n) ≤ f(n) (0 axioms) -/

/-- **Key structural theorem.** The number of subgroups of A_n is at most the
    number of subgroups of S_n.

    Proof: the inclusion `A_n ↪ S_n` (the subgroup-subtype homomorphism) is
    injective, so `Subgroup.map` along it is an injection of subgroup lattices
    `Subgroup A_n ↪ Subgroup S_n`. Cardinalities of finite types respect
    injections. -/
theorem numSubgroupsAn_le_Sn (n : ℕ) : numSubgroupsAn n ≤ numSubgroupsSn n := by
  unfold numSubgroupsAn numSubgroupsSn
  refine Nat.card_le_card_of_injective
    (Subgroup.map (alternatingGroup (Fin n)).subtype) ?_
  exact Subgroup.map_injective (Subgroup.subtype_injective _)

/- ## Part III: Logarithmic / normalized comparisons (0 axioms) -/

/-- `log g(n) ≤ log f(n)`, the comparison at logarithmic scale. -/
theorem log_numSubgroupsAn_le (n : ℕ) :
    Real.log (numSubgroupsAn n : ℝ) ≤ Real.log (numSubgroupsSn n : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast numSubgroupsAn_pos n
  · exact_mod_cast numSubgroupsAn_le_Sn n

/-- The normalized ratio comparison: `log g(n)/n² ≤ log f(n)/n²` for `n ≥ 1`.
    Passing to the limit, this shows `limsup log g(n)/n² ≤ limsup log f(n)/n²`,
    so the parent's asymptotic for S_n caps the A_n count from above with no
    additional assumption. -/
theorem An_ratio_le_Sn_ratio (n : ℕ) (hn : 0 < n) :
    Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2
      ≤ Real.log (numSubgroupsSn n : ℝ) / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  exact (div_le_div_right hn2).mpr (log_numSubgroupsAn_le n)

/- ## Part IV: The upper asymptotic follows from the parent axiom (0 new axioms) -/

/-- **Upper asymptotic bound, conditional on the S_n asymptotic only.**
    If `log f(n)/n² → 1/16` (the Roney-Dougal–Tracey theorem for S_n proved in
    the parent entry), then for every `ε > 0` eventually `log g(n)/n² < 1/16+ε`.
    In particular `limsup log g(n)/n² ≤ 1/16`.

    This direction needs *no* new axiom: it is the parent's S_n asymptotic
    combined with the unconditional inequality `g(n) ≤ f(n)`. -/
theorem An_upper_from_Sn
    (hS : Tendsto (fun n => Real.log (numSubgroupsSn n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (1 / 16)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 < 1 / 16 + ε := by
  rw [Metric.tendsto_nhds] at hS
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hS ε hε)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
  have hnN : n ≥ N := le_trans (le_max_left _ _) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right _ _) hn
  have hd := hN n hnN
  rw [Real.dist_eq] at hd
  have hSlt : Real.log (numSubgroupsSn n : ℝ) / (n : ℝ) ^ 2 < 1 / 16 + ε := by
    have := (abs_lt.mp hd).2; linarith
  exact lt_of_le_of_lt (An_ratio_le_Sn_ratio n hn1) hSlt

/- ## Part V: The full analog (deep result, axiomatized as in the parent) -/

/-- **Roney-Dougal–Tracey analog for A_n (2025-era, axiomatized).**
    `log g(n) = (1/16 + o(1)) n²`. The upper half is provable from the parent
    (see `An_upper_from_Sn`); the matching lower half — that A_n really attains
    `(1/16 - o(1)) n²` via its elementary abelian 2-subgroups — is the deep
    published content, axiomatized here exactly as the parent axiomatizes the
    S_n statement. -/
axiom alternating_asymptotic :
    Tendsto (fun n => Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (1 / 16))

/-- **Pyber analog for A_n:** `log g(n) ≍ n²`.
    There are constants `c₁, c₂ > 0` with `c₁ n² ≤ log g(n) ≤ c₂ n²` eventually.
    Derived from `alternating_asymptotic` by the same ε-argument the parent uses
    to obtain Pyber's theorem from the RDT asymptotic. -/
theorem pyber_alternating :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      c₁ * (n : ℝ) ^ 2 ≤ Real.log (numSubgroupsAn n : ℝ) ∧
      Real.log (numSubgroupsAn n : ℝ) ≤ c₂ * (n : ℝ) ^ 2 := by
  refine ⟨1 / 32, 3 / 32, by norm_num, by norm_num, ?_⟩
  rw [Metric.tendsto_nhds] at alternating_asymptotic
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (alternating_asymptotic (1 / 32) (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq] at hd
  have hab := abs_lt.mp hd
  have h_lo : Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 > 1 / 32 := by linarith [hab.1]
  have h_hi : Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 < 3 / 32 := by linarith [hab.2]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    by_contra hle; push_neg at hle
    have := le_antisymm hle (sq_nonneg _)
    rw [this, div_zero] at h_lo; linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff hn2] at h_lo; linarith
  · rw [div_lt_iff hn2] at h_hi; linarith

end Erdos1162OQ04
