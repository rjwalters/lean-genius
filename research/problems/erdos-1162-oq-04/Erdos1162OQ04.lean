/-
# Erdős Problem #1162, Open Question OQ-04
# The analogous asymptotic for the alternating group A_n

## Question

Erdős #1162 asks for the asymptotic of f(n) = #{subgroups of S_n}. OQ-04 asks:
what is the analogous result for the alternating group A_n?

Write g(n) = #{subgroups of A_n}.

## Main mathematical content of this file

1. **Reduction (0 new axioms):** g(n) ≤ f(n) UNCONDITIONALLY. The inclusion
   A_n ↪ S_n is an injective group homomorphism, so `Subgroup.map` along it
   injects the subgroup lattice of A_n into that of S_n; `Nat.card` is monotone
   under injections into a finite type.

2. **The upper half is FREE.** Composing g(n) ≤ f(n) with the parent
   Roney–Dougal–Tracey asymptotic `log f(n)/n² → 1/16` gives, with NO new axiom,
        limsup log g(n)/n² ≤ 1/16,
   i.e. for every ε > 0 eventually `log g(n)/n² < 1/16 + ε`
   (`An_ratio_eventually_lt`).

3. **Only the lower half is deep.** The single new axiom `An_lower_bound` is the
   A_n analogue of the RDT lower bound. It is genuine new input, but it is a
   MODEST addition: A_n still contains the dominant elementary abelian
   2-subgroups (even-weight products of disjoint transpositions give rank
   ⌊n/2⌋ − 1 on ≈ n/4 support), so the constant is UNCHANGED at 1/16 = (1/4)².

4. Combining (2) and (3) yields the full A_n asymptotic
   `log g(n) = (1/16 + o(1)) n²` (`alternating_asymptotic`) and its Pyber-analog
   (`pyber_alternating`).

## Axiom accounting

This file is **self-contained** (it does not import the parent `Erdos1162Problem`,
whose Mathlib imports have drifted). It therefore carries **exactly two axioms**:

- `roney_dougal_tracey` — the parent S_n asymptotic [RoTr25] (re-declared locally,
  identical to the parent's axiom).
- `An_lower_bound` — the A_n lower half; the only genuinely new input.

The reduction `g(n) ≤ f(n)`, the log/ratio transfer, and the entire upper half are
THEOREMS with no assumptions beyond these two axioms.

References:
- [RoTr25] Roney-Dougal, Tracey, "The number of subgroups of the symmetric
  group" (2025) — parent S_n result.
- [Py93] Pyber, "Enumerating finite groups of given order" (1993).
-/

import Mathlib

open Real Filter

namespace Erdos1162OQ04

/-! ### The S_n baseline (parent result, re-declared self-contained) -/

/-- f(n) = the number of subgroups of the symmetric group S_n. -/
noncomputable def numSubgroups (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/-- **Roney–Dougal–Tracey (2025):** `log f(n) = (1/16 + o(1)) · n²`.
Axiomatized as a deep published result [RoTr25]; identical to the parent
`Erdos1162.roney_dougal_tracey`. -/
axiom roney_dougal_tracey :
    Tendsto (fun n => Real.log (numSubgroups n : ℝ) / (n : ℝ) ^ 2) atTop (nhds (1 / 16))

/-! ### The A_n count -/

/-- g(n) = the number of subgroups of the alternating group A_n, realized as
`alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))` viewed as a group. -/
noncomputable def numSubgroupsAn (n : ℕ) : ℕ :=
  Nat.card (Subgroup (alternatingGroup (Fin n)))

/-- g(n) ≥ 1: the trivial subgroup always exists. -/
theorem numSubgroupsAn_pos (n : ℕ) : 0 < numSubgroupsAn n := by
  unfold numSubgroupsAn
  haveI : Nonempty (Subgroup (alternatingGroup (Fin n))) := ⟨⊥⟩
  exact Nat.card_pos

/-- **Reduction (0 new axioms):** g(n) ≤ f(n).

The subgroup lattice of A_n injects into that of S_n via `H ↦ H.map (A_n).subtype`.
The subtype inclusion is injective, hence so is `Subgroup.map` of it, and
`Nat.card` is monotone under injections into the finite type `Subgroup (S_n)`. -/
theorem numSubgroupsAn_le (n : ℕ) : numSubgroupsAn n ≤ numSubgroups n := by
  -- The inclusion A_n ↪ S_n is injective (it is `Subtype.val` on the carrier).
  have hinj : Function.Injective (alternatingGroup (Fin n)).subtype := by
    intro a b h
    exact Subtype.ext h
  -- Pushforward of subgroups along an injective hom is injective on the lattice.
  have hmap : Function.Injective
      (Subgroup.map (alternatingGroup (Fin n)).subtype) :=
    Subgroup.map_injective hinj
  -- `Subgroup (S_n)` is finite, so `Nat.card` is monotone under this injection.
  haveI : Finite (Subgroup (Equiv.Perm (Fin n))) := inferInstance
  unfold numSubgroupsAn numSubgroups
  exact Nat.card_le_card_of_injective _ hmap

/-- Monotonicity of `log` transfers the count bound: log g(n) ≤ log f(n). -/
theorem log_numSubgroupsAn_le (n : ℕ) :
    Real.log (numSubgroupsAn n : ℝ) ≤ Real.log (numSubgroups n : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast numSubgroupsAn_pos n
  · exact_mod_cast numSubgroupsAn_le n

/-- Ratio (n²-normalized) form of the transfer:
`log g(n)/n² ≤ log f(n)/n²` for all n (both sides are 0 at n = 0). -/
theorem An_ratio_le (n : ℕ) :
    Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2
      ≤ Real.log (numSubgroups n : ℝ) / (n : ℝ) ^ 2 := by
  gcongr <;>
    first
      | exact_mod_cast numSubgroupsAn_pos n
      | exact_mod_cast numSubgroupsAn_le n

/-- **Upper half is FREE (0 new axioms).**
Using only the parent S_n asymptotic `roney_dougal_tracey`, the A_n ratio is
eventually below `1/16 + ε` for every ε > 0. This is `limsup log g(n)/n² ≤ 1/16`. -/
theorem An_ratio_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 < 1 / 16 + ε := by
  have hrdt := roney_dougal_tracey
  rw [Metric.tendsto_nhds] at hrdt
  filter_upwards [hrdt ε hε] with n hd
  rw [Real.dist_eq] at hd
  have hf : Real.log (numSubgroups n : ℝ) / (n : ℝ) ^ 2 < 1 / 16 + ε := by
    have := (abs_lt.mp hd).2
    linarith
  exact lt_of_le_of_lt (An_ratio_le n) hf

/-- **The single new axiom: the matching LOWER bound for A_n.**

A_n contains an elementary abelian 2-subgroup of rank ⌊n/2⌋ − 1 (the even-weight
subgroup of the ⌊n/2⌋ disjoint-transposition 2-group), and the dominant subgroup
contribution comes from ≈ n/4 support, so the constant is the same 1/16 = (1/4)²
as for S_n. Axiomatized as the A_n analogue of the Roney–Dougal–Tracey lower
bound — the only ingredient not derivable from the S_n result. -/
axiom An_lower_bound :
    ∀ ε > 0, ∀ᶠ n in atTop,
      1 / 16 - ε < Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2

/-- **The A_n asymptotic:** `log g(n) = (1/16 + o(1)) n²`.

Upper half from the S_n result (`An_ratio_eventually_lt`, 0 new axioms);
lower half from `An_lower_bound` (1 new axiom). Same constant 1/16 as S_n. -/
theorem alternating_asymptotic :
    Tendsto (fun n => Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (1 / 16)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [An_ratio_eventually_lt ε hε, An_lower_bound ε hε] with n hup hlo
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Pyber-analog for A_n:** log g(n) ≍ n².
There are constants c₁, c₂ > 0 with c₁ n² ≤ log g(n) ≤ c₂ n² for all large n.
Follows from the A_n asymptotic exactly as the S_n Pyber theorem follows from
the S_n asymptotic. -/
theorem pyber_alternating :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      c₁ * (n : ℝ) ^ 2 ≤ Real.log (numSubgroupsAn n : ℝ) ∧
      Real.log (numSubgroupsAn n : ℝ) ≤ c₂ * (n : ℝ) ^ 2 := by
  refine ⟨1 / 32, 3 / 32, by norm_num, by norm_num, ?_⟩
  have h := alternating_asymptotic
  rw [Metric.tendsto_nhds] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h (1 / 32) (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq] at hd
  have hab := abs_lt.mp hd
  have h_lo : Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 > 1 / 32 := by
    linarith [hab.1]
  have h_hi : Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 < 3 / 32 := by
    linarith [hab.2]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    by_contra hle
    push_neg at hle
    have := le_antisymm hle (sq_nonneg _)
    rw [this, div_zero] at h_lo
    linarith
  refine ⟨?_, ?_⟩
  · have := (lt_div_iff₀ hn2).mp h_lo; linarith
  · have := (div_lt_iff₀ hn2).mp h_hi; linarith

/- ## Small cases (sanity checks)

Note the contrast with S_n at n = 2: |A_2| = 1 (the only even permutation of two
points is the identity), so g(2) = 1 whereas f(2) = 2.

    g(1) = 1   (A_1 trivial)
    g(2) = 1   (A_2 trivial)
    g(3) = 2   (A_3 ≅ Z/3, prime cyclic: only ⊥ and ⊤)
    g(4) = 10  (A_4 order 12; ⊥, ⊤, three ⟨(ab)(cd)⟩, one V₄, four ⟨3-cycle⟩)

These are stated informally; a machine-checked small case via `native_decide` would
introduce the `Lean.ofReduceBool` compiler-kernel axiom, so it is deliberately
omitted to keep the axiom set to exactly the two intended mathematical axioms. -/

end Erdos1162OQ04
