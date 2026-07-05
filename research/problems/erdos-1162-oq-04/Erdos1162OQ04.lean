/-
# Erdős Problem #1162, Open Question OQ-04
# The analogous asymptotic for the alternating group A_n

CANDIDATE — **UNVERIFIED** (Docker build blocked by containerd blob EIO;
Aristotle offline 404). This file is intentionally kept OUTSIDE `proofs/Proofs/`
so that the lakefile glob `["Proofs", "Proofs.*"]` does not attempt to compile it
before it has been verified. Once the build infrastructure recovers, verify it
(`./proofs/scripts/docker-build.sh Proofs.Erdos1162OQ04` after moving it into
`proofs/Proofs/`) and address the API-name checklist at the bottom.

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

- Inherited from parent (already axiomatized in Erdos1162Problem.lean):
  `Erdos1162.roney_dougal_tracey`  (the S_n asymptotic).
- **New in this file: exactly ONE axiom** — `An_lower_bound` (the A_n lower half).
- The reduction, the log/ratio transfer, and the upper half are all THEOREMS
  with no new assumptions.

References:
- [RoTr25] Roney-Dougal, Tracey, "The number of subgroups of the symmetric
  group" (2025) — parent S_n result.
- [Py93] Pyber, "Enumerating finite groups of given order" (1993).
-/

import Mathlib
import Proofs.Erdos1162Problem

open Real Filter

namespace Erdos1162OQ04

open Erdos1162 (numSubgroups)

/-- g(n) = the number of subgroups of the alternating group A_n, realized as
`alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))` viewed as a group. -/
noncomputable def numSubgroupsAn (n : ℕ) : ℕ :=
  Nat.card (Subgroup (alternatingGroup (Fin n)))

/-- g(n) ≥ 1: the trivial subgroup always exists. -/
theorem numSubgroupsAn_pos (n : ℕ) : 0 < numSubgroupsAn n := by
  unfold numSubgroupsAn
  exact Nat.card_pos_of_nonempty ⟨⊥⟩

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
  gcongr
  exact log_numSubgroupsAn_le n

/-- **Upper half is FREE (0 new axioms).**
Using only the parent S_n asymptotic `roney_dougal_tracey`, the A_n ratio is
eventually below `1/16 + ε` for every ε > 0. This is `limsup log g(n)/n² ≤ 1/16`. -/
theorem An_ratio_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.log (numSubgroupsAn n : ℝ) / (n : ℝ) ^ 2 < 1 / 16 + ε := by
  have hrdt := Erdos1162.roney_dougal_tracey
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
Follows from the A_n asymptotic exactly as `Erdos1162.pyber_theorem` follows from
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
  · rw [lt_div_iff hn2] at h_lo; linarith
  · rw [div_lt_iff hn2] at h_hi; linarith

/- ## Small cases (sanity checks)

Note the contrast with S_n at n = 2: |A_2| = 1 (the only even permutation of two
points is the identity), so g(2) = 1 whereas f(2) = 2.

    g(1) = 1   (A_1 trivial)
    g(2) = 1   (A_2 trivial)
    g(3) = 2   (A_3 ≅ Z/3, prime cyclic: only ⊥ and ⊤)
    g(4) = 10  (A_4 order 12; ⊥, ⊤, three ⟨(ab)(cd)⟩, one V₄, four ⟨3-cycle⟩)

`g(3)` is stated below via `native_decide` (which would introduce the
`Lean.ofReduceBool` compiler-kernel axiom; kept commented so this candidate has
exactly the one intended mathematical axiom `An_lower_bound`). Uncomment and
count `Lean.ofReduceBool` if a machine-checked small case is wanted. -/

-- theorem g3 : numSubgroupsAn 3 = 2 := by
--   unfold numSubgroupsAn
--   simp only [Nat.card_eq_fintype_card]
--   native_decide

end Erdos1162OQ04

/- ## API-name verification checklist (verify once Docker/Mathlib available)

The proofs above are written against Mathlib 4.26 from memory; the following
names/signatures must be confirmed (they are the only points of uncertainty):

1. `alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))`
   — requires `[Fintype (Fin n)] [DecidableEq (Fin n)]` (both available). ✓ likely.
2. `Subgroup.map_injective : Function.Injective f → Function.Injective (Subgroup.map f)`.
3. `Nat.card_le_card_of_injective (f) (hf : Function.Injective f) [Finite β] :
      Nat.card α ≤ Nat.card β`.
4. `Finite (Subgroup (Equiv.Perm (Fin n)))` instance auto-synthesizes
   (the parent file's Session-4 note records an `instFiniteSubgroupPerm`; a
   global `[Finite G] → Finite (Subgroup G)` instance should also apply).
5. `(alternatingGroup (Fin n)).subtype a` is defeq to `a.val` so that
   `intro a b h; exact Subtype.ext h` closes injectivity. If not, replace with
   `Subgroup.subtype_injective _` or `by simp [Subgroup.coe_subtype];
   exact Subtype.val_injective`.
6. `Real.log_le_log (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y`
   — direction/arg order (possible alt: `Real.log_le_log_right`).
7. `gcongr` discharges `a/c ≤ b/c` from `a ≤ b` with `0 ≤ (n:ℝ)^2` by positivity.
   Fallback: `(div_le_div_iff_right hn2).mpr` with an `n = 0` case split.
8. `Metric.tendsto_nhds`, `Real.dist_eq`, `abs_lt`, `Filter.eventually_atTop`,
   `lt_div_iff`, `div_lt_iff` — all used identically to the VERIFIED parent
   proof `Erdos1162.rdt_implies_pyber`, so these are high-confidence.

Points 6–8 mirror the already-verified parent file; points 2–5 are the genuine
new API surface to confirm.
-/
