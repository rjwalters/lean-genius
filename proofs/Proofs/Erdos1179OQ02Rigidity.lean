/-
Proof: Rigidity / equality case for the Erdős #1179 oq-02 trivial lower bound.
Date: 2026-06-15 (S4)
Research: erdos-1179-oq-02 (researcher-7)

oq-02 sharpens the Erdős–Hall `(1+o(1))` factor to a bounded additive error.
The merged sibling `Erdos1179OQ02.lean` (#24551) proved the per-subset trivial
lower bound axiom-free:

    if `A` is ε-uniform with `ε < 1`, then `N ≤ 2 ^ |A|`           (so `|A| ≥ ⌈log₂ N⌉`).

This file proves the matching **rigidity / equality statement**: an ε-uniform
set *saturates* that lower bound (`N = 2 ^ |A|`, equivalently `|A| = ⌈log₂ N⌉`
on a power-of-two group) **iff** every group element has a *unique* subset-sum
representation.  In other words, the extremal subsets of the trivial bound are
precisely the unique-representation sets — the perfectly-uniform (`0`-uniform)
configurations that the deterministic upper companion `Erdos1179OQ02Upper.lean`
exhibits on bases of `(ZMod 2)^m`.

Mathematical content.  ε-uniformity with `ε < 1` already forces every count
`F_A(g) ≥ 1` (`epsUniform_spanning`), and the counts always sum to `2 ^ |A|`
(`total_reprCount`).  There are exactly `N` summands.  If `N = 2 ^ |A|` then the
sum of `N` integers each `≥ 1` equals `N`, forcing each to be exactly `1`;
conversely if each count is `1` the sum is `N = 2 ^ |A|`.  This is a clean
counting rigidity — no probability, no axioms.

No axioms; depends only on `Erdos1179.epsUniform_spanning` (from
`Proofs/Erdos1179OQ02.lean`) and `Erdos1179.total_reprCount` (from the parent
`Proofs/Erdos1179Problem.lean`).

Mathlib bearer name-checked @ pinned rev 2df2f01:
`Finset.sum_eq_sum_iff_of_le` — the `@[to_additive]` image of
`Finset.prod_eq_prod_iff_of_le`
(Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:512):
`(h : ∀ i ∈ s, f i ≤ g i) : (∑ i ∈ s, f i = ∑ i ∈ s, g i) ↔ ∀ i ∈ s, f i = g i`.

Build-verified (researcher-8, 2026-06-19) and registered in `Proofs.lean` via
`./proofs/scripts/docker-build.sh Proofs.Erdos1179OQ02Rigidity`:
`✔ [7745/7745] Built Proofs.Erdos1179OQ02Rigidity` — 0 sorries, 0 axioms (the
prior build-pending note, written under a Docker blackout, is now discharged).
-/

import Proofs.Erdos1179OQ02
import Mathlib

namespace Erdos1179

open Finset

/-- **Saturation ⇔ unique representations.**  For an ε-uniform subset `A` of an
abelian group of order `N` with `ε < 1`, the trivial lower bound `N ≤ 2 ^ |A|`
is attained with equality (`N = 2 ^ |A|`) **iff** every element has exactly one
subset-sum representation.

The forward direction is the rigidity statement: the extremal sets of the
trivial bound are exactly the unique-representation (perfectly `0`-uniform)
sets.  The reverse direction is the elementary count `∑_g 1 = 2^|A|`. -/
theorem epsUniform_saturated_iff_unique_repr {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) :
    Fintype.card G = 2 ^ A.card ↔ ∀ g : G, reprCount A g = 1 := by
  constructor
  · -- Saturation forces uniqueness.
    intro hsat g
    -- Every count is ≥ 1, and the counts sum to 2^|A| = N = ∑_g 1.
    have hspan : ∀ g' : G, (1 : ℕ) ≤ reprCount A g' :=
      fun g' => epsUniform_spanning A ε hε1 hunif g'
    have hsum : (∑ _g' : G, (1 : ℕ)) = ∑ g' : G, reprCount A g' := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        total_reprCount, hsat]
    -- Pointwise `≥` together with equal sums forces termwise equality.
    have hone :=
      (Finset.sum_eq_sum_iff_of_le (fun g' _ => hspan g')).mp hsum g (Finset.mem_univ g)
    exact hone.symm
  · -- Uniqueness gives the count `∑_g 1 = 2^|A|`, i.e. `N = 2^|A|`.
    intro h
    have hsum := total_reprCount A
    rw [Finset.sum_congr rfl (fun g _ => h g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one] at hsum
    exact hsum

/-- **Rigidity (forward direction, standalone).**  An ε-uniform set (`ε < 1`)
that saturates the trivial lower bound `N ≤ 2 ^ |A|` gives every group element a
*unique* subset-sum representation. -/
theorem unique_repr_of_epsUniform_saturated {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) (hsat : Fintype.card G = 2 ^ A.card) (g : G) :
    reprCount A g = 1 :=
  (epsUniform_saturated_iff_unique_repr A ε hε1 hunif).mp hsat g

/-- **Logarithmic form of the equality case.**  On a power-of-two group an
ε-uniform set (`ε < 1`) attains the integer lower bound `|A| = ⌈log₂ N⌉` exactly
when its representations are unique.  (`Nat.clog 2 (2 ^ m) = m` via
`Nat.clog_pow`.) -/
theorem epsUniform_card_eq_clog_iff_unique_repr {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) :
    (Fintype.card G = 2 ^ A.card ∧ A.card = Nat.clog 2 (Fintype.card G))
      ↔ ∀ g : G, reprCount A g = 1 := by
  rw [← epsUniform_saturated_iff_unique_repr A ε hε1 hunif]
  constructor
  · exact fun h => h.1
  · intro hsat
    exact ⟨hsat, by rw [hsat, Nat.clog_pow 2 A.card (by norm_num)]⟩

end Erdos1179
