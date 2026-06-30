/-
Proof: Existence witness for the extremal (additive-constant-zero) case of Erdős #1179 oq-02.
Date: 2026-06-18 (S4)
Research: erdos-1179-oq-02 (researcher-4)

oq-02 asks whether the Erdős–Hall `(1+o(1))` multiplicative factor in
`g_ε(N) = (1+o_ε(1))·log₂N` can be sharpened to a bounded *additive* error
`g_ε(N) ≤ log₂N + O_ε(1)`, matching the trivial lower bound `g_ε(N) ≥ log₂N`.

The sibling files prove a chain of results that are all **conditional** on the
existence of a *unique-representation set* — a finset `A ⊆ G` with
`reprCount A g = 1` for every `g`:

  * `Erdos1179OQ02.lean`      — lower bound `g_ε(N) ≥ log₂N` (per-subset).
  * `Erdos1179OQ02Upper.lean` — IF such an `A` exists, it is exactly `0`-uniform
                                and has size exactly `⌈log₂N⌉`.
  * `Erdos1179OQ02Extremal/Rigidity.lean` — rigidity/uniqueness of such `A`.

Every one of those theorems takes the hypothesis `∀ g, reprCount A g = 1` (or
`IsEpsUniform A 0`) as an *assumption*.  Until a witness is exhibited, the whole
edifice is vacuous: it might describe the empty class of groups.

This file removes that gap.  It constructs the **standard basis** of the
elementary abelian 2-group `G = (Fin m → ZMod 2)` (order `N = 2^m`) as the
finset `stdBasis m = { Pi.single i 1 : i ∈ Fin m }`, and proves *from first
principles* (axiom-free) that it is a unique-representation set:

    ∀ g, reprCount (stdBasis m) g = 1.

Consequences, now **unconditional** for every `m`:

  * `additive_constant_zero_attained` — `stdBasis m` is exactly `0`-uniform and
    has size exactly `⌈log₂N⌉`.  So the conjectured additive sharpening of oq-02
    holds with additive constant **`0`**, *deterministically* (not merely w.h.p.),
    for the infinite family of orders `N = 2^m`.  This certifies the additive
    constant can never be forced positive in general, and makes all the
    conditional sibling theorems non-vacuous.

Mathematical content.  For the standard basis, the subset-sum map
`S ↦ ∑_{x∈S} x` is a bijection from subsets of the basis onto `G`: a subset `T`
of coordinates maps to its indicator vector, and `g` is recovered as its support
`{i : g i = 1}`.  Concretely we show (a) every `g` is hit — spanning,
`1 ≤ reprCount`, via the explicit subset `T = {i : g i = 1}` — and (b)
`N = 2^|A|` (parent `total_reprCount`).  Since `∑_g reprCount = 2^|A| = N = ∑_g 1`
with each term `≥ 1`, equality forces every term to be exactly `1`
(`Finset.sum_eq_sum_iff_of_le`).

No axioms; depends only on `Erdos1179.reprCount`, `Erdos1179.IsEpsUniform`,
`Erdos1179.expectedReprCount` and `Erdos1179.total_reprCount` from the parent
`Proofs/Erdos1179Problem.lean`.
-/

import Proofs.Erdos1179Problem
import Mathlib

namespace Erdos1179

open Finset

/-- The `i`-th standard basis vector of `(Fin m → ZMod 2)`: the indicator of
coordinate `i`. -/
def basisVec (m : ℕ) (i : Fin m) : Fin m → ZMod 2 := Pi.single i (1 : ZMod 2)

/-- The standard basis of `(Fin m → ZMod 2)`, as a finset of `m` indicator
vectors. -/
def stdBasis (m : ℕ) : Finset (Fin m → ZMod 2) :=
  Finset.univ.image (basisVec m)

/-- The standard basis vectors are pairwise distinct (`1 ≠ 0` in `ZMod 2`). -/
theorem basisVec_injective (m : ℕ) : Function.Injective (basisVec m) := by
  intro i j h
  by_contra hij
  have h' : basisVec m i i = basisVec m j i := congrFun h i
  rw [basisVec, basisVec, Pi.single_eq_same, Pi.single_eq_of_ne hij] at h'
  exact one_ne_zero h'

/-- The standard basis has exactly `m` elements. -/
theorem stdBasis_card (m : ℕ) : (stdBasis m).card = m := by
  rw [stdBasis, Finset.card_image_of_injective _ (basisVec_injective m),
    Finset.card_univ, Fintype.card_fin]

/-- `(Fin m → ZMod 2)` has `2^m` elements. -/
theorem card_pi_zmod_two (m : ℕ) : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Spanning.**  Every `g : (Fin m → ZMod 2)` has at least one subset-sum
representation from the standard basis: the explicit subset of basis vectors
indexed by the support `{i : g i = 1}` sums to `g`. -/
theorem stdBasis_spanning (m : ℕ) (g : Fin m → ZMod 2) :
    1 ≤ reprCount (stdBasis m) g := by
  classical
  set T : Finset (Fin m) := Finset.univ.filter (fun i => g i = 1) with hT
  have hSsub : (T.image (basisVec m)) ⊆ stdBasis m := by
    rw [stdBasis]
    exact Finset.image_subset_image (Finset.subset_univ T)
  have hsum : (T.image (basisVec m)).sum id = g := by
    rw [Finset.sum_image (fun x _ y _ hxy => basisVec_injective m hxy)]
    funext j
    rw [Finset.sum_apply]
    have hterm : ∀ i, id (basisVec m i) j = (if j = i then (1 : ZMod 2) else 0) := by
      intro i; simp [basisVec, Pi.single_apply]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ T) => hterm i)]
    simp only [Finset.sum_ite_eq, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (g j) with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  have hmem : (T.image (basisVec m)) ∈
      (stdBasis m).powerset.filter (fun U => U.sum id = g) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSsub, hsum⟩
  have hpos : 0 < reprCount (stdBasis m) g := by
    simp only [reprCount]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- **Unique representations.**  The standard basis of `(Fin m → ZMod 2)` gives
every group element *exactly one* subset-sum representation.  This is the witness
that the conditional sibling theorems (`Erdos1179OQ02Upper`/`Extremal`/`Rigidity`)
assume but never construct. -/
theorem stdBasis_unique_repr (m : ℕ) (g : Fin m → ZMod 2) :
    reprCount (stdBasis m) g = 1 := by
  have hspan : ∀ h, 1 ≤ reprCount (stdBasis m) h := stdBasis_spanning m
  have htot : (∑ h, reprCount (stdBasis m) h) = 2 ^ (stdBasis m).card :=
    total_reprCount (stdBasis m)
  have hcardG : Fintype.card (Fin m → ZMod 2) = 2 ^ (stdBasis m).card := by
    rw [card_pi_zmod_two, stdBasis_card]
  have heq : (∑ _h : (Fin m → ZMod 2), (1 : ℕ))
      = ∑ h : (Fin m → ZMod 2), reprCount (stdBasis m) h := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, htot, ← hcardG]
  have hall := (Finset.sum_eq_sum_iff_of_le (fun h _ => hspan h)).mp heq
  exact (hall g (Finset.mem_univ g)).symm

/-- There **exists** a unique-representation set in `(Fin m → ZMod 2)` for every
`m`.  Existential form of `stdBasis_unique_repr`. -/
theorem exists_unique_repr_set (m : ℕ) :
    ∃ A : Finset (Fin m → ZMod 2), ∀ g, reprCount A g = 1 :=
  ⟨stdBasis m, stdBasis_unique_repr m⟩

/-- The standard basis has size exactly `⌈log₂N⌉ = Nat.clog 2 N`, the lower
bound — i.e. it meets `g_ε(N) ≥ log₂N` with equality. -/
theorem stdBasis_card_eq_clog (m : ℕ) :
    (stdBasis m).card = Nat.clog 2 (Fintype.card (Fin m → ZMod 2)) := by
  rw [card_pi_zmod_two, Nat.clog_pow 2 m (by norm_num : 1 < 2), stdBasis_card]

/-- The standard basis is **exactly `0`-uniform**: every representation count
equals the expected value `μ = 2^|A| / N = 1`. -/
theorem stdBasis_epsUniform_zero (m : ℕ) : IsEpsUniform (stdBasis m) 0 := by
  intro g
  have hrep : reprCount (stdBasis m) g = 1 := stdBasis_unique_repr m g
  have hμ : expectedReprCount (stdBasis m).card (Fintype.card (Fin m → ZMod 2)) = 1 := by
    unfold expectedReprCount
    rw [card_pi_zmod_two, stdBasis_card,
      show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m by push_cast; ring,
      div_self (by positivity)]
  rw [hrep, hμ]
  norm_num

/-- **Additive constant zero is attained, deterministically, for `N = 2^m`.**
For every `m` there is a subset `A` of the elementary abelian 2-group
`(Fin m → ZMod 2)` (order `N = 2^m`) that is *exactly* `0`-uniform and has size
*exactly* `⌈log₂N⌉`.  Hence the conjectured additive sharpening of oq-02,
`g_ε(N) ≤ log₂N + O_ε(1)`, holds with additive constant `0` (and `ε = 0`) on this
infinite family — so the additive constant can never be forced positive in
general, and the conditional optimality theorems of the sibling files are
non-vacuous. -/
theorem additive_constant_zero_attained (m : ℕ) :
    ∃ A : Finset (Fin m → ZMod 2),
      IsEpsUniform A 0 ∧ A.card = Nat.clog 2 (Fintype.card (Fin m → ZMod 2)) :=
  ⟨stdBasis m, stdBasis_epsUniform_zero m, stdBasis_card_eq_clog m⟩

end Erdos1179
