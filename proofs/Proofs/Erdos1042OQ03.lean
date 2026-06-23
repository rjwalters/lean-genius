/-
Erdős Problem #1042 — open question oq-03:
"What other geometric properties of the root set affect the component count of
the lemniscate?"

The parent entry (#1042, resolved by Ghosh–Ramachandran 2024) records the
*answers* about the transfinite diameter as axioms. This companion isolates and
fully PROVES the elementary geometric mechanism that sits underneath every
component-count bound: the ROOTS of f confine its lemniscate.

For a monic polynomial f(z) = ∏ᵢ (z - rootᵢ) the lemniscate {z : |f(z)| < 1}
is contained in the union of the OPEN UNIT BALLS centred at the roots of f:
every point where |f| < 1 lies within distance 1 of some root, because if z
were ≥ 1 away from all roots then |f(z)| = ∏ᵢ|z - rootᵢ| ≥ 1. Consequently the
lemniscate is open, bounded, and (in positive degree) nonempty — it always
contains each root. This confinement is exactly the geometric input that forces
the classical "at most n components" bound (each bounded component must trap a
root) and is why the *positions* of the roots — not merely the transfinite
diameter of the ambient set — govern the component count.

All results below are axiom-free and self-contained; the structures are
re-declared locally so that nothing depends on the parent's axioms
(`transfiniteDiameter`, `ghosh_ramachandran_*`).
-/

import Mathlib

open Complex BigOperators Metric

namespace Erdos1042OQ03

/-- A monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` of a given degree, recorded by its
list of roots. -/
structure RootedPoly where
  degree : ℕ
  roots : Fin degree → ℂ

/-- The monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` evaluated at `z`. -/
noncomputable def RootedPoly.eval (p : RootedPoly) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The lemniscate of `p`, the open sublevel set `{z : |f(z)| < 1}`. -/
def lem (p : RootedPoly) : Set ℂ :=
  {z : ℂ | Complex.abs (p.eval z) < 1}

/-- The polynomial map `z ↦ f(z)` is continuous (a finite product of the
continuous maps `z ↦ z - rootᵢ`). -/
theorem continuous_eval (p : RootedPoly) : Continuous p.eval := by
  unfold RootedPoly.eval
  exact continuous_finset_prod _ fun i _ => continuous_id.sub continuous_const

/-- The lemniscate is open: it is the preimage of the open ray `(-∞, 1)` under the
continuous map `z ↦ |f(z)|`. -/
theorem isOpen_lem (p : RootedPoly) : IsOpen (lem p) := by
  have h : Continuous fun z => Complex.abs (p.eval z) :=
    Complex.continuous_abs.comp (continuous_eval p)
  show IsOpen ((fun z => Complex.abs (p.eval z)) ⁻¹' Set.Iio 1)
  exact h.isOpen_preimage (Set.Iio 1) isOpen_Iio

/-- Each root of `f` lies in the lemniscate: `f(rootᵢ) = 0`, and `|0| = 0 < 1`. -/
theorem root_mem_lem (p : RootedPoly) (i : Fin p.degree) : p.roots i ∈ lem p := by
  have h0 : p.eval (p.roots i) = 0 := by
    unfold RootedPoly.eval
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  show Complex.abs (p.eval (p.roots i)) < 1
  rw [h0]; simp

/-- In positive degree the lemniscate is nonempty (it contains the first root). -/
theorem lem_nonempty (p : RootedPoly) (hp : 0 < p.degree) : (lem p).Nonempty :=
  ⟨p.roots ⟨0, hp⟩, root_mem_lem p ⟨0, hp⟩⟩

/-- **Confinement.** Every point of the lemniscate lies within distance 1 of some
root: if `z` were `≥ 1` away from all roots then `|f(z)| = ∏ᵢ|z - rootᵢ| ≥ 1`,
contradicting `z ∈ lem p`. -/
theorem lem_near_root (p : RootedPoly) {z : ℂ} (hz : z ∈ lem p) :
    ∃ i : Fin p.degree, Complex.abs (z - p.roots i) < 1 := by
  by_contra h
  push_neg at h
  have h1 : (1 : ℝ) ≤ Complex.abs (p.eval z) := by
    unfold RootedPoly.eval
    rw [map_prod]
    exact Finset.one_le_prod' fun i _ => h i
  have hz' : Complex.abs (p.eval z) < 1 := hz
  exact absurd hz' (not_lt.mpr h1)

/-- **Geometric confinement of the lemniscate.** The lemniscate is contained in the
union of the open unit balls centred at the roots of `f`. Since there are exactly
`degree` such balls, this is the geometric source of the classical "at most `n`
connected components" bound. -/
theorem lem_subset_iUnion_ball (p : RootedPoly) :
    lem p ⊆ ⋃ i : Fin p.degree, Metric.ball (p.roots i) 1 := by
  intro z hz
  obtain ⟨i, hi⟩ := lem_near_root p hz
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  exact hi

/-- The lemniscate is bounded: it sits inside a finite union of unit balls. -/
theorem isBounded_lem (p : RootedPoly) : Bornology.IsBounded (lem p) := by
  have hb : Bornology.IsBounded (⋃ i : Fin p.degree, Metric.ball (p.roots i) 1) :=
    isBounded_iUnion.mpr fun _ => Metric.isBounded_ball
  exact hb.subset (lem_subset_iUnion_ball p)

/-- **Capstone.** Every polynomial lemniscate is an open, bounded subset of ℂ
confined to the union of the open unit balls about the roots of `f`. The root
geometry — not just the transfinite diameter of the ambient set — therefore
controls where the lemniscate (and hence each of its components) can live. -/
theorem geometric_confinement (p : RootedPoly) :
    IsOpen (lem p) ∧ Bornology.IsBounded (lem p) ∧
      lem p ⊆ ⋃ i : Fin p.degree, Metric.ball (p.roots i) 1 :=
  ⟨isOpen_lem p, isBounded_lem p, lem_subset_iUnion_ball p⟩

end Erdos1042OQ03
