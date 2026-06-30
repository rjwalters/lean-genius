/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: researcher-8
-/
import Mathlib
import Proofs.SpernerSimplicialInstance
import Proofs.SpernerSimplicialInstanceOQ05Scarf1d

/-
# Continuous-coloring → Sperner-coloring reduction (interval case of Brouwer)

`sperner-simplicial-instance-oq-04` asks to build Brouwer's fixed-point theorem
on top of the 1-d Sperner lemma (`interval_sperner`) by combining it with a
mesh refinement and a **continuous-coloring → Sperner-coloring reduction**.

This file formalizes the explicitly-named *interval* (1-d) deliverable: the
reduction that turns a real function `f : ℝ → ℝ` with `f 0 ≤ 0 ≤ f 1` into the
sign 2-coloring of the mesh `{0, 1/m, …, 1}` and feeds it to the already-proven
discrete intermediate-value theorem
(`SpernerSimplicialInstanceOQ05Scarf1d.discrete_ivt_panchromatic_cell`).

The output is, for **every** mesh `m > 0`, a width-`1/m` cell whose two endpoints
straddle a sign change of `f`. This is the discrete intermediate-value theorem
for a real-valued `f`, and it is the base from which the continuous IVT follows
by letting `m → ∞` (Bolzano–Weierstrass + continuity); that limit step, and the
`n`-dimensional Brouwer derivation via barycentric subdivision, are recorded as
the open remainder in `knowledge.md` — they are not in this file.

No `sorry`, no `axiom`. Builds on the axiom-free discrete theorem.
-/

namespace SpernerSimplicialInstanceOQ04

open SpernerSimplicialInstanceOQ05Scarf1d

/-- The `j`-th mesh point of `{0, 1/m, …, 1}`: `meshPt m j = j / m`. -/
noncomputable def meshPt (m : ℕ) (j : ℕ) : ℝ := (j : ℝ) / (m : ℝ)

/-- The **sign 2-coloring** of the mesh induced by `f`: vertex `j` is colored
`0` when `f` is `≤ 0` at the mesh point `j / m`, and `1` otherwise. This is the
continuous-coloring → Sperner-coloring reduction in the 1-d case. -/
noncomputable def signColoring (f : ℝ → ℝ) (m : ℕ) : ℕ → Fin 2 :=
  fun j => if f (meshPt m j) ≤ 0 then 0 else 1

/-- Definitional unfolding of `signColoring` at a vertex (`rfl`). -/
lemma signColoring_apply (f : ℝ → ℝ) (m j : ℕ) :
    signColoring f m j = if f (meshPt m j) ≤ 0 then 0 else 1 := rfl

@[simp] lemma meshPt_zero (m : ℕ) : meshPt m 0 = 0 := by simp [meshPt]

lemma meshPt_self {m : ℕ} (hm : 0 < m) : meshPt m m = 1 := by
  unfold meshPt
  rw [div_self]
  exact_mod_cast hm.ne'

/-- Left endpoint color is `0` when `f 0 ≤ 0`. -/
lemma signColoring_zero (f : ℝ → ℝ) {m : ℕ} (h0 : f 0 ≤ 0) :
    signColoring f m 0 = 0 := by
  rw [signColoring_apply, meshPt_zero]
  exact if_pos h0

/-- Right endpoint color is `1` when `0 < f 1`. -/
lemma signColoring_self (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m) (h1 : 0 < f 1) :
    signColoring f m m = 1 := by
  rw [signColoring_apply, meshPt_self hm]
  exact if_neg (not_le.mpr h1)

/-- **Discrete intermediate-value theorem for a real function** (interval case
of the Sperner→Brouwer reduction).

For any `f : ℝ → ℝ` with `f 0 ≤ 0 < f 1` and any mesh `m > 0`, there is a cell
`i : Fin m` whose two mesh endpoints `i/m` and `(i+1)/m` straddle a sign change
of `f`. Proven by applying the combinatorial discrete IVT to the sign coloring;
no continuity is needed for this discrete statement. -/
theorem exists_sign_change_cell (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m)
    (h0 : f 0 ≤ 0) (h1 : 0 < f 1) :
    ∃ i : Fin m,
      (f (meshPt m i.val) ≤ 0 ∧ 0 < f (meshPt m (i.val + 1))) ∨
      (0 < f (meshPt m i.val) ∧ f (meshPt m (i.val + 1)) ≤ 0) := by
  have hpar : signColoring f m 0 ≠ signColoring f m m := by
    rw [signColoring_zero f h0, signColoring_self f hm h1]
    decide
  obtain ⟨i, hi⟩ :=
    SpernerSimplicialInstanceOQ05Scarf1d.discrete_ivt_panchromatic_cell
      (signColoring f m) hm hpar
  refine ⟨i, ?_⟩
  simp only [IsPanchromatic1d, signColoring_apply] at hi
  by_cases ha : f (meshPt m i.val) ≤ 0 <;> by_cases hb : f (meshPt m (i.val + 1)) ≤ 0
  · rw [if_pos ha, if_pos hb] at hi; exact absurd rfl hi
  · exact Or.inl ⟨ha, not_le.mp hb⟩
  · exact Or.inr ⟨not_le.mp ha, hb⟩
  · rw [if_neg ha, if_neg hb] at hi; exact absurd rfl hi

/-- Product form of the sign-change cell: the two mesh endpoints of some cell
have opposite signs (`f(a)·f(b) ≤ 0`). A uniform restatement of
`exists_sign_change_cell` independent of which way the sign flips. -/
theorem exists_sign_change_bracket (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m)
    (h0 : f 0 ≤ 0) (h1 : 0 < f 1) :
    ∃ i : Fin m, f (meshPt m i.val) * f (meshPt m (i.val + 1)) ≤ 0 := by
  obtain ⟨i, hi⟩ := exists_sign_change_cell f hm h0 h1
  refine ⟨i, ?_⟩
  rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact mul_nonpos_iff.mpr (Or.inr ⟨ha, hb.le⟩)
  · exact mul_nonpos_iff.mpr (Or.inl ⟨ha.le, hb⟩)

end SpernerSimplicialInstanceOQ04
