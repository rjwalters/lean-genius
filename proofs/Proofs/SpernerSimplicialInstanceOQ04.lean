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

The output of that reduction is, for **every** mesh `m > 0`, a width-`1/m` cell
whose two endpoints straddle a sign change of `f` (`exists_sign_change_cell` /
`exists_sign_change_bracket`) — the discrete intermediate-value theorem for a
real-valued `f`, needing no continuity.

The file then **takes the continuous limit** `m → ∞`. `ivt_of_shrinking_brackets`
isolates the analytic content, stated independently of Sperner: a continuous `f`
with sign-changing brackets of width `→ 0` in `[0,1]` has a root there, proved by
Bolzano–Weierstrass (`IsCompact.tendsto_subseq`) plus continuity — *not* via
Mathlib's `intermediate_value_Icc`. `exists_root_of_continuous` combines the two:
for continuous `f` with `f 0 ≤ 0 < f 1` it produces an actual root `x ∈ [0,1]`,
completing the 1-d (interval) case of Brouwer entirely on top of the 1-d Sperner
lemma. The remaining open item is the `n`-dimensional Brouwer derivation via
barycentric subdivision (recorded in `knowledge.md`); it is not in this file.

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

open Filter Topology Set in
/-- **The continuous limit step, stated independently of Sperner.**

If a continuous `f : ℝ → ℝ` admits, for every index `n`, a bracket
`[a n, b n] ⊆ [0,1]` of width `≤ 1/(n+1)` across which it changes sign
(`f (a n) · f (b n) ≤ 0`), then `f` has a root in `[0,1]`.

This is the analytic content of turning the discrete sign-change cells of
`exists_sign_change_bracket` into an exact root: pass to the limit `m → ∞`.
The proof uses Bolzano–Weierstrass (`IsCompact.tendsto_subseq` on the compact
`[0,1]`) to extract a convergent subsequence `a ∘ φ → x`; the widths vanishing
forces `b ∘ φ → x` too, and continuity carries the termwise sign condition
`f(a)·f(b) ≤ 0` to the limit `(f x)² ≤ 0`, whence `f x = 0`. It does **not**
invoke Mathlib's `intermediate_value_Icc`. -/
theorem ivt_of_shrinking_brackets (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hwidth : ∀ n, |a n - b n| ≤ 1 / ((n : ℝ) + 1))
    (hsign : ∀ n, f (a n) * f (b n) ≤ 0) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  -- Bolzano–Weierstrass on the compact interval `[0,1]`.
  obtain ⟨x, hx_mem, φ, hφ_mono, hφ_tend⟩ := isCompact_Icc.tendsto_subseq ha
  refine ⟨x, hx_mem, ?_⟩
  -- The bracket widths along the subsequence tend to `0`.
  have hbase : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hg0 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    hbase.comp hφ_mono.tendsto_atTop
  have hd0 : Tendsto (fun n => b (φ n) - a (φ n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by
      rw [Real.norm_eq_abs, abs_sub_comm]; exact hwidth (φ n)) hg0
  -- Hence `b ∘ φ → x` as well.
  have hb_tend : Tendsto (fun n => b (φ n)) atTop (𝓝 x) := by
    have heq : (fun n => b (φ n)) = fun n => a (φ n) + (b (φ n) - a (φ n)) := by
      funext n; ring
    rw [heq]
    simpa using hφ_tend.add hd0
  -- Continuity carries both subsequences into `f x`.
  have hfa : Tendsto (fun n => f (a (φ n))) atTop (𝓝 (f x)) :=
    (hf.tendsto x).comp hφ_tend
  have hfb : Tendsto (fun n => f (b (φ n))) atTop (𝓝 (f x)) :=
    (hf.tendsto x).comp hb_tend
  have hprod : Tendsto (fun n => f (a (φ n)) * f (b (φ n))) atTop (𝓝 (f x * f x)) :=
    hfa.mul hfb
  -- The termwise sign condition passes to the limit: `(f x)² ≤ 0`.
  have hle : f x * f x ≤ 0 := le_of_tendsto' hprod (fun n => hsign (φ n))
  have hsq : f x * f x = 0 := le_antisymm hle (mul_self_nonneg (f x))
  exact mul_self_eq_zero.mp hsq

open Set in
/-- **Continuous intermediate-value theorem, derived from the 1-d Sperner
lemma.** For continuous `f : ℝ → ℝ` with `f 0 ≤ 0 < f 1`, there is a root
`x ∈ [0,1]`.

The derivation is `discrete Sperner ⇒ sign-change brackets ⇒ limit`: for each
mesh `m = n+1`, `exists_sign_change_bracket` (a corollary of the 1-d Sperner
lemma `discrete_ivt_panchromatic_cell`) yields a width-`1/(n+1)` bracket across
a sign change; `ivt_of_shrinking_brackets` then passes to the limit. Mathlib's
own `intermediate_value_Icc` is deliberately **not** used. -/
theorem exists_root_of_continuous (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : f 0 ≤ 0) (h1 : 0 < f 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  have hbr : ∀ n : ℕ, ∃ i : Fin (n + 1),
      f (meshPt (n + 1) i.val) * f (meshPt (n + 1) (i.val + 1)) ≤ 0 :=
    fun n => exists_sign_change_bracket f n.succ_pos h0 h1
  choose i hi using hbr
  refine ivt_of_shrinking_brackets f hf
    (fun n => meshPt (n + 1) (i n).val)
    (fun n => meshPt (n + 1) ((i n).val + 1)) ?_ ?_ ?_
  · -- left endpoints lie in `[0,1]`
    intro n
    dsimp only
    rw [Set.mem_Icc]
    simp only [meshPt]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast (i n).isLt.le
  · -- bracket width is exactly `1/(n+1)`
    intro n
    dsimp only
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hab : meshPt (n + 1) (i n).val - meshPt (n + 1) ((i n).val + 1)
        = -(1 / ((n : ℝ) + 1)) := by
      simp only [meshPt]; push_cast; field_simp; ring
    have hval : |meshPt (n + 1) (i n).val - meshPt (n + 1) ((i n).val + 1)|
        = 1 / ((n : ℝ) + 1) := by
      rw [hab, abs_neg]; exact abs_of_pos (by positivity)
    exact le_of_eq hval
  · -- opposite signs across the bracket
    exact fun n => hi n

end SpernerSimplicialInstanceOQ04
