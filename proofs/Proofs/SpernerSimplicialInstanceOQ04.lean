/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: researcher-8, researcher-9
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
for a real-valued `f`, and it is the base from which the **continuous IVT** now
follows in this file (`continuous_ivt_of_bridge`) by letting `m → ∞`: extract a
convergent subsequence of the bracket left-endpoints via Bolzano–Weierstrass on
the compact `[0,1]`, push it through the continuity of `f`, and read off a root
from `f(x*)² ≤ 0`. The derivation goes *through the discrete Sperner bracket*
(`exists_sign_change_bracket`), not through Mathlib's `intermediate_value_Icc`.

The remaining `n`-dimensional Brouwer derivation via barycentric subdivision is
recorded as the open remainder in `knowledge.md` — it is not in this file.

No `sorry`, no `axiom`. Builds on the axiom-free discrete theorem.
-/

namespace SpernerSimplicialInstanceOQ04

open SpernerSimplicialInstanceOQ05Scarf1d
open Filter Topology

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

/-- **Continuous intermediate-value theorem, derived from the discrete Sperner
bracket** (interval case of Brouwer, part (b) of `oq-04`).

For any continuous `f : ℝ → ℝ` with `f 0 ≤ 0 ≤ f 1` there is a point
`x ∈ [0,1]` with `f x = 0`.

The proof is the genuine `m → ∞` limit of the discrete bridge, **not** a call to
Mathlib's `intermediate_value_Icc`:

1. For each mesh `m = n+1`, `exists_sign_change_bracket` yields a width-`1/m`
   cell `[aₙ, bₙ] ⊆ [0,1]` with `f(aₙ)·f(bₙ) ≤ 0`.
2. `aₙ ∈ [0,1]` (compact), so Bolzano–Weierstrass (`IsCompact.tendsto_subseq`)
   gives a subsequence `a_{φ k} → x*` with `x* ∈ [0,1]`.
3. `bₙ - aₙ = 1/(n+1) → 0`, hence `b_{φ k} → x*` as well.
4. Continuity of `f` passes both limits through:
   `f(a_{φ k})·f(b_{φ k}) → f(x*)²`. Each factor product is `≤ 0`, so the limit
   `f(x*)² ≤ 0`; with `f(x*)² ≥ 0` this forces `f(x*) = 0`. -/
theorem continuous_ivt_of_bridge (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : f 0 ≤ 0) (h1 : 0 ≤ f 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  -- Degenerate case `f 1 = 0`: the right endpoint is already a root.
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · exact ⟨1, Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩, h1'.symm⟩
  -- Main case `0 < f 1`: run the mesh-refinement limit of the discrete bridge.
  -- Package a bracket cell for every mesh `m = n+1`.
  have bracket : ∀ n : ℕ, ∃ q : ℝ × ℝ,
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1 ∧
        q.2 - q.1 = 1 / ((n : ℝ) + 1) ∧ f q.1 * f q.2 ≤ 0 := by
    intro n
    obtain ⟨i, hi⟩ := exists_sign_change_bracket f (Nat.succ_pos n) h0 h1'
    refine ⟨(meshPt (n + 1) i.val, meshPt (n + 1) (i.val + 1)), ?_, ?_, ?_, hi⟩
    · refine ⟨?_, ?_⟩
      · simp only [meshPt]; positivity
      · simp only [meshPt]
        rw [div_le_one (by exact_mod_cast Nat.succ_pos n)]
        exact_mod_cast i.isLt.le
    · refine ⟨?_, ?_⟩
      · simp only [meshPt]; positivity
      · simp only [meshPt]
        rw [div_le_one (by exact_mod_cast Nat.succ_pos n)]
        exact_mod_cast Nat.succ_le_of_lt i.isLt
    · simp only [meshPt]
      rw [div_sub_div_same]
      push_cast
      ring
  -- Extract the bracket sequences.
  choose q hq1 hq2 hdiff hprod using bracket
  -- Bolzano–Weierstrass on the compact `[0,1]` for the left endpoints.
  obtain ⟨x, hx, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hq1
  -- `1/(φ k + 1) → 0`, since `φ` is strictly monotone (hence `→ ∞`).
  have hzero : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  -- Right endpoints converge to the same limit `x`.
  have hconvb : Tendsto (fun k => (q (φ k)).2) atTop (𝓝 x) := by
    have hsum := hconv.add hzero
    rw [add_zero] at hsum
    refine hsum.congr (fun k => ?_)
    have hd := hdiff (φ k)
    simp only [Function.comp]
    linarith [hd]
  -- Push both limits through continuity of `f`.
  have hfa : Tendsto (fun k => f ((q (φ k)).1)) atTop (𝓝 (f x)) := by
    have := (hf.tendsto x).comp hconv
    simpa [Function.comp] using this
  have hfb : Tendsto (fun k => f ((q (φ k)).2)) atTop (𝓝 (f x)) := by
    have := (hf.tendsto x).comp hconvb
    simpa [Function.comp] using this
  -- The product of the (nonpositive) bracket values converges to `f x * f x`.
  have hle : f x * f x ≤ 0 := by
    refine le_of_tendsto (hfa.mul hfb) ?_
    filter_upwards with k using hprod (φ k)
  -- `f x * f x ≤ 0` and `≥ 0` force `f x = 0`.
  have hsq : f x * f x = 0 := le_antisymm hle (mul_self_nonneg _)
  exact ⟨x, hx, mul_self_eq_zero.mp hsq⟩

end SpernerSimplicialInstanceOQ04
