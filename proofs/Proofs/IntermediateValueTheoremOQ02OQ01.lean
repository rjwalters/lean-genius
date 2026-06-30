/-
Intermediate Value Theorem — convergence of bisection to an exact zero (OQ-02-OQ-01)

Open Question (parent `intermediate-value-theorem-oq-02`):
  *Formalize convergence of the bisection midpoints to an exact zero via completeness
  of ℝ (Cauchy sequences), recovering the full classical IVT from the approximate
  version.*

The parent entry `intermediate-value-theorem-oq-02` built the bisection algorithm and
proved its *approximate* content: for every ε > 0 it produces a point with |f(x)| < ε.
Here we close the loop and recover the **exact** classical IVT from that same algorithm.

The bisection endpoint sequences `Lₙ = (bisect f n (a,b)).1` and `Rₙ = (bisect f n (a,b)).2`
are monotone (one up, one down), order-bounded, and satisfy `Rₙ − Lₙ = (b−a)/2ⁿ → 0`.
By completeness of ℝ (here: monotone bounded convergence, `tendsto_atTop_ciSup`) both
converge to a common limit `c ∈ [a,b]`, which is also the limit of the midpoints.
Continuity carries the sign invariant `f(Lₙ) ≤ 0 ≤ f(Rₙ)` to the limit, forcing
`f(c) ≤ 0 ≤ f(c)`, i.e. `f(c) = 0`.

Main results:
* `bisect_tendsto_root` — the bisection midpoints converge to a point `c ∈ [a,b]` with
  `f c = 0` (the exact IVT, obtained constructively from the algorithm).
* `exact_ivt_zero` — the existence statement `∃ c ∈ [a,b], f c = 0`.
* `exact_ivt` — the **full classical IVT** for an arbitrary intermediate value `y`
  between `f a` and `f b`, recovered from the bisection construction.

This file imports and builds directly on the parent's verified bisection lemmas; it
adds the completeness/limit layer that the parent deliberately left open.
-/

import Mathlib
import Proofs.IntermediateValueTheoremOQ02

open Set Filter Topology

namespace ConstructiveIVT

/-- The left bisection endpoints form a monotone (non-decreasing) sequence. -/
theorem bisect_left_seq_mono {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    Monotone (fun n => (bisect f n (a, b)).1) := by
  apply monotone_nat_of_le_succ
  intro n
  have ho := bisect_ordered f n (a, b) hab
  show (bisect f n (a, b)).1 ≤ (bisectStep f (bisect f n (a, b))).1
  unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- The right bisection endpoints form an antitone (non-increasing) sequence. -/
theorem bisect_right_seq_anti {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    Antitone (fun n => (bisect f n (a, b)).2) := by
  apply antitone_nat_of_succ_le
  intro n
  have ho := bisect_ordered f n (a, b) hab
  show (bisectStep f (bisect f n (a, b))).2 ≤ (bisect f n (a, b)).2
  unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- **Bisection converges to an exact zero.**
For continuous `f` on `[a,b]` with `f a ≤ 0 ≤ f b`, the bisection midpoints converge to
a point `c ∈ [a,b]` with `f c = 0`.  This recovers the exact IVT from the parent's
approximate (ε-) version using completeness of ℝ. -/
theorem bisect_tendsto_root {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ c ∈ Icc a b,
      Tendsto (fun n => bisectMid f n (a, b)) atTop (𝓝 c) ∧ f c = 0 := by
  -- Endpoints lie in `[a,b]`.
  have hmemL : ∀ n, (bisect f n (a, b)).1 ∈ Icc a b := fun n => by
    have hc := bisect_contained f n a b hab.le
    have ho := bisect_ordered f n (a, b) hab.le
    exact ⟨hc.1, le_trans ho hc.2⟩
  have hmemR : ∀ n, (bisect f n (a, b)).2 ∈ Icc a b := fun n => by
    have hc := bisect_contained f n a b hab.le
    have ho := bisect_ordered f n (a, b) hab.le
    exact ⟨le_trans hc.1 ho, hc.2⟩
  -- Monotone bounded ⇒ the left sequence converges to its supremum `c`.
  have hLmono := bisect_left_seq_mono hab.le f
  have hbdd : BddAbove (Set.range (fun n => (bisect f n (a, b)).1)) :=
    ⟨b, by rintro x ⟨n, rfl⟩; exact (hmemL n).2⟩
  obtain ⟨c, hLc⟩ : ∃ c, Tendsto (fun n => (bisect f n (a, b)).1) atTop (𝓝 c) :=
    ⟨_, tendsto_atTop_ciSup hLmono hbdd⟩
  -- The interval width tends to `0`.
  have hpow : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 := h2.const_mul (b - a)
    rw [mul_zero] at h3
    exact h3.congr (fun n => by rw [div_pow, one_pow]; ring)
  have hwidth : Tendsto (fun n => (bisect f n (a, b)).2 - (bisect f n (a, b)).1)
      atTop (𝓝 0) :=
    hpow.congr (fun n => (bisect_width f n (a, b)).symm)
  -- Hence the right sequence converges to the same limit `c`.
  have hRc : Tendsto (fun n => (bisect f n (a, b)).2) atTop (𝓝 c) := by
    have h := hLc.add hwidth
    rw [add_zero] at h
    exact h.congr (fun n => by ring)
  -- The common limit lies in `[a,b]`.
  have hc_mem : c ∈ Icc a b :=
    ⟨ge_of_tendsto hLc (Eventually.of_forall fun n => (hmemL n).1),
     le_of_tendsto hLc (Eventually.of_forall fun n => (hmemL n).2)⟩
  -- The midpoints converge to `c` as well.
  have hMid : Tendsto (fun n => bisectMid f n (a, b)) atTop (𝓝 c) := by
    have h := (hLc.add hRc).div_const 2
    rw [show (c + c) / 2 = c by ring] at h
    exact h.congr (fun n => by simp only [bisectMid])
  refine ⟨c, hc_mem, hMid, ?_⟩
  -- Continuity transports the sign invariant to the limit.
  have hcontL : Tendsto (fun n => f ((bisect f n (a, b)).1)) atTop (𝓝 (f c)) :=
    (hf c hc_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hLc, Eventually.of_forall hmemL⟩)
  have hcontR : Tendsto (fun n => f ((bisect f n (a, b)).2)) atTop (𝓝 (f c)) :=
    (hf c hc_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hRc, Eventually.of_forall hmemR⟩)
  have hle : f c ≤ 0 :=
    le_of_tendsto hcontL
      (Eventually.of_forall fun n => (bisect_sign f n (a, b) hfa hfb).1)
  have hge : 0 ≤ f c :=
    ge_of_tendsto hcontR
      (Eventually.of_forall fun n => (bisect_sign f n (a, b) hfa hfb).2)
  exact le_antisymm hle hge

/-- **Exact IVT (zero version).** A continuous `f` on `[a,b]` with `f a ≤ 0 ≤ f b` has an
exact zero in `[a,b]` — recovered from the bisection algorithm. -/
theorem exact_ivt_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ c ∈ Icc a b, f c = 0 := by
  obtain ⟨c, hc, _, hfc⟩ := bisect_tendsto_root hab hf hfa hfb
  exact ⟨c, hc, hfc⟩

/-- **Full classical Intermediate Value Theorem.** For continuous `f` on `[a,b]` and any
value `y` between `f a` and `f b`, there is `c ∈ [a,b]` with `f c = y`.  This is recovered
from the bisection construction by applying the zero version to `g = f − y`. -/
theorem exact_ivt {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {y : ℝ} (hfa : f a ≤ y) (hfb : y ≤ f b) :
    ∃ c ∈ Icc a b, f c = y := by
  have hg : ContinuousOn (fun x => f x - y) (Icc a b) := hf.sub continuousOn_const
  obtain ⟨c, hc, hgc⟩ := exact_ivt_zero hab hg (by simpa using hfa) (by simpa using hfb)
  exact ⟨c, hc, by linarith [hgc]⟩

end ConstructiveIVT
