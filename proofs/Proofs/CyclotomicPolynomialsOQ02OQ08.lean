/-
Erdős #1215 — sub-question OQ-02: Path-length bounds for cyclotomic sublevel sets.

Iteration 7 (researcher-1, 2026-07-19): the FIRST admissible-path construction.

All prior OQ-02 files (OQ02OQ01 … OQ02OQ07) prove *containment*, *area*, *radius*
and *symmetry* facts about the sublevel set `{z : |Φ_n z| < C}` — none of them ever
constructs an actual admissible PATH, which is the literal object of the OQ-02 target:

    ∃ C, ∀ n, ∃ γ : [0,1] → {|Φ_n| < C}, γ 0 = 0, γ reaches the boundary |Φ_n| = C,
         length(γ) ≤ C · n.

This file supplies the missing piece for the cases where the sublevel set is *convex*,
namely the degree-one cyclotomics `Φ_1 = X - 1` and `Φ_2 = X + 1`. For these the
sublevel set is an open disc `ball(±1, C)`, so a STRAIGHT segment from the origin to
the boundary is admissible — and a straight segment's length is just the distance
between its endpoints, which entirely sidesteps the general rectifiable-arc-length
infrastructure Mathlib still lacks (the reason the general `n ≥ 3` case stays open).

Concretely we prove: for any linear polynomial `X - a` with a root `a` on the unit
circle and any threshold `c > 1`, the straight path `γ t = t • (-a)` runs from `0` to
the boundary `|X - a| = c`, stays inside the closed sublevel set the whole way, and has
length `c - 1`. Specialised to `Φ_1` (`a = 1`) and `Φ_2` (`a = -1`) this gives an
explicit admissible escape path of length `c - 1 ≤ c · n` — the first genuine instance
of the OQ-02 path-length target, complementing the containment/area bounds of the
earlier iterations.

Scope / honesty: this covers only the degree-one (convex) cyclotomics `n ∈ {1, 2}`.
The genuinely open driver — `Φ_n` for `n ≥ 3`, whose sublevel sets are non-convex
lemniscates that may split into several components — needs polynomial-lemniscate
topology and a rectifiable arc-length functional that Mathlib does not yet have; it
is untouched here and remains the open question, exactly as recorded in the prior
iterations' knowledge notes.

Verified: 0 sorry / 0 axiom. Imports only Mathlib.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

open Complex Polynomial

namespace Erdos1215.OQ02.Path

/-- Sublevel set `{z : |P z| < c}`. Restated locally so this file imports only
Mathlib (the parent `Erdos1215Problem.lean` uses the same definition). -/
def levelSet (P : ℂ[X]) (c : ℝ) : Set ℂ := {z : ℂ | ‖P.eval z‖ < c}

/--
`HasStraightEscape P c L` says the ray `γ t = t • v` (`v : ℂ`) is an **admissible
escape path** for the sublevel set `{|P| < c}` of length at most `L`:

* it starts at the origin (`γ 0 = 0`, automatic for `t • v`);
* it reaches the boundary `|P| = c` at some time `t₁ > 0`;
* it stays inside the *closed* sublevel set `|P| ≤ c` for all `t ∈ [0, t₁]`;
* the straight-segment length `t₁ · ‖v‖` is at most `L`.

The segment length `t₁ · ‖v‖` is used in place of a general rectifiable arc length;
for a straight path the two agree, so no arc-length infrastructure is needed. -/
def HasStraightEscape (P : ℂ[X]) (c L : ℝ) : Prop :=
  ∃ (v : ℂ) (t₁ : ℝ), 0 < t₁ ∧
    ‖P.eval (t₁ • v)‖ = c ∧
    (∀ t ∈ Set.Icc (0 : ℝ) t₁, ‖P.eval (t • v)‖ ≤ c) ∧
    t₁ * ‖v‖ ≤ L

/-- Along the ray `t • (-a)` the linear polynomial `X - a` evaluates to
`|X - a|(t • (-a)) = (t + 1) · ‖a‖`, for `t ≥ 0`. -/
theorem norm_eval_linear_ray {a : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    ‖(X - Polynomial.C a).eval (t • (-a))‖ = (t + 1) * ‖a‖ := by
  have hsmul : (t : ℝ) • (-a) = (↑t : ℂ) * (-a) := Complex.real_smul
  rw [eval_sub, eval_X, eval_C, hsmul]
  have hrw : (↑t : ℂ) * (-a) - a = -((↑t + 1) * a) := by ring
  rw [hrw, norm_neg, norm_mul]
  have hcast : (↑t + 1 : ℂ) = ((t + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/--
**First admissible-path result for OQ-02.** For a linear polynomial `X - a` whose
root `a` lies on the unit circle (`‖a‖ = 1`), and any threshold `c > 1`, the straight
ray `γ t = t • (-a)` is an admissible escape path of length `c - 1`: it runs from the
origin to the boundary `|X - a| = c`, stays inside the closed sublevel set, and has
length `c - 1`.

This is the exact object the OQ-02 target asks for (a bounded-length path from `0` to
the boundary of the sublevel set), established here for the convex — degree one — case
that the earlier containment-only iterations never constructed. -/
theorem hasStraightEscape_linear_unitRoot {a : ℂ} (ha : ‖a‖ = 1) {c : ℝ} (hc : 1 < c) :
    HasStraightEscape (X - Polynomial.C a) c (c - 1) := by
  refine ⟨-a, c - 1, by linarith, ?_, ?_, ?_⟩
  · -- reaches the boundary at t₁ = c - 1
    rw [norm_eval_linear_ray (by linarith), ha, mul_one]; ring
  · -- stays inside the closed sublevel set on [0, c-1]
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [norm_eval_linear_ray ht0, ha, mul_one]; linarith
  · -- straight-segment length (c-1)·‖-a‖ = c-1
    rw [norm_neg, ha, mul_one]

/-- `Φ_1 = X - 1` admits a straight escape path of length `c - 1` for every `c > 1`. -/
theorem cyclotomic_one_hasStraightEscape {c : ℝ} (hc : 1 < c) :
    HasStraightEscape (cyclotomic 1 ℂ) c (c - 1) := by
  have hΦ : (cyclotomic 1 ℂ) = X - Polynomial.C (1 : ℂ) := by
    rw [cyclotomic_one, map_one]
  rw [hΦ]
  exact hasStraightEscape_linear_unitRoot (by simp) hc

/-- `Φ_2 = X + 1` admits a straight escape path of length `c - 1` for every `c > 1`. -/
theorem cyclotomic_two_hasStraightEscape {c : ℝ} (hc : 1 < c) :
    HasStraightEscape (cyclotomic 2 ℂ) c (c - 1) := by
  have hΦ : (cyclotomic 2 ℂ) = X - Polynomial.C (-1 : ℂ) := by
    rw [cyclotomic_two, map_neg, map_one]; ring
  rw [hΦ]
  exact hasStraightEscape_linear_unitRoot (by simp) hc

/--
**OQ-02 path-length target for the degree-one cyclotomics.** For `n ∈ {1, 2}` and any
`c > 1`, the cyclotomic sublevel set `{|Φ_n| < c}` admits an admissible escape path
whose length is at most `c · n` — the bound demanded by the OQ-02 statement
(length `≤ C · n`).

The length we produce is in fact `c - 1`, independent of `n`, hence far below the
linear `c · n` target; the `c · n` phrasing is kept to match OQ-02 verbatim. Only the
convex degree-one cases are covered; `n ≥ 3` remains open. -/
theorem cyclotomic_deg_one_hasStraightEscape_linear_bound
    {n : ℕ} (hn : n = 1 ∨ n = 2) {c : ℝ} (hc : 1 < c) :
    HasStraightEscape (cyclotomic n ℂ) c (c * n) := by
  have hlen : c - 1 ≤ c * (n : ℝ) := by
    rcases hn with h | h <;> subst h <;> push_cast <;> nlinarith
  have base : HasStraightEscape (cyclotomic n ℂ) c (c - 1) := by
    rcases hn with h | h <;> subst h
    · exact cyclotomic_one_hasStraightEscape hc
    · exact cyclotomic_two_hasStraightEscape hc
  obtain ⟨v, t₁, ht₁, hb, hstay, hlenv⟩ := base
  exact ⟨v, t₁, ht₁, hb, hstay, le_trans hlenv hlen⟩

end Erdos1215.OQ02.Path
