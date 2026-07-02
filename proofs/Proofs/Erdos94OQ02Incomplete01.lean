/-
  Reduction Lemmas for the Asymptotic Constant of Distance Multiplicities
  (Erdős Problem #94, OQ-02 — the analytic core, self-contained and axiom-free)

  Parent entry `erdos-94-oq-02` formalizes the open question: for convex n-gons
  the squared-multiplicity sum satisfies ∑ f(u)² ~ c·n³, and the regular n-gon
  analysis suggests c = 1/2. That formalization axiomatizes S and the existence
  of the limit, and leaves TWO theorems as `sorry`:

    * `optimal_bound_from_conjecture`  — from c = 1/2 and Erdős–Fishburn
      extremality, derive S(P) ≤ (1/2 + ε)·n³ for all large convex P;
    * `constant_ge_half`               — from the regular n-gon lower envelope,
      derive c ≥ 1/2.

  Neither of these `sorry`s is the *open* content of the problem: the genuinely
  open statements are the value c = 1/2 and the Erdős–Fishburn extremality
  conjecture, which the parent (correctly) carries as hypotheses. What the two
  `sorry`s actually require is a pair of routine — but real — limit arguments:

    (A) an upper-tail bound: a convergent normalized sequence a(n)/n³ → c is
        eventually below (c + ε)·n³;
    (B) a lower-bound comparison: a normalized sequence dominating the envelope
        n³/2 − n² has limit ≥ 1/2.

  This file isolates and PROVES that analytic core in a completely self-contained,
  axiom-free way (abstracted over an arbitrary real sequence, so no dependence on
  S, on `Classical.choose`, or on the parent's existence axioms). The results are
  exactly the reductions that discharge the two parent `sorry`s once the open
  conjectures are assumed, cleanly separating the "hard analysis" (done here) from
  the "hard geometry" (the actual open conjectures).

  References:
  - Fishburn (1995): O(n³) bound for convex polygons
  - Lefmann–Theile (1995): O(n³) under no-three-collinear
  - https://erdosproblems.com/94

  Tags: geometry, convex, distances, asymptotic-constant, limits, analysis
-/

import Mathlib

open Filter Topology

namespace Erdos94OQ02Incomplete01

/-!
## Part I: Upper-tail extraction from convergence

If a real sequence converges to `c`, then for every `ε > 0` it is eventually
strictly below `c + ε`. This is the qualitative half of "eventually within ε".
-/

/-- Upper-tail extraction: if `g n → c`, then for every `ε > 0`, eventually
    `g n < c + ε`. -/
theorem eventually_lt_of_tendsto {g : ℕ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, g n < c + ε := by
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N, hN⟩ := hg ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  have h := hN n hn
  rw [Real.dist_eq, abs_lt] at h
  linarith [h.2]

/-!
## Part II: From normalized convergence to an absolute upper bound

The content underlying the parent's `optimal_bound_from_conjecture`: converting a
statement about `a n / n³` into a statement about `a n` itself, by clearing the
positive denominator `n³` for `n ≥ 1`.
-/

/-- Absolute upper bound: if the normalized sequence `a n / n³` converges to `c`,
    then for every `ε > 0`, eventually `a n ≤ (c + ε)·n³`. -/
theorem absolute_upper_bound {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n => a n / (n : ℝ) ^ 3) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, a n ≤ (c + ε) * (n : ℝ) ^ 3 := by
  filter_upwards [eventually_lt_of_tendsto h hε, eventually_ge_atTop 1] with n hlt hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [div_lt_iff₀ hn3] at hlt
  linarith

/-- Specialization of `absolute_upper_bound` to the conjectured constant `c = 1/2`:
    if `a n / n³ → 1/2`, then for every `ε > 0`, eventually `a n ≤ (1/2 + ε)·n³`.
    This is precisely the analytic step behind the parent's
    `optimal_bound_from_conjecture` (with `a = S_regular`). -/
theorem half_upper_bound {a : ℕ → ℝ}
    (h : Tendsto (fun n => a n / (n : ℝ) ^ 3) atTop (𝓝 (1 / 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, a n ≤ (1 / 2 + ε) * (n : ℝ) ^ 3 :=
  absolute_upper_bound h hε

/-- Universal-bound reduction: combining the absolute upper bound with an
    (abstract) extremality hypothesis. If `a n / n³ → c` and some quantity `x`
    never exceeds `a n` (extremality: `S P ≤ S_regular n`), then eventually
    `x ≤ (c + ε)·n³`. This packages the shape of the parent's universal bound. -/
theorem universal_bound_reduction {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n => a n / (n : ℝ) ^ 3) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, x ≤ a n → x ≤ (c + ε) * (n : ℝ) ^ 3 := by
  filter_upwards [absolute_upper_bound h hε] with n hn x hx
  linarith

/-!
## Part III: The lower envelope and the lower bound `c ≥ 1/2`

The content underlying the parent's `constant_ge_half`: the regular n-gon supplies
the lower envelope `a n ≥ n³/2 − n²`, whose normalization is `1/2 − 1/n → 1/2`.
A limit comparison then forces the constant to be at least `1/2`.
-/

/-- The lower envelope `1/2 − 1/n` tends to `1/2`. -/
theorem envelope_tendsto :
    Tendsto (fun n : ℕ => 1 / 2 - 1 / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h

/-- Lower-bound reduction: if `a n / n³ → c` and eventually `a n ≥ n³/2 − n²`
    (the regular n-gon envelope), then `c ≥ 1/2`. This is the analytic step behind
    the parent's `constant_ge_half`. -/
theorem constant_ge_half_reduction {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n => a n / (n : ℝ) ^ 3) atTop (𝓝 c))
    (hlb : ∀ᶠ n in atTop, a n ≥ (n : ℝ) ^ 3 / 2 - (n : ℝ) ^ 2) :
    c ≥ 1 / 2 := by
  have key : (fun n : ℕ => 1 / 2 - 1 / (n : ℝ)) ≤ᶠ[atTop]
      (fun n => a n / (n : ℝ) ^ 3) := by
    filter_upwards [hlb, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hne : (n : ℝ) ≠ 0 := hn0.ne'
    have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    rw [le_div_iff₀ hn3]
    have expand : (1 / 2 - 1 / (n : ℝ)) * (n : ℝ) ^ 3
        = (n : ℝ) ^ 3 / 2 - (n : ℝ) ^ 2 := by
      field_simp
    rw [expand]
    exact hn
  have hle := le_of_tendsto_of_tendsto envelope_tendsto h key
  linarith

/-- Combined reduction (both directions at once): if the normalized regular n-gon
    sum converges to `c` and satisfies the envelope lower bound, then
    `1/2 ≤ c`, and moreover `c = 1/2` iff the upper direction `c ≤ 1/2` holds.
    This states cleanly what remains open: only the value question `c ≤ 1/2`. -/
theorem constant_eq_half_iff {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n => a n / (n : ℝ) ^ 3) atTop (𝓝 c))
    (hlb : ∀ᶠ n in atTop, a n ≥ (n : ℝ) ^ 3 / 2 - (n : ℝ) ^ 2) :
    c = 1 / 2 ↔ c ≤ 1 / 2 := by
  have hge : c ≥ 1 / 2 := constant_ge_half_reduction h hlb
  constructor
  · intro hc; linarith
  · intro hc; linarith

#check @eventually_lt_of_tendsto
#check @absolute_upper_bound
#check @half_upper_bound
#check @universal_bound_reduction
#check @envelope_tendsto
#check @constant_ge_half_reduction
#check @constant_eq_half_iff

end Erdos94OQ02Incomplete01
