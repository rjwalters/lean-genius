import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A CF-independent reduction for the upper bound `μ(e) ≤ 2`

`Proofs/ETranscendentalOQ03.lean` proves `μ(e) = 2` modulo a single axiom

```
axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) : ¬LiouvilleWith p (exp 1)
```

That axiom bundles two genuinely different ingredients:

1. **Filter / Diophantine bookkeeping.** Unfolding `LiouvilleWith p x` and turning
   "infinitely many good approximations" into a contradiction with a quadratic-type
   lower bound. This is pure real analysis on `LiouvilleWith` and is *not* specific
   to `e`.
2. **The continued-fraction input.** The actual statement that `e` is badly
   approximable: for every `ε > 0` there is `c > 0` with
   `|e - m/n| ≥ c / n^(2+ε)` for all `n ≥ 1, m ∈ ℤ`. This is the hard part, requiring
   Euler's regular continued fraction `e = [2; 1, 2, 1, 1, 4, …]`, which Mathlib does
   not yet have.

This file discharges ingredient (1) **once and for all**, for an arbitrary real `x`:

  `not_liouvilleWith_of_diophantine_bound`

reduces `¬ LiouvilleWith p x` (for `p > 2`) to the single self-contained Diophantine
hypothesis at the *fixed* exponent `(p + 2) / 2 ∈ (2, p)`. The remaining work to remove
the axiom in the main file is then *only* ingredient (2): supply that lower bound for
`x = e`. No `LiouvilleWith` manipulation is needed downstream.

The key elementary identity driving the proof is
`(p + 2) / 2 + (p - 2) / 2 = p`, i.e. writing `a := (p+2)/2` and `d := (p-2)/2` we have
`a + d = p` with `d > 0`, so `n^p = n^a · n^d` and `n^d → ∞`.

**Status.** Build-pending companion file (authored under a Docker/Aristotle blackout, so
not machine-checked here). It is intentionally *not* registered in `Proofs.lean` and the
main gallery file is untouched, so the gallery build is unaffected. Once a build host is
available, compile, then replace `e_not_liouvilleWith_gt_two` in
`ETranscendentalOQ03.lean` by an application of `not_liouvilleWith_of_diophantine_bound`
to the (still-axiomatized) continued-fraction lower bound for `e`.
-/

namespace ETranscendentalOQ03Reduction

open Filter

/-- **Reduction lemma (CF-independent).**

For `p > 2`, to show `¬ LiouvilleWith p x` it suffices to have a single quadratic-type
Diophantine lower bound at the fixed exponent `(p + 2) / 2`:

  `∀ n ≥ 1, ∀ m : ℤ, c / n ^ ((p + 2) / 2) ≤ |x - m / n|`

for some `c > 0`. Intuitively: if `x` cannot be approximated better than the exponent
`(p+2)/2 < p`, then no constant `C` can make `|x - m/n| < C / n^p` hold for infinitely
many `n`, because `n^(p - (p+2)/2) = n^((p-2)/2) → ∞`. -/
theorem not_liouvilleWith_of_diophantine_bound (x : ℝ) (p : ℝ) (hp : 2 < p)
    (c : ℝ) (hc : 0 < c)
    (hlb : ∀ n : ℕ, 1 ≤ n → ∀ m : ℤ,
      c / (n : ℝ) ^ ((p + 2) / 2) ≤ |x - (m : ℝ) / (n : ℝ)|) :
    ¬ LiouvilleWith p x := by
  rintro ⟨C, hC⟩
  -- Abbreviations: a = (p+2)/2 (approximation exponent), d = (p-2)/2 (the gain).
  set a : ℝ := (p + 2) / 2 with ha_def
  set d : ℝ := (p - 2) / 2 with hd_def
  have hd_pos : 0 < d := by rw [hd_def]; linarith
  have hadp : a + d = p := by rw [ha_def, hd_def]; ring
  -- `c * n^d → ∞`, hence eventually `C ≤ c * n^d`, and we may also assume `1 ≤ n`.
  have htend : Tendsto (fun n : ℕ => c * (n : ℝ) ^ d) atTop atTop := by
    refine Tendsto.const_mul_atTop hc ?_
    exact (Real.tendsto_rpow_atTop hd_pos).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ C ≤ c * (n : ℝ) ^ d := by
    filter_upwards [eventually_ge_atTop 1, htend.eventually_ge_atTop C] with n hn hCle
    exact ⟨hn, hCle⟩
  -- Pick an `n` that is simultaneously a "good approximation" index and large.
  obtain ⟨n, ⟨m, _hne, happrox⟩, hn1, hCle⟩ := (hC.and_eventually hev).exists
  have hn0 : 0 < n := hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hna_pos : (0 : ℝ) < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn_pos a
  have hnd_pos : (0 : ℝ) < (n : ℝ) ^ d := Real.rpow_pos_of_pos hn_pos d
  -- Chain the two bounds: `c / n^a ≤ |x - m/n| < C / n^p`.
  have hchain : c / (n : ℝ) ^ a < C / (n : ℝ) ^ p :=
    lt_of_le_of_lt (hlb n hn1 m) happrox
  -- Split `n^p = n^a * n^d` and cancel the common `n^a`.
  have hsplit : (n : ℝ) ^ p = (n : ℝ) ^ a * (n : ℝ) ^ d := by
    rw [← hadp, Real.rpow_add hn_pos]
  have hCsplit : C / (n : ℝ) ^ p = (C / (n : ℝ) ^ d) / (n : ℝ) ^ a := by
    rw [hsplit, div_div, mul_comm ((n : ℝ) ^ a) ((n : ℝ) ^ d)]
  rw [hCsplit] at hchain
  -- (Lean 4.26: `div_lt_div_right` was renamed to `div_lt_div_iff_of_pos_right`.)
  have hkey : c < C / (n : ℝ) ^ d := (div_lt_div_iff_of_pos_right hna_pos).mp hchain
  have hlt : c * (n : ℝ) ^ d < C := (lt_div_iff₀ hnd_pos).mp hkey
  exact absurd hCle (not_le.mpr hlt)

/-- **Specialization to `e`.**

If the (still open in Mathlib) continued-fraction lower bound for `e` is supplied at the
exponent `(p+2)/2`, then `e` is not Liouville with exponent `p > 2`. This is the precise
remaining obligation needed to discharge `e_not_liouvilleWith_gt_two`. -/
theorem e_not_liouvilleWith_gt_two_of_bound (p : ℝ) (hp : 2 < p)
    (c : ℝ) (hc : 0 < c)
    (hlb : ∀ n : ℕ, 1 ≤ n → ∀ m : ℤ,
      c / (n : ℝ) ^ ((p + 2) / 2) ≤ |Real.exp 1 - (m : ℝ) / (n : ℝ)|) :
    ¬ LiouvilleWith p (Real.exp 1) :=
  not_liouvilleWith_of_diophantine_bound (Real.exp 1) p hp c hc hlb

end ETranscendentalOQ03Reduction
