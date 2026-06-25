/-
  Mellin transform of the unit indicator — open question oq-01 (child oq-01-oq-01).

  The parent entry (`MellinPowerConvergenceOQ01`) computes the Mellin transform
  of the unit indicator `𝟙_{(0,1]}`, its sharp convergence strip `Re s > 0`, and
  the scaling law `mellin 𝟙_{(0,a]} s = a^s / s`. Its first open question asks to
  extend this to

    (1) the indicator of a *general interval* `𝟙_{[a,b]}` (here `𝟙_{(a,b]}`),
        giving `(b^s - a^s)/s`, and
    (2) the *power-weighted* indicator `t^c · 𝟙_{(0,1]}`, which shifts the
        convergence strip to `Re s > -c` and yields `1/(s + c)`.

  This file answers both, axiom-free and sorry-free, building on the parent's
  scaling law and Mathlib's Mellin API (`hasMellin_sub`, `hasMellin_cpow_Ioc`,
  `mellin_cpow_smul`, `MellinConvergent.cpow_smul`):

    * `hasMellin_indicator_interval` / `mellin_indicator_interval`
        — the general-interval transform `(b^s - a^s)/s` (Re s > 0), via the
          difference `𝟙_{(a,b]} = 𝟙_{(0,b]} - 𝟙_{(0,a]}`;
    * `mellin_indicator_interval_one` — at `s = 1` it returns the length `b - a`;
    * `hasMellin_powerWeighted_unit` / `mellin_powerWeighted_unit`
        — the power-weighted transform `1/(s + c)` on the shifted strip `Re s > -c`;
    * `mellinConvergent_powerWeighted_unit_iff`
        — the convergence strip is *exactly* `Re s > -c` (sharp, both directions);
    * `hasMellin_powerWeighted_interval`
        — the capstone combining both: `mellin (t^c · 𝟙_{(a,b]}) s
          = (b^{s+c} - a^{s+c})/(s + c)`.
-/

import Mathlib
import Proofs.MellinPowerConvergenceOQ01

open Complex MeasureTheory Set
open MellinPowerConvergenceOQ01

namespace MellinPowerConvergenceOQ01OQ01

/-! ## Part 1: the general interval `𝟙_{(a,b]}` gives `(b^s - a^s)/s` -/

/-- **General interval.** For `0 < a ≤ b` and `Re s > 0`, the Mellin transform of
the indicator of `(a, b]` exists and equals `(b^s - a^s)/s`. The proof writes
`𝟙_{(a,b]} = 𝟙_{(0,b]} - 𝟙_{(0,a]}` and subtracts two instances of the parent's
scaling law. -/
theorem hasMellin_indicator_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    HasMellin (Set.indicator (Set.Ioc a b) (fun _ => 1)) s (((b : ℂ) ^ s - (a : ℂ) ^ s) / s) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- `𝟙_{(a,b]}(t) = 𝟙_{(0,b]}(t) - 𝟙_{(0,a]}(t)` pointwise.
  have hfun : Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ))
      = fun t => Set.indicator (Set.Ioc 0 b) (fun _ => (1 : ℂ)) t
               - Set.indicator (Set.Ioc 0 a) (fun _ => (1 : ℂ)) t := by
    funext t
    by_cases htab : t ∈ Set.Ioc a b
    · have hat := htab.1
      have htb := htab.2
      rw [Set.indicator_of_mem htab,
          Set.indicator_of_mem (show t ∈ Set.Ioc 0 b from ⟨lt_trans ha hat, htb⟩),
          Set.indicator_of_notMem (show t ∉ Set.Ioc 0 a from fun h => absurd h.2 (not_le.mpr hat))]
      ring
    · rw [Set.indicator_of_notMem htab]
      by_cases ht0b : t ∈ Set.Ioc 0 b
      · have hta : t ∈ Set.Ioc 0 a := by
          refine ⟨ht0b.1, ?_⟩
          by_contra h
          exact htab ⟨lt_of_not_le h, ht0b.2⟩
        rw [Set.indicator_of_mem ht0b, Set.indicator_of_mem hta]; ring
      · have hta : t ∉ Set.Ioc 0 a := fun h => ht0b ⟨h.1, le_trans h.2 hab⟩
        rw [Set.indicator_of_notMem ht0b, Set.indicator_of_notMem hta]; ring
  rw [hfun, sub_div]
  have hMb := hasMellin_indicator_Ioc hb hs
  have hMa := hasMellin_indicator_Ioc ha hs
  have hsub := hasMellin_sub hMb.1 hMa.1
  rwa [hMb.2, hMa.2] at hsub

/-- The value form of the general-interval transform. -/
theorem mellin_indicator_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) :
    mellin (Set.indicator (Set.Ioc a b) (fun _ => 1)) s = ((b : ℂ) ^ s - (a : ℂ) ^ s) / s :=
  (hasMellin_indicator_interval ha hab hs).2

/-- At `s = 1` the general-interval transform returns the length of the interval:
`mellin 𝟙_{(a,b]} 1 = b - a`. -/
theorem mellin_indicator_interval_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    mellin (Set.indicator (Set.Ioc a b) (fun _ => 1)) 1 = (b : ℂ) - (a : ℂ) := by
  rw [mellin_indicator_interval ha hab (by rw [Complex.one_re]; norm_num)]
  rw [Complex.cpow_one, Complex.cpow_one, div_one]

/-! ## Part 2: the power-weighted indicator `t^c · 𝟙_{(0,1]}`, strip `Re s > -c` -/

/-- **Power-weighted unit indicator.** For real weight `c` and `Re s > -c`, the
Mellin transform of `t^c · 𝟙_{(0,1]}` exists and equals `1/(s + c)`. The strip
of the base case `Re s > 0` is shifted to `Re s > -c`. -/
theorem hasMellin_powerWeighted_unit (c : ℝ) {s : ℂ} (hs : -c < s.re) :
    HasMellin (Set.indicator (Set.Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (c : ℂ))) s (1 / (s + c)) := by
  apply hasMellin_cpow_Ioc (c : ℂ)
  rw [Complex.ofReal_re]
  linarith

/-- The value form of the power-weighted transform. -/
theorem mellin_powerWeighted_unit (c : ℝ) {s : ℂ} (hs : -c < s.re) :
    mellin (Set.indicator (Set.Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (c : ℂ))) s = 1 / (s + c) :=
  (hasMellin_powerWeighted_unit c hs).2

/-- **Sharp shifted strip.** The Mellin integral of the power-weighted unit
indicator converges *iff* `Re s > -c`. The boundary `Re s = -c` is exactly where
`∫_0^1 t^{s + c - 1} dt` diverges — the parent's `Re s > 0` strip translated by
`-c`. -/
theorem mellinConvergent_powerWeighted_unit_iff (c : ℝ) {s : ℂ} :
    MellinConvergent (Set.indicator (Set.Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (c : ℂ))) s ↔ -c < s.re := by
  have hfun : Set.indicator (Set.Ioc (0:ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (c : ℂ))
      = fun t : ℝ => (t : ℂ) ^ (c : ℂ) • unitIndicator t := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · simp [unitIndicator, Set.indicator_of_mem ht]
    · simp [unitIndicator, Set.indicator_of_notMem ht]
  rw [hfun, MellinConvergent.cpow_smul, mellinConvergent_unitIndicator_iff,
    Complex.add_re, Complex.ofReal_re]
  constructor <;> intro h <;> linarith

/-! ## Part 3: the power-weighted general interval (capstone) -/

/-- **Capstone.** Combining Parts 1 and 2: for `0 < a ≤ b` and `Re s > -c`, the
Mellin transform of `t^c · 𝟙_{(a,b]}` exists and equals
`(b^{s+c} - a^{s+c})/(s + c)`. The weight `t^c` shifts the spectral parameter
from `s` to `s + c`, applied to the general-interval law of Part 1. -/
theorem hasMellin_powerWeighted_interval (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : -c < s.re) :
    HasMellin (Set.indicator (Set.Ioc a b) (fun t => (t : ℂ) ^ (c : ℂ))) s
      (((b : ℂ) ^ (s + c) - (a : ℂ) ^ (s + c)) / (s + c)) := by
  have hsc : 0 < (s + (c : ℂ)).re := by rw [Complex.add_re, Complex.ofReal_re]; linarith
  have hbase := hasMellin_indicator_interval ha hab hsc
  -- `t^c · 𝟙_{(a,b]}(t) = t^c • 𝟙_{(a,b]}(t)`.
  have hfun : Set.indicator (Set.Ioc a b) (fun t => (t : ℂ) ^ (c : ℂ))
      = fun t : ℝ => (t : ℂ) ^ (c : ℂ) • Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ)) t := by
    funext t
    by_cases ht : t ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent.cpow_smul]; exact hbase.1
  · rw [mellin_cpow_smul]; exact hbase.2

end MellinPowerConvergenceOQ01OQ01
