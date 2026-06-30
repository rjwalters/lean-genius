import Mathlib
import Proofs.MellinPowerConvergenceOQ01

/-
# General intervals and power weights for the Mellin transform

The parent entry `mellin-power-convergence-oq-01` proves the base pair
`mellin 𝟙_{(0,1]} s = 1/s`, its sharp convergence strip `Re s > 0`, and the
dilation law `mellin 𝟙_{(0,a]} s = a^s/s`. This grandchild closes the two
natural algebraic gaps left open, turning the single base pair into a working
calculus.

* **General half-open interval** (`hasMellin_indicator_Ioc_pair`): for
  `0 < a < b` and `Re s > 0`,
  `mellin 𝟙_{(a,b]} s = (b^s - a^s)/s`.
  Since `(a,b] = (0,b] \ (0,a]` we have the pointwise identity
  `𝟙_{(a,b]} = 𝟙_{(0,b]} - 𝟙_{(0,a]}`, so subtracting the two parent dilation
  results (`hasMellin_sub`) gives `b^s/s - a^s/s = (b^s - a^s)/s`. This is the
  elementary building block of every piecewise-constant Mellin transform
  (Perron-type summation, truncated Dirichlet integrals). At `s = 1` it returns
  the length `b - a`.

* **Power-weighted unit indicator** (`hasMellin_powerIndicator`,
  `mellinConvergent_powerIndicator_iff`): for real `c` and `Re s > -c`,
  `mellin (t^c · 𝟙_{(0,1]}) s = 1/(s + c)`, with convergence holding **iff**
  `Re s > -c`. Absorbing the monomial weight into the Mellin exponent,
  `t^{s-1} · t^c = t^{(s+c)-1}`, reduces the whole computation to the parent
  base case at the shifted argument `s + c`; the fundamental strip slides left
  by `c`. This is the prototype for how decay/growth weights move the
  convergence strip — the mechanism behind the analytic continuation of `Γ`.

Both results reuse Mathlib's Mellin API (`hasMellin_sub`,
`MellinConvergent.cpow_smul`, `mellin_cpow_smul`) together with the parent
entry, so they are genuinely new packagings rather than restatements of a
single Mathlib lemma. No axioms.
-/

open Complex MeasureTheory Set

namespace MellinPowerConvergenceOQ01OQ01

open MellinPowerConvergenceOQ01

/-! ## General half-open interval: `mellin 𝟙_{(a,b]} s = (b^s - a^s)/s` -/

/-- **Set-difference decomposition.** For `0 < a < b`, the indicator of the
half-open interval `(a,b]` is the difference of the two nested unit-anchored
indicators: `𝟙_{(a,b]} = 𝟙_{(0,b]} - 𝟙_{(0,a]}`. -/
theorem indicator_Ioc_sub {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ)))
      = fun t => Set.indicator (Set.Ioc (0 : ℝ) b) (fun _ => (1 : ℂ)) t
              - Set.indicator (Set.Ioc (0 : ℝ) a) (fun _ => (1 : ℂ)) t := by
  have hb : (0 : ℝ) < b := ha.trans hab
  funext t
  by_cases htb : t ∈ Set.Ioc (0 : ℝ) b
  · by_cases hta : t ∈ Set.Ioc (0 : ℝ) a
    · -- `t ∈ (0,a]`, hence not in `(a,b]`
      have hnab : t ∉ Set.Ioc a b := by
        simp only [Set.mem_Ioc] at hta ⊢
        rintro ⟨h, _⟩; linarith [hta.2]
      rw [Set.indicator_of_notMem hnab, Set.indicator_of_mem htb,
        Set.indicator_of_mem hta, sub_self]
    · -- `t ∈ (0,b]` but `t ∉ (0,a]`, hence `a < t ≤ b`, i.e. `t ∈ (a,b]`
      have hmem : t ∈ Set.Ioc a b := by
        simp only [Set.mem_Ioc] at htb hta ⊢
        refine ⟨?_, htb.2⟩
        by_contra h; push_neg at h
        exact hta ⟨htb.1, h⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem htb,
        Set.indicator_of_notMem hta, sub_zero]
  · -- `t ∉ (0,b]`, hence in neither `(a,b]` nor `(0,a]`
    have hna : t ∉ Set.Ioc (0 : ℝ) a := fun h => htb (by
      simp only [Set.mem_Ioc] at h ⊢; exact ⟨h.1, h.2.trans hab.le⟩)
    have hnab : t ∉ Set.Ioc a b := fun h => htb (by
      simp only [Set.mem_Ioc] at h ⊢; exact ⟨ha.trans h.1, h.2⟩)
    rw [Set.indicator_of_notMem hnab, Set.indicator_of_notMem htb,
      Set.indicator_of_notMem hna, sub_zero]

/-- **General interval transform.** For `0 < a < b` and `Re s > 0`, the Mellin
transform of `𝟙_{(a,b]}` exists and equals `(b^s - a^s)/s`. The half-open
interval `(a,b]` is `(0,b] \ (0,a]`, so the result is the difference of the two
parent dilation laws. -/
theorem hasMellin_indicator_Ioc_pair {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {s : ℂ} (hs : 0 < s.re) :
    HasMellin (Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ))) s
      (((b : ℂ) ^ s - (a : ℂ) ^ s) / s) := by
  have hb : (0 : ℝ) < b := ha.trans hab
  rw [indicator_Ioc_sub ha hab]
  have hcb := hasMellin_indicator_Ioc hb hs
  have hca := hasMellin_indicator_Ioc ha hs
  have hsub := hasMellin_sub hcb.1 hca.1
  rwa [mellin_indicator_Ioc hb hs, mellin_indicator_Ioc ha hs, ← sub_div] at hsub

/-- The value form of the general-interval transform. -/
theorem mellin_indicator_Ioc_pair {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ))) s
      = ((b : ℂ) ^ s - (a : ℂ) ^ s) / s :=
  (hasMellin_indicator_Ioc_pair ha hab hs).2

/-- **Length at `s = 1`.** Specialising to `s = 1` recovers the Lebesgue length
of the interval: `mellin 𝟙_{(a,b]} 1 = b - a`. -/
theorem mellin_indicator_Ioc_pair_one {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    mellin (Set.indicator (Set.Ioc a b) (fun _ => (1 : ℂ))) 1
      = (b : ℂ) - (a : ℂ) := by
  rw [mellin_indicator_Ioc_pair ha hab (by norm_num), Complex.cpow_one,
    Complex.cpow_one, div_one]

/-! ## Power-weighted unit indicator: `mellin (t^c · 𝟙_{(0,1]}) s = 1/(s+c)` -/

/-- The power-weighted unit indicator `t ↦ t^c · 𝟙_{(0,1]}(t)` valued in `ℂ`,
for a real exponent `c`. -/
noncomputable abbrev powerIndicator (c : ℝ) : ℝ → ℂ :=
  fun t => (t : ℂ) ^ (c : ℂ) • unitIndicator t

/-- **Power-weight transform.** For real `c` and `Re s > -c`, the Mellin
transform of `t^c · 𝟙_{(0,1]}` exists and equals `1/(s + c)`. Absorbing the
weight `t^c` into the exponent reduces the computation to the parent base case
at the shifted argument `s + c`. -/
theorem hasMellin_powerIndicator {c : ℝ} {s : ℂ} (hs : -c < s.re) :
    HasMellin (powerIndicator c) s (1 / (s + (c : ℂ))) := by
  have hsc : 0 < (s + (c : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  refine ⟨?_, ?_⟩
  · -- convergence via the `cpow_smul` shift
    exact MellinConvergent.cpow_smul.mpr (hasMellin_unitIndicator hsc).1
  · -- value: `mellin (t^c • 𝟙) s = mellin 𝟙 (s+c) = 1/(s+c)`
    rw [mellin_cpow_smul, mellin_unitIndicator hsc]

/-- The value form of the power-weight transform. -/
theorem mellin_powerIndicator {c : ℝ} {s : ℂ} (hs : -c < s.re) :
    mellin (powerIndicator c) s = 1 / (s + (c : ℂ)) :=
  (hasMellin_powerIndicator hs).2

/-- **Sharp shifted convergence strip.** The Mellin integral of
`t^c · 𝟙_{(0,1]}` converges **if and only if** `Re s > -c`: the parent strip
`Re s > 0` slides left by `c`. -/
theorem mellinConvergent_powerIndicator_iff {c : ℝ} {s : ℂ} :
    MellinConvergent (powerIndicator c) s ↔ -c < s.re := by
  rw [show (powerIndicator c)
        = (fun t : ℝ => (t : ℂ) ^ (c : ℂ) • unitIndicator t) from rfl,
    MellinConvergent.cpow_smul, mellinConvergent_unitIndicator_iff,
    Complex.add_re, Complex.ofReal_re]
  constructor <;> intro h <;> linarith

end MellinPowerConvergenceOQ01OQ01
