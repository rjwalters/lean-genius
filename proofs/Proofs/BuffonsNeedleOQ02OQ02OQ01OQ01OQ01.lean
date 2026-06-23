import Mathlib

/-
# The Asymptotic αₙ ~ √(2/(πn)) for the Buffon Crossing Factor
# (buffons-needle-oq-02-oq-02-oq-01-oq-01-oq-01)

## The Open Question

The parent entry `buffons-needle-oq-02-oq-02-oq-01-oq-01` solves the two-step
recurrence `α_{n+2} = (n/(n+1))αₙ` for the Buffon crossing factor in closed form:
the even and odd subsequences are the base values `2/π`, `1/2` times finite
telescoping products of the rational factors `(2j+2)/(2j+3)` and `(2j+3)/(2j+4)`.
It leaves open the precise *asymptotic* of `αₙ`: establish `αₙ ~ √(2/(πn))`
**directly from the telescoping products**, rather than via Stirling's formula for
`Γ(n/2)/(√π Γ((n+1)/2))`, and find the sharp two-sided bounds obtainable purely
from the factor product.

## Result

Write `Eₘ = ∏_{j<m} (2j+2)/(2j+3)` (the even product) and
`Oₘ = ∏_{j<m} (2j+3)/(2j+4)` (the odd product), so that
`α_{2m+2} = (2/π)·Eₘ` and `α_{2m+3} = (1/2)·Oₘ`.

1. **Telescoping identity** (`evenProd_mul_oddProd`): `Eₘ · Oₘ = 1/(m+1)`.
   Factor-wise `(2j+2)/(2j+3) · (2j+3)/(2j+4) = (j+1)/(j+2)`, which telescopes.

2. **Wallis bridge** (`wallis_eq`): `W m = (2m+1)·Eₘ²`, where `W` is Mathlib's
   Wallis partial product `∏_{i<m}(2i+2)/(2i+1)·(2i+2)/(2i+3)`. This is the exact
   link from the telescoping product to `π`: since `W m → π/2`, we get
   `(2m+1)·Eₘ² → π/2` with **no appeal to Stirling**.

3. **Sharp two-sided bounds** (`le_evenProd_sq`, `evenProd_sq_le`):
   `π/(4(m+1)) ≤ Eₘ² ≤ π/(4m+2)`, straight from Mathlib's integral Wallis bounds
   `le_W`/`W_le`; both sides squeeze to `π/(4m)`. The purely *rational* upper bound
   `Eₘ² < 1/(m+1)` (`evenProd_sq_lt`) drops out of the telescoping identity alone
   (`Eₘ < Oₘ` and `Eₘ·Oₘ = 1/(m+1)`).

4. **The asymptotic** (`tendsto_even`, `tendsto_odd`, `tendsto_crossingFactor_sqrt`):
   `αₙ · √n → √(2/π)`, i.e. `αₙ ~ √(2/(πn))`, proved separately for the even and
   odd subsequences from the Wallis bridge and then merged over all `n`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace BuffonCrossingAsymptotic

open Real Filter
open scoped Topology BigOperators

/-- The n-dimensional crossing factor `αₙ = E_{Sⁿ⁻¹}[|u₁|]`, by the recurrence
    `α_{n+2} = (n/(n+1)) · αₙ` with `α₂ = 2/π`, `α₃ = 1/2`. Re-declared verbatim
    from the parent entry. -/
noncomputable def crossingFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2 / π
  | 3 => 1 / 2
  | (n + 4) => ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2)

@[simp] lemma crossingFactor_two : crossingFactor 2 = 2 / π := rfl

@[simp] lemma crossingFactor_three : crossingFactor 3 = 1 / 2 := rfl

lemma crossingFactor_succ_succ (n : ℕ) :
    crossingFactor (n + 4) = ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2) := rfl

/-- The even-subsequence telescoping product `Eₘ = ∏_{j<m} (2j+2)/(2j+3)`. -/
noncomputable def evenProd (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)

/-- The odd-subsequence telescoping product `Oₘ = ∏_{j<m} (2j+3)/(2j+4)`. -/
noncomputable def oddProd (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 4)

lemma evenProd_succ (m : ℕ) :
    evenProd (m + 1) = evenProd m * ((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 3)) :=
  Finset.prod_range_succ _ _

lemma oddProd_succ (m : ℕ) :
    oddProd (m + 1) = oddProd m * ((2 * (m : ℝ) + 3) / (2 * (m : ℝ) + 4)) :=
  Finset.prod_range_succ _ _

lemma evenProd_pos (m : ℕ) : 0 < evenProd m := by
  apply Finset.prod_pos; intro j _; positivity

lemma oddProd_pos (m : ℕ) : 0 < oddProd m := by
  apply Finset.prod_pos; intro j _; positivity

-- ============================================================
-- PART 1: Closed forms relating crossingFactor to the products
-- ============================================================

/-- **Even-dimension closed form**: `α_{2m+2} = (2/π) · Eₘ`. -/
theorem crossingFactor_even (m : ℕ) :
    crossingFactor (2 * m + 2) = (2 / π) * evenProd m := by
  induction m with
  | zero => simp [evenProd]
  | succ k ih =>
      have hidx : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
      rw [hidx, crossingFactor_succ_succ (2 * k), ih, evenProd_succ]
      push_cast; ring

/-- **Odd-dimension closed form**: `α_{2m+3} = (1/2) · Oₘ`. -/
theorem crossingFactor_odd (m : ℕ) :
    crossingFactor (2 * m + 3) = (1 / 2) * oddProd m := by
  induction m with
  | zero => simp [oddProd]
  | succ k ih =>
      have hidx : 2 * (k + 1) + 3 = (2 * k + 1) + 4 := by ring
      have hidx2 : (2 * k + 1) + 2 = 2 * k + 3 := by ring
      rw [hidx, crossingFactor_succ_succ (2 * k + 1), hidx2, ih, oddProd_succ]
      push_cast; ring

lemma crossingFactor_even_pos (m : ℕ) : 0 < crossingFactor (2 * m + 2) := by
  rw [crossingFactor_even]; exact mul_pos (by positivity) (evenProd_pos m)

lemma crossingFactor_odd_pos (m : ℕ) : 0 < crossingFactor (2 * m + 3) := by
  rw [crossingFactor_odd]; exact mul_pos (by norm_num) (oddProd_pos m)

-- ============================================================
-- PART 2: The telescoping identity and the Wallis bridge
-- ============================================================

/-- **Telescoping identity**: `Eₘ · Oₘ = 1/(m+1)`. Each paired factor collapses
    to `(2j+2)/(2j+4) = (j+1)/(j+2)`, and the resulting product telescopes. -/
theorem evenProd_mul_oddProd (m : ℕ) : evenProd m * oddProd m = 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => simp [evenProd, oddProd]
  | succ k ih =>
      rw [evenProd_succ, oddProd_succ]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hk2 : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
      have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
      have h4 : (2 * (k : ℝ) + 4) ≠ 0 := by positivity
      rw [mul_mul_mul_comm, ih]
      push_cast
      field_simp
      ring

/-- **Wallis bridge**: `W m = (2m+1) · Eₘ²`, where `W` is Mathlib's Wallis partial
    product. This is the exact link from the telescoping product to `π`. -/
theorem wallis_eq (m : ℕ) : Real.Wallis.W m = (2 * (m : ℝ) + 1) * evenProd m ^ 2 := by
  induction m with
  | zero => simp [Real.Wallis.W, evenProd]
  | succ k ih =>
      rw [Real.Wallis.W_succ, ih, evenProd_succ]
      have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- `Eₘ² = W m / (2m+1)`. -/
theorem evenProd_sq_eq (m : ℕ) :
    evenProd m ^ 2 = Real.Wallis.W m / (2 * (m : ℝ) + 1) := by
  have h1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff h1, wallis_eq]; ring

-- ============================================================
-- PART 3: Sharp two-sided bounds
-- ============================================================

/-- Each even factor is strictly below the corresponding odd factor:
    `(2j+2)/(2j+3) < (2j+3)/(2j+4)` (equivalently `(2j+2)(2j+4) < (2j+3)²`). -/
theorem evenProd_lt_oddProd (m : ℕ) (hm : 1 ≤ m) : evenProd m < oddProd m := by
  apply Finset.prod_lt_prod_of_nonempty
  · intro j _; positivity
  · intro j _
    have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    have h4 : (2 * (j : ℝ) + 4) ≠ 0 := by positivity
    have hsub : (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 4) - (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)
        = 1 / ((2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 3)) := by
      field_simp; ring
    have hpos : (0 : ℝ) < 1 / ((2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 3)) := by positivity
    linarith [hsub, hpos]
  · exact Finset.nonempty_range_iff.mpr (by omega)

/-- **Rational upper bound** from the telescoping identity alone:
    `Eₘ² < 1/(m+1)` for `m ≥ 1`. -/
theorem evenProd_sq_lt (m : ℕ) (hm : 1 ≤ m) : evenProd m ^ 2 < 1 / ((m : ℝ) + 1) := by
  have hlt := evenProd_lt_oddProd m hm
  have hpos := evenProd_pos m
  have hprod := evenProd_mul_oddProd m
  nlinarith [mul_lt_mul_of_pos_left hlt hpos, hprod]

/-- **Sharp upper bound** from Mathlib's integral Wallis bound `W m ≤ π/2`:
    `Eₘ² ≤ π/(4m+2)`. -/
theorem evenProd_sq_le (m : ℕ) : evenProd m ^ 2 ≤ π / (4 * (m : ℝ) + 2) := by
  rw [evenProd_sq_eq]
  have hW := Real.Wallis.W_le m
  have heq : π / (4 * (m : ℝ) + 2) = (π / 2) / (2 * (m : ℝ) + 1) := by
    rw [div_div]; congr 1; ring
  rw [heq]
  gcongr

/-- **Sharp lower bound** from Mathlib's integral Wallis bound `le_W`:
    `π/(4(m+1)) ≤ Eₘ²`. -/
theorem le_evenProd_sq (m : ℕ) : π / (4 * (m : ℝ) + 4) ≤ evenProd m ^ 2 := by
  rw [evenProd_sq_eq]
  have hW := Real.Wallis.le_W m
  have h1 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  calc π / (4 * (m : ℝ) + 4)
      = ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * (π / 2)) / (2 * (m : ℝ) + 1) := by
        field_simp; ring
    _ ≤ Real.Wallis.W m / (2 * (m : ℝ) + 1) := by gcongr

/-- `Oₘ² = (2m+1) / ((m+1)² · W m)`. -/
theorem oddProd_sq_eq (m : ℕ) :
    oddProd m ^ 2 = (2 * (m : ℝ) + 1) / (((m : ℝ) + 1) ^ 2 * Real.Wallis.W m) := by
  have hEO := evenProd_mul_oddProd m
  have hWeq := wallis_eq m
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hden : ((m : ℝ) + 1) ^ 2 * Real.Wallis.W m ≠ 0 :=
    mul_ne_zero (by positivity) (ne_of_gt (Real.Wallis.W_pos m))
  rw [eq_div_iff hden]
  have key : evenProd m ^ 2 * oddProd m ^ 2 = 1 / ((m : ℝ) + 1) ^ 2 := by
    rw [← mul_pow, hEO, div_pow, one_pow]
  rw [hWeq]
  have hexpand : oddProd m ^ 2 * (((m : ℝ) + 1) ^ 2 * ((2 * (m : ℝ) + 1) * evenProd m ^ 2))
      = (2 * (m : ℝ) + 1) * (((m : ℝ) + 1) ^ 2 * (evenProd m ^ 2 * oddProd m ^ 2)) := by ring
  rw [hexpand, key, mul_one_div, div_self (by positivity), mul_one]

-- ============================================================
-- PART 4: The asymptotic αₙ ~ √(2/(πn))
-- ============================================================

private lemma tendsto_natCast_add_const_atTop (c : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) + c) atTop atTop :=
  tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop

/-- **Even-subsequence asymptotic**: `α_{2m+2} · √(2m+2) → √(2/π)`. -/
theorem tendsto_even :
    Tendsto (fun m : ℕ => crossingFactor (2 * m + 2) * Real.sqrt (2 * (m : ℝ) + 2)) atTop
      (𝓝 (Real.sqrt (2 / π))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hsq : ∀ m : ℕ, (crossingFactor (2 * m + 2) * Real.sqrt (2 * (m : ℝ) + 2)) ^ 2
      = (4 / π ^ 2) * Real.Wallis.W m * ((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1)) := by
    intro m
    have h2m1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    rw [mul_pow, Real.sq_sqrt (by positivity), crossingFactor_even, mul_pow, evenProd_sq_eq]
    field_simp
    ring
  have e2 : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1)) atTop (𝓝 1) := by
    have hden : Tendsto (fun m : ℕ => 2 * (m : ℝ) + 1) atTop atTop := by
      refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h0 : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
    have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add h0
    rw [add_zero] at hsum
    refine hsum.congr (fun m => ?_)
    have h2m1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hc : Tendsto (fun _ : ℕ => (4 / π ^ 2)) atTop (𝓝 (4 / π ^ 2)) := tendsto_const_nhds
  have hlim_sq : Tendsto (fun m : ℕ => (crossingFactor (2 * m + 2) * Real.sqrt (2 * (m : ℝ) + 2)) ^ 2)
      atTop (𝓝 (2 / π)) := by
    have prod := (hc.mul Real.Wallis.tendsto_W_nhds_pi_div_two).mul e2
    rw [show (4 / π ^ 2) * (π / 2) * 1 = 2 / π by field_simp; ring] at prod
    exact prod.congr (fun m => (hsq m).symm)
  have hroot := (Real.continuous_sqrt.tendsto (2 / π)).comp hlim_sq
  refine hroot.congr (fun m => ?_)
  exact Real.sqrt_sq (mul_nonneg (crossingFactor_even_pos m).le (Real.sqrt_nonneg _))

/-- **Odd-subsequence asymptotic**: `α_{2m+3} · √(2m+3) → √(2/π)`. -/
theorem tendsto_odd :
    Tendsto (fun m : ℕ => crossingFactor (2 * m + 3) * Real.sqrt (2 * (m : ℝ) + 3)) atTop
      (𝓝 (Real.sqrt (2 / π))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hsq : ∀ m : ℕ, (crossingFactor (2 * m + 3) * Real.sqrt (2 * (m : ℝ) + 3)) ^ 2
      = ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3) / (4 * ((m : ℝ) + 1) ^ 2)) * (1 / Real.Wallis.W m) := by
    intro m
    have hWne : Real.Wallis.W m ≠ 0 := ne_of_gt (Real.Wallis.W_pos m)
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    rw [mul_pow, Real.sq_sqrt (by positivity), crossingFactor_odd, mul_pow, oddProd_sq_eq]
    field_simp
    ring
  have e2 : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3) / (4 * ((m : ℝ) + 1) ^ 2))
      atTop (𝓝 1) := by
    have hden : Tendsto (fun m : ℕ => 4 * ((m : ℝ) + 1) ^ 2) atTop atTop := by
      refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
      nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg ((m : ℝ) + 1)]
    have h0 : Tendsto (fun m : ℕ => (4 * ((m : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
    have hsum := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at hsum
    refine hsum.congr (fun m => ?_)
    have hm1 : (4 * ((m : ℝ) + 1) ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have e1 : Tendsto (fun m : ℕ => 1 / Real.Wallis.W m) atTop (𝓝 (2 / π)) := by
    have hinv := Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ ((by positivity : (0 : ℝ) < π / 2).ne')
    rw [show (π / 2)⁻¹ = 2 / π by rw [inv_div]] at hinv
    simpa [one_div] using hinv
  have hlim_sq : Tendsto (fun m : ℕ => (crossingFactor (2 * m + 3) * Real.sqrt (2 * (m : ℝ) + 3)) ^ 2)
      atTop (𝓝 (2 / π)) := by
    have prod := e2.mul e1
    rw [one_mul] at prod
    exact prod.congr (fun m => (hsq m).symm)
  have hroot := (Real.continuous_sqrt.tendsto (2 / π)).comp hlim_sq
  refine hroot.congr (fun m => ?_)
  exact Real.sqrt_sq (mul_nonneg (crossingFactor_odd_pos m).le (Real.sqrt_nonneg _))

/-- **The full asymptotic** `αₙ ~ √(2/(πn))`, i.e. `αₙ · √n → √(2/π)`, obtained by
    merging the even and odd subsequence limits over all `n`. -/
theorem tendsto_crossingFactor_sqrt :
    Tendsto (fun n : ℕ => crossingFactor n * Real.sqrt (n : ℝ)) atTop
      (𝓝 (Real.sqrt (2 / π))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Me, hMe⟩ := (Metric.tendsto_atTop.mp tendsto_even) ε hε
  obtain ⟨Mo, hMo⟩ := (Metric.tendsto_atTop.mp tendsto_odd) ε hε
  refine ⟨2 * max Me Mo + 2, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨k, hk⟩
  · set m := r - 1 with hmdef
    have hrge : r ≥ max Me Mo + 1 := by omega
    have hnm : n = 2 * m + 2 := by omega
    have hmge : Me ≤ m := le_trans (le_max_left Me Mo) (by omega)
    have key := hMe m hmge
    have heq : crossingFactor n * Real.sqrt (n : ℝ)
        = crossingFactor (2 * m + 2) * Real.sqrt (2 * (m : ℝ) + 2) := by
      rw [hnm]; push_cast; ring
    rw [heq]; exact key
  · set m := k - 1 with hmdef
    have hkge : k ≥ max Me Mo + 1 := by omega
    have hnm : n = 2 * m + 3 := by omega
    have hmge : Mo ≤ m := le_trans (le_max_right Me Mo) (by omega)
    have key := hMo m hmge
    have heq : crossingFactor n * Real.sqrt (n : ℝ)
        = crossingFactor (2 * m + 3) * Real.sqrt (2 * (m : ℝ) + 3) := by
      rw [hnm]; push_cast; ring
    rw [heq]; exact key

/-
## Significance

The parent entry gives the closed-form telescoping products for the Buffon
crossing factor `αₙ` but stops short of their asymptotics. This entry extracts the
precise growth `αₙ ~ √(2/(πn))` directly from those products. The mechanism is the
**Wallis bridge** `W m = (2m+1)·Eₘ²` (`wallis_eq`): the even product squared is
exactly Mathlib's Wallis partial product divided by `2m+1`, so the limit
`W m → π/2` transfers verbatim to `(2m+1)·Eₘ² → π/2` — no Stirling expansion of
the Gamma quotient is used anywhere. The same bridge yields the sharp two-sided
bounds `π/(4(m+1)) ≤ Eₘ² ≤ π/(4m+2)`, while the bare telescoping identity
`Eₘ·Oₘ = 1/(m+1)` gives the rational bound `Eₘ² < 1/(m+1)`. The even and odd
asymptotics are then merged to `αₙ·√n → √(2/π)` over all `n`. Verified with no
axioms and no `native_decide`.
-/

end BuffonCrossingAsymptotic
