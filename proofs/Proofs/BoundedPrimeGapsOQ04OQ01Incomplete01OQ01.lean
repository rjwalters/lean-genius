/-
  # Aggregating the cotangent sum: ∑ 1/(2‖a/q‖) = O(q log q)

  The parent file `BoundedPrimeGapsOQ04OQ01Incomplete01` proves the **per-residue**
  cosecant→distance bound

      1/|sin(π a/q)| ≤ 1/(2‖a/q‖),      ‖x‖ = |x − round x| ∈ [0, 1/2].

  In the Pólya–Vinogradov argument this per-term bound is summed over the nonzero
  residues `a = 1, …, q−1`, producing the **cotangent sum**

      S(q) := ∑_{a=1}^{q-1} 1/(2‖a/q‖).

  This file proves the standard **elementary** bound completing that aggregation:

      S(q) ≤ q · H_{q-1} ≤ q · (1 + log q)  =  O(q log q),

  where `H_{q-1} = ∑_{a=1}^{q-1} 1/a` is the harmonic number.

  ## The elementary mechanism

  For `1 ≤ a ≤ q−1` the fraction `a/q ∈ (0,1)` has nearest integer `0` (if `2a < q`)
  or `1` (if `2a ≥ q`), so its distance to the nearest integer is

      ‖a/q‖ = min(a, q−a) / q.                         (`dist_frac_eq`)

  Hence the summand is the *exact rational*

      1/(2‖a/q‖) = q / (2·min(a, q−a)).

  The key inequality is then completely elementary: `min(a, q−a)` is one of `a`, `q−a`,
  so `1/min(a, q−a) ≤ 1/a + 1/(q−a)`, giving

      q/(2·min(a,q−a)) ≤ (q/2)·(1/a + 1/(q−a)).

  Summing and reindexing `a ↦ q − a` collapses `∑ 1/(q−a) = ∑ 1/a`, so both halves
  equal `H_{q-1}` and the `q/2` doubles back to `q·H_{q-1}`. No pairing case-analysis
  or trigonometry is needed — only positivity and a single reflection of the index set.

  ## Results
  * `dist_frac_eq`              : `‖a/q‖ = min(a,q−a)/q` for `0 < a < q` (the bridge to `round`).
  * `cotangent_sum_le_harmonic` : **`S(q) ≤ q · H_{q-1}`** (the exact elementary majorant).
  * `cotangent_sum_bigO`        : **`S(q) ≤ q · (1 + log q)`** (the explicit `O(q log q)`).

  Everything is machine-checked with no axioms beyond Mathlib. The harmonic→log step
  reuses Mathlib's `harmonic_le_one_add_log`.

  Parent:  BoundedPrimeGapsOQ04OQ01Incomplete01.lean  (per-term cosecant bound).
-/

import Mathlib

namespace BoundedPrimeGapsOQ04OQ01Incomplete01OQ01

open Real Finset

/-- **The nearest-integer distance of a proper fraction.** For `0 < a < q`, the
fraction `a/q ∈ (0,1)` rounds to `0` (when `2a < q`) or `1` (when `2a ≥ q`), so its
distance to the nearest integer is `min(a, q−a)/q`. This is the identity that turns
the transcendental summand `1/(2‖a/q‖)` into the exact rational `q/(2·min(a,q−a))`. -/
theorem dist_frac_eq (q a : ℕ) (ha : 0 < a) (haq : a < q) :
    |(a : ℝ) / q - round ((a : ℝ) / q)| = (min a (q - a) : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le ha (le_of_lt haq)
  have haq' : (a : ℝ) < q := by exact_mod_cast haq
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hfrac_lo : (0 : ℝ) ≤ (a : ℝ) / q := by positivity
  have hfrac_hi : (a : ℝ) / q < 1 := (div_lt_one hq0).mpr haq'
  rcases lt_or_ge (2 * a) q with h2 | h2
  · -- `2a < q`: `a/q < 1/2`, rounds to 0, distance `= a/q`, and `min = a`.
    have h2' : (2 : ℝ) * a < q := by exact_mod_cast h2
    have hlt_half : (a : ℝ) / q < 1 / 2 := by
      rw [div_lt_iff₀ hq0]; linarith
    have hround : round ((a : ℝ) / q) = 0 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    have hmin : min (a : ℝ) ((q : ℝ) - a) = a := by
      apply min_eq_left; linarith
    rw [hround]
    simp only [Int.cast_zero, sub_zero]
    rw [hmin, abs_of_nonneg hfrac_lo]
  · -- `2a ≥ q`: `a/q ≥ 1/2`, rounds to 1, distance `= 1 − a/q = (q−a)/q`, and `min = q−a`.
    have h2' : (q : ℝ) ≤ 2 * a := by exact_mod_cast h2
    have hge_half : (1 : ℝ) / 2 ≤ (a : ℝ) / q := by
      rw [le_div_iff₀ hq0]; linarith
    have hround : round ((a : ℝ) / q) = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    have hmin : min (a : ℝ) ((q : ℝ) - a) = (q : ℝ) - a := by
      apply min_eq_right; linarith
    rw [hround]
    simp only [Int.cast_one]
    rw [hmin, abs_of_nonpos (by linarith), neg_sub, sub_div, div_self (ne_of_gt hq0)]

/-- **The elementary majorant of the cotangent sum.** For `q ≥ 2`,

  `S(q) = ∑_{a=1}^{q-1} 1/(2‖a/q‖) ≤ q · H_{q-1}`,

where `H_{q-1} = ∑_{a=1}^{q-1} 1/a`. This is the exact bound produced by aggregating
the per-residue cosecant bound; combined with `harmonic_le_one_add_log` it yields the
`O(q log q)` cotangent-sum estimate underlying Pólya–Vinogradov. -/
theorem cotangent_sum_le_harmonic (q : ℕ) (hq : 2 ≤ q) :
    ∑ a ∈ Finset.Ico 1 q, 1 / (2 * |(a : ℝ) / q - round ((a : ℝ) / q)|)
      ≤ (q : ℝ) * ∑ a ∈ Finset.Ico 1 q, ((a : ℝ))⁻¹ := by
  have hq0 : (0 : ℝ) < q := by positivity
  -- Step 1: termwise bound  1/(2‖a/q‖) ≤ (q/2)·(1/a + 1/(q−a)).
  have hterm : ∀ a ∈ Finset.Ico 1 q,
      1 / (2 * |(a : ℝ) / q - round ((a : ℝ) / q)|)
        ≤ (q : ℝ) / 2 * ((a : ℝ)⁻¹ + ((q : ℝ) - a)⁻¹) := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hapos : 0 < a := ha1
    have haq : a < q := ha2
    have haR : (0 : ℝ) < a := by exact_mod_cast hapos
    have hqaR : (0 : ℝ) < (q : ℝ) - a := by
      have : (a : ℝ) < q := by exact_mod_cast haq
      linarith
    -- rewrite the distance into the exact rational form `min (a, q−a) / q` (real min).
    rw [dist_frac_eq q a hapos haq]
    have hminR : (0 : ℝ) < min (a : ℝ) ((q : ℝ) - a) := lt_min haR hqaR
    have hMne : min (a : ℝ) ((q : ℝ) - a) ≠ 0 := hminR.ne'
    have hqne : (q : ℝ) ≠ 0 := hq0.ne'
    -- `1/min ≤ 1/a + 1/(q−a)`: `min` is one of the two positive denominators, so its
    -- reciprocal is the larger of `1/a`, `1/(q−a)`, hence at most their sum.
    have hrecip : (min (a : ℝ) ((q : ℝ) - a))⁻¹ ≤ (a : ℝ)⁻¹ + ((q : ℝ) - a)⁻¹ := by
      rcases le_total (a : ℝ) ((q : ℝ) - a) with hle | hle
      · rw [min_eq_left hle]
        have : (0 : ℝ) ≤ ((q : ℝ) - a)⁻¹ := by positivity
        linarith
      · rw [min_eq_right hle]
        have : (0 : ℝ) ≤ (a : ℝ)⁻¹ := by positivity
        linarith
    -- `1/(2·(min/q)) = q/(2·min) = (q/2)·(1/min) ≤ (q/2)·(1/a+1/(q−a))`.
    calc 1 / (2 * (min (a : ℝ) ((q : ℝ) - a) / q))
        = (q : ℝ) / 2 * (min (a : ℝ) ((q : ℝ) - a))⁻¹ := by
          field_simp
      _ ≤ (q : ℝ) / 2 * ((a : ℝ)⁻¹ + ((q : ℝ) - a)⁻¹) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
  -- Step 2: sum the termwise bound.
  refine (Finset.sum_le_sum hterm).trans ?_
  -- ∑ (q/2)(1/a + 1/(q−a)) = (q/2)(∑1/a + ∑1/(q−a)) = (q/2)(H + H) = q·H
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  -- reflect the index a ↦ q − a to identify ∑ 1/(q−a) with ∑ 1/a
  have hreflect : ∑ a ∈ Finset.Ico 1 q, ((q : ℝ) - a)⁻¹ = ∑ a ∈ Finset.Ico 1 q, ((a : ℝ))⁻¹ := by
    apply Finset.sum_nbij' (fun a => q - a) (fun a => q - a)
    · intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha
      have : ((q - a : ℕ) : ℝ) = (q : ℝ) - a := by rw [Nat.cast_sub (by omega)]
      rw [this]
  rw [hreflect]
  -- (q/2)·(H + H) = q·H
  rw [← two_mul, ← mul_assoc]
  rw [show (q : ℝ) / 2 * 2 = (q : ℝ) by ring]

/-- **The `O(q log q)` cotangent-sum bound.** For `q ≥ 2`,

  `S(q) = ∑_{a=1}^{q-1} 1/(2‖a/q‖) ≤ q · (1 + log q)`.

This is the explicit `O(q log q)` estimate for the aggregated cotangent sum used to
close the Pólya–Vinogradov character-sum bound. It follows from the elementary
majorant `cotangent_sum_le_harmonic` and Mathlib's harmonic-number bound
`harmonic_le_one_add_log`. -/
theorem cotangent_sum_bigO (q : ℕ) (hq : 2 ≤ q) :
    ∑ a ∈ Finset.Ico 1 q, 1 / (2 * |(a : ℝ) / q - round ((a : ℝ) / q)|)
      ≤ (q : ℝ) * (1 + Real.log q) := by
  refine (cotangent_sum_le_harmonic q hq).trans ?_
  have hq0 : (0 : ℝ) < q := by positivity
  -- identify the real harmonic sum with Mathlib's `harmonic (q-1)`
  have hsum_eq : ∑ a ∈ Finset.Ico 1 q, ((a : ℝ))⁻¹ = (harmonic (q - 1) : ℝ) := by
    have hIco : Finset.Ico 1 q = Finset.Icc 1 (q - 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hsum_eq]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hq0)
  refine (harmonic_le_one_add_log (q - 1)).trans ?_
  have hpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    have : 1 ≤ q - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hle : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    have : q - 1 ≤ q := by omega
    exact_mod_cast this
  have hlog : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := Real.log_le_log hpos hle
  linarith

end BoundedPrimeGapsOQ04OQ01Incomplete01OQ01
