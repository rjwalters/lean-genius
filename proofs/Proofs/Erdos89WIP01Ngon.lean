/-
  Erdős Problem #89 — the regular `n`-gon and the upper bound `g(n) ≤ ⌊n/2⌋`

  Source: https://erdosproblems.com/89
  Parent: `Proofs/Erdos89WIP01.lean` (the distinct-distances ladder: exact values
  `g(0) = g(1) = 0`, `g(2) = g(3) = 1`, `g(4) = g(5) = 2`, the sandwich
  `2 ≤ g(6) ≤ 3`, monotonicity, and the linear bound `g(n) ≤ n − 1` via the
  collinear arithmetic progression `apSet`).

  This file adds the classical pre-Erdős upper bound: the **regular `n`-gon**
  on the unit circle realises at most `⌊n/2⌋` distinct distances, halving the
  progression bound `n − 1`.

  * `ngonPoint n k = (cos(2πk/n), sin(2πk/n))` — the `k`-th vertex.
  * `dist_ngonPoint` — the **chord-length formula**: the distance between
    vertices `i` and `j` is `2·|sin(π(i−j)/n)|`. All trigonometry in the file
    flows through this single identity (`(cos A − cos B)² + (sin A − sin B)²
    = 2 − 2cos(A−B) = 4 sin²((A−B)/2)`).
  * `ngonPoint_injOn` / `ngonSet_card` — the `n` vertices are pairwise
    distinct: a coincidence would force `sin(π(i−j)/n) = 0` with
    `|π(i−j)/n| < π`, so `i = j`. Injectivity is thus *derived from the
    distance formula* rather than proved by separate coordinate geometry.
  * `ngonSet_distinctDistances_subset` — every chord length equals
    `2·sin(πk/n)` for some `k ∈ {1, …, ⌊n/2⌋}`: the index `m = |i − j|`
    reflects into `min(m, n−m)` via `sin(π − x) = sin x`.
  * **`minDistinctDistances_le_half`** — `g(n) ≤ ⌊n/2⌋`. One uniform witness
    now recovers every exact upper value in the ladder: `g(3) ≤ 1` (triangle),
    `g(4) ≤ 2` (square), `g(5) ≤ 2` (pentagon), `g(6) ≤ 3` (hexagon — an
    alternative to the parent's pentagon-plus-centre witness), and it is tight
    at `n = 3, 4, 5` against the parent's exact values.
  * `minDistinctDistances_seven_le_three` / `minDistinctDistances_seven_mem_Icc`
    — the first NEW ladder entry from the bound: `2 ≤ g(7) ≤ 3` (previously the
    best in-file bound at `n = 7` was `g(7) ≤ 6`). The true value is `g(7) = 3`;
    the lower half needs the planar two-distance-set bound, open in the parent.

  What the bound does NOT give: `g(n) ≥ ⌊n/2⌋` is FALSE for large `n` (Erdős's
  `√n`-ish constructions beat the `n`-gon), so this is a genuine upper-bound
  brick only — the conjectured truth is `Θ(n/√(log n))` (Guth–Katz), which
  stays deep and axiomatized in the parent `Erdos89Problem`.

  All results are axiom-free (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`) and contain no `sorry`.
-/

import Mathlib
import Proofs.Erdos89WIP01

open Finset Real

namespace Erdos89

/- ## The vertices and the chord-length formula -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle:
`(cos(2πk/n), sin(2πk/n))`. -/
noncomputable def ngonPoint (n k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * k / n), Real.sin (2 * π * k / n)]

/-- **Chord-length formula.** The distance between vertices `i` and `j` of the
regular `n`-gon is `2·|sin(π(i−j)/n)|`. The identity behind it:
`(cos A − cos B)² + (sin A − sin B)² = 2 − 2cos(A−B) = 4·sin²((A−B)/2)`. -/
theorem dist_ngonPoint (n i j : ℕ) :
    Erdos89.dist (ngonPoint n i) (ngonPoint n j)
      = 2 * |Real.sin (π * ((i : ℝ) - j) / n)| := by
  unfold Erdos89.dist ngonPoint
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  have hAB : 2 * π * (i : ℝ) / n - 2 * π * (j : ℝ) / n
      = 2 * (π * ((i : ℝ) - j) / n) := by ring
  set θ := π * ((i : ℝ) - j) / n with hθ
  have h34 : Real.cos (2 * π * (i : ℝ) / n) * Real.cos (2 * π * (j : ℝ) / n)
      + Real.sin (2 * π * (i : ℝ) / n) * Real.sin (2 * π * (j : ℝ) / n)
      = 1 - 2 * Real.sin θ ^ 2 := by
    have h3 := Real.cos_sub (2 * π * (i : ℝ) / n) (2 * π * (j : ℝ) / n)
    have h4 : Real.cos (2 * π * (i : ℝ) / n - 2 * π * (j : ℝ) / n)
        = 1 - 2 * Real.sin θ ^ 2 := by
      rw [hAB, Real.cos_two_mul]
      have h5 := Real.sin_sq_add_cos_sq θ
      linear_combination 2 * h5
    linear_combination h4 - h3
  have hkey : (Real.cos (2 * π * (i : ℝ) / n) - Real.cos (2 * π * (j : ℝ) / n)) ^ 2
      + (Real.sin (2 * π * (i : ℝ) / n) - Real.sin (2 * π * (j : ℝ) / n)) ^ 2
      = (2 * Real.sin θ) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq (2 * π * (i : ℝ) / n)
    have h2 := Real.sin_sq_add_cos_sq (2 * π * (j : ℝ) / n)
    linear_combination h1 + h2 - 2 * h34
  rw [hkey, Real.sqrt_sq_eq_abs, abs_mul]
  norm_num

/- ## The vertices are pairwise distinct

Injectivity is derived from the chord-length formula itself: coinciding
vertices would have distance `0`, forcing `sin(π(i−j)/n) = 0` with the
argument strictly inside `(−π, π)`, hence `i = j`. -/

/-- The vertex map is injective on `{0, …, n−1}`. -/
theorem ngonPoint_injOn (n : ℕ) :
    Set.InjOn (ngonPoint n) ↑(Finset.range n) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hnn : 0 < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast hnn
  have hd : Erdos89.dist (ngonPoint n i) (ngonPoint n j) = 0 := by
    show ‖ngonPoint n i - ngonPoint n j‖ = 0
    rw [hij, sub_self, norm_zero]
  rw [dist_ngonPoint] at hd
  have hs : Real.sin (π * ((i : ℝ) - j) / n) = 0 := by
    have habs : |Real.sin (π * ((i : ℝ) - j) / n)| = 0 := by linarith
    exact abs_eq_zero.mp habs
  have hπ := Real.pi_pos
  have hilt : (i : ℝ) - j < n := by
    have h1 : (i : ℝ) < n := by exact_mod_cast hi
    have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hjlt : -(n : ℝ) < (i : ℝ) - j := by
    have h1 : (j : ℝ) < n := by exact_mod_cast hj
    have h2 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have hlt : π * ((i : ℝ) - j) / n < π := by
    have hmul : π * ((i : ℝ) - j) < π * n := by nlinarith
    calc π * ((i : ℝ) - j) / n = π * ((i : ℝ) - j) * (n : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
      _ < π * n * (n : ℝ)⁻¹ := by
          exact mul_lt_mul_of_pos_right hmul (inv_pos.mpr hn)
      _ = π := by field_simp
  have hgt : -π < π * ((i : ℝ) - j) / n := by
    have hmul : π * (-(n : ℝ)) < π * ((i : ℝ) - j) := by nlinarith
    calc -π = π * (-(n : ℝ)) * (n : ℝ)⁻¹ := by field_simp
      _ < π * ((i : ℝ) - j) * (n : ℝ)⁻¹ := by
          exact mul_lt_mul_of_pos_right hmul (inv_pos.mpr hn)
      _ = π * ((i : ℝ) - j) / n := by rw [div_eq_mul_inv]
  have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt hgt hlt).mp hs
  rcases div_eq_zero_iff.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' Real.pi_ne_zero
    · have : (i : ℝ) = j := by linarith [sub_eq_zero.mp h']
      exact_mod_cast this
  · exact absurd h (ne_of_gt hn)

/-- The regular `n`-gon as a point set. -/
noncomputable def ngonSet (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (Finset.range n).image (ngonPoint n)

/-- The `n`-gon has exactly `n` points. -/
theorem ngonSet_card (n : ℕ) : (ngonSet n).card = n := by
  rw [ngonSet, Finset.card_image_of_injOn (ngonPoint_injOn n), Finset.card_range]

/- ## Chord lengths take at most `⌊n/2⌋` values

`sin(πm/n) = sin(π(n−m)/n)` reflects the index `m = |i−j| ∈ {1, …, n−1}` into
`min(m, n−m) ∈ {1, …, ⌊n/2⌋}`, so every chord length is `2·sin(πk/n)` for some
`k` in that short range. -/

/-- Every chord value `2·|sin(πm/n)|` with `1 ≤ m < n` lies in the image of
`{1, …, ⌊n/2⌋}` under `k ↦ 2·sin(πk/n)` — reflect `m` to `n − m` when
`2m > n`, via `sin(π − x) = sin x`. -/
theorem two_sin_mem_image {n m : ℕ} (h1 : 1 ≤ m) (hm : m < n) :
    2 * |Real.sin (π * m / n)|
      ∈ (Finset.Icc 1 (n / 2)).image (fun k : ℕ => 2 * Real.sin (π * k / n)) := by
  have hnn : 0 < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast hnn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast h1
  have hmn : (m : ℝ) < n := by exact_mod_cast hm
  have hπ := Real.pi_pos
  have harg_pos : 0 < π * m / n := div_pos (mul_pos hπ hm0) hn
  have harg_lt : π * m / n < π := by
    have hmul : π * (m : ℝ) < π * n := by nlinarith
    calc π * (m : ℝ) / n = π * (m : ℝ) * (n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ < π * n * (n : ℝ)⁻¹ := mul_lt_mul_of_pos_right hmul (inv_pos.mpr hn)
      _ = π := by field_simp
  have hpos := Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt
  rw [abs_of_pos hpos]
  by_cases hhalf : 2 * m ≤ n
  · exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨h1, by omega⟩, rfl⟩
  · refine Finset.mem_image.mpr
      ⟨n - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hm.le
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn
    have harg : π * ((n : ℝ) - m) / n = π - π * m / n := by
      field_simp
    rw [hcast, harg, Real.sin_pi_sub]

/-- Every distance of the `n`-gon is `2·sin(πk/n)` for some `k ∈ {1, …, ⌊n/2⌋}`. -/
theorem ngonSet_distinctDistances_subset (n : ℕ) :
    distinctDistances (ngonSet n)
      ⊆ (Finset.Icc 1 (n / 2)).image (fun k : ℕ => 2 * Real.sin (π * k / n)) := by
  rw [distinctDistances_eq_image]
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨⟨p1, p2⟩, hpq, rfl⟩ := hd
  rw [Finset.mem_offDiag] at hpq
  obtain ⟨h1, h2, hne⟩ := hpq
  rw [ngonSet, Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  rw [Finset.mem_range] at ha hb
  have hab : a ≠ b := fun h => hne (by rw [h])
  rw [dist_ngonPoint]
  rcases Nat.lt_or_ge a b with hlt | hge
  · -- `a < b`: the index is `b − a`, entering through `sin(−x) = −sin x`.
    have hm : (a : ℝ) - b = -(((b - a : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hlt.le]; ring
    have hneg : π * ((a : ℝ) - b) / n = -(π * ((b - a : ℕ) : ℝ) / n) := by
      rw [hm]; ring
    rw [hneg, Real.sin_neg, abs_neg]
    exact two_sin_mem_image (by omega) (by omega)
  · -- `b < a`: the index is `a − b` directly.
    have hlt' : b < a := by omega
    have hm : (a : ℝ) - b = ((a - b : ℕ) : ℝ) := (Nat.cast_sub hlt'.le).symm
    rw [hm]
    exact two_sin_mem_image (by omega) (by omega)

/- ## The halving upper bound and the first new ladder entry -/

/-- **The `n`-gon upper bound: `g(n) ≤ ⌊n/2⌋`.** The regular `n`-gon is an
`n`-point set whose chord lengths take at most `⌊n/2⌋` values, halving the
progression bound `g(n) ≤ n − 1` (`minDistinctDistances_le_pred`). One uniform
witness recovers the whole known upper ladder — `g(3) ≤ 1`, `g(4) ≤ 2`,
`g(5) ≤ 2`, `g(6) ≤ 3` — and is TIGHT against the parent's exact values at
`n = 3, 4, 5`. (For large `n` the bound is far from optimal: the truth is
`Θ(n/√(log n))`, and already Erdős's grid beats the `n`-gon.) -/
theorem minDistinctDistances_le_half (n : ℕ) :
    minDistinctDistances n ≤ n / 2 := by
  calc minDistinctDistances n
      ≤ numDistinctDistances (ngonSet n) :=
        minDistinctDistances_le_of_card_eq (ngonSet_card n)
    _ = (distinctDistances (ngonSet n)).card := rfl
    _ ≤ ((Finset.Icc 1 (n / 2)).image
          (fun k : ℕ => 2 * Real.sin (π * k / n))).card :=
        Finset.card_le_card (ngonSet_distinctDistances_subset n)
    _ ≤ (Finset.Icc 1 (n / 2)).card := Finset.card_image_le
    _ = n / 2 := by rw [Nat.card_Icc]

/-- **`g(7) ≤ 3`** — the first ladder entry beyond the parent's table: the
regular heptagon realises only the three chord lengths `2·sin(kπ/7)`,
`k = 1, 2, 3`. Before this bound the best in-file estimate at `n = 7` was the
progression's `g(7) ≤ 6`. -/
theorem minDistinctDistances_seven_le_three : minDistinctDistances 7 ≤ 3 := by
  have h := minDistinctDistances_le_half 7
  norm_num at h
  exact h

/-- **Sandwich `2 ≤ g(7) ≤ 3`.** The lower half lifts `g(5) = 2` through
monotonicity; the upper half is the heptagon. The true value is `g(7) = 3`,
whose lower bound needs the planar two-distance-set theorem (a two-distance
set in `ℝ²` has at most `5` points) — the same open brick that blocks
`g(6) = 3` in the parent. -/
theorem minDistinctDistances_seven_mem_Icc :
    minDistinctDistances 7 ∈ Set.Icc 2 3 := by
  refine ⟨?_, minDistinctDistances_seven_le_three⟩
  calc 2 = minDistinctDistances 5 := minDistinctDistances_five.symm
    _ ≤ minDistinctDistances 7 := minDistinctDistances_mono (by norm_num)

end Erdos89
