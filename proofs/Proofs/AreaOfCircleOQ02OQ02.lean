/-
  N-Ball Volume Vanishes in High Dimensions:  V_n → 0  as  n → ∞

  Open Question: area-of-circle-oq-02-oq-02
  Parent:        area-of-circle-oq-02  (N-Dimensional Ball Volume Formula)

  The volume of the unit n-ball is

      V_n = π^(n/2) / Γ(n/2 + 1).

  Although V_n first GROWS with n (it peaks near n = 5, where V_5 ≈ 5.26),
  it ultimately DECAYS to 0: in high dimensions the unit ball occupies a
  vanishing fraction of its bounding cube.  This file proves the limit.

  Main results:
  * `unitBallVolume_two_mul`            : V_{2m} = π^m / m!     (exact even closed form)
  * `unitBallVolume_two_mul_add_one_le` : V_{2m+1} ≤ 2·π^m / m! (odd uniform bound)
  * `unitBallVolume_tendsto_zero`       : Tendsto unitBallVolume atTop (𝓝 0)   ★ MAIN
  * `volume_unitBall_toReal_tendsto_zero`
        : the actual Lebesgue measure of the unit ball in
          EuclideanSpace ℝ (Fin n) tends to 0.

  Strategy (elementary; the limit step is Gamma-free):
  * The even subsequence has the exact closed form V_{2m} = π^m / m!, which
    tends to 0 by Mathlib's `tendsto_pow_div_factorial_atTop`
    (an exponential is eventually beaten by a factorial).
  * The odd subsequence is bounded by 2·π^m / m!, proved by induction from
    the recurrence V_n = V_{n-2}·2π/n, since each step's factor satisfies
    2π/(2m+3) ≤ π/(m+1).  A squeeze then sends it to 0.
  * The two subsequences cover ℕ, so an ε–N parity argument combines them.

  This file is deliberately self-contained (it imports only Mathlib and
  re-derives the unit ball volume, its recurrence, and the Euclidean
  scaling law from `EuclideanSpace.volume_ball`).  It carries no axioms
  and no `sorry`s.
-/

import Mathlib

open MeasureTheory Metric Real Filter Topology
open scoped Nat

namespace AreaOfCircleOQ02OQ02

/-
## Part I: The unit n-ball volume and its basic structure
-/

/-- The volume of the unit `n`-ball: `V_n = π^(n/2) / Γ(n/2 + 1)`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The unit ball volume is non-negative. -/
theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n := by
  unfold unitBallVolume
  apply div_nonneg
  · exact rpow_nonneg (le_of_lt pi_pos) _
  · exact le_of_lt (Gamma_pos_of_pos (by positivity))

/-- Helper: `Γ(3/2) = √π / 2`, from `Γ(1/2 + 1) = (1/2)·Γ(1/2)` and `Γ(1/2) = √π`. -/
private lemma gamma_three_div_two : Gamma (3 / 2 : ℝ) = √π / 2 := by
  have h := Real.Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
  rw [h, Gamma_one_half_eq]
  ring

/-- For `n = 1`, the unit ball is the interval `[-1,1]`, of length 2. -/
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  unfold unitBallVolume
  simp only [Nat.cast_one]
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring, gamma_three_div_two]
  rw [← Real.sqrt_eq_rpow]
  have h : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [h.ne']

/-- For `n = 2`, the unit ball is the unit disk, of area π (the area-of-circle case). -/
theorem unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) / 2 + 1 = 2 from by ring, show (2 : ℝ) / 2 = 1 from by ring]
  rw [rpow_one, Gamma_two]
  simp

/-- **Dimension recurrence.**  `V_n = V_{n-2} · 2π / n` for `n ≥ 2`, from the
    Gamma functional equation `Γ(x+1) = x·Γ(x)`. -/
theorem unitBallVolume_recurrence (n : ℕ) (hn : 2 ≤ n) :
    unitBallVolume n = unitBallVolume (n - 2) * (2 * π) / n := by
  unfold unitBallVolume
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]; norm_num
  rw [hcast, show (n : ℝ) / 2 = ((n : ℝ) - 2) / 2 + 1 from by ring,
      Real.rpow_add pi_pos, Real.rpow_one]
  have hpos : (0 : ℝ) < ((n : ℝ) - 2) / 2 + 1 := by linarith
  rw [Real.Gamma_add_one (ne_of_gt hpos)]
  have hG : Gamma (((n : ℝ) - 2) / 2 + 1) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hpos)
  have ha1 : ((n : ℝ) - 2) / 2 + 1 ≠ 0 := ne_of_gt hpos
  rw [div_mul_eq_mul_div, div_div,
      div_eq_div_iff (mul_ne_zero ha1 hG) (mul_ne_zero hG hnn)]
  ring

/-
## Part II: Closed form / bound for the even / odd subsequences
-/

/-- **Even closed form.**  `V_{2m} = π^m / m!`, since `Γ(m+1) = m!`. -/
theorem unitBallVolume_two_mul (m : ℕ) :
    unitBallVolume (2 * m) = π ^ m / (m ! : ℝ) := by
  unfold unitBallVolume
  rw [show ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) by push_cast; ring,
      Real.rpow_natCast, Real.Gamma_nat_eq_factorial]

/-- **Odd uniform bound.**  `V_{2m+1} ≤ 2·π^m / m!`, by induction from the
    recurrence: each step multiplies by `2π/(2m+3) ≤ π/(m+1)`. -/
theorem unitBallVolume_two_mul_add_one_le (m : ℕ) :
    unitBallVolume (2 * m + 1) ≤ 2 * π ^ m / (m ! : ℝ) := by
  induction m with
  | zero =>
    rw [show (2 * 0 + 1) = 1 from rfl, unitBallVolume_one]
    norm_num
  | succ k ih =>
    have hrec := unitBallVolume_recurrence (2 * (k + 1) + 1) (by omega)
    have hidx : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
    rw [hidx] at hrec
    rw [hrec]
    have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hAk : unitBallVolume (2 * k + 1) * (k ! : ℝ) ≤ 2 * π ^ k :=
      (le_div_iff₀ hfac).mp ih
    have ha : 0 ≤ unitBallVolume (2 * k + 1) := unitBallVolume_nonneg _
    have hpi : 0 < π := pi_pos
    have hc : (0 : ℝ) < ((2 * (k + 1) + 1 : ℕ) : ℝ) := by positivity
    have hd : (0 : ℝ) < (((k + 1)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (k + 1)
    rw [div_le_div_iff₀ hc hd]
    have hcast1 : ((2 * (k + 1) + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 3 := by push_cast; ring
    have hcast2 : (((k + 1)! : ℕ) : ℝ) = ((k : ℝ) + 1) * (k ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hcast1, hcast2, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hAk (by positivity : (0 : ℝ) ≤ 2 * π * ((k : ℝ) + 1)),
               pow_pos hpi k, hpi, mul_pos (pow_pos hpi k) hpi, ha]

/-
## Part III: Each subsequence tends to 0
-/

/-- The even subsequence tends to 0: `V_{2m} = π^m / m! → 0`. -/
theorem tendsto_even :
    Tendsto (fun m => unitBallVolume (2 * m)) atTop (𝓝 0) :=
  Filter.Tendsto.congr (fun m => (unitBallVolume_two_mul m).symm)
    (FloorSemiring.tendsto_pow_div_factorial_atTop (π : ℝ))

/-- The odd subsequence tends to 0, squeezed by `2·π^m / m! → 0`. -/
theorem tendsto_odd :
    Tendsto (fun m => unitBallVolume (2 * m + 1)) atTop (𝓝 0) := by
  have hg : Tendsto (fun m => 2 * π ^ m / (m ! : ℝ)) atTop (𝓝 0) := by
    have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (π : ℝ)).const_mul (2 : ℝ)
    simp only [mul_zero] at h
    exact Filter.Tendsto.congr (fun m => (mul_div_assoc 2 (π ^ m) ((m ! : ℝ))).symm) h
  exact squeeze_zero (fun m => unitBallVolume_nonneg _) unitBallVolume_two_mul_add_one_le hg

/-
## Part IV: The main limit  V_n → 0
-/

/-- **Main result.**  The unit `n`-ball volume vanishes as `n → ∞`:

      `V_n = π^(n/2) / Γ(n/2 + 1) ⟶ 0`.

    The even and odd subsequences each tend to 0 and together exhaust ℕ, so an
    ε–N argument over the parity of `n` delivers the full limit. -/
theorem unitBallVolume_tendsto_zero :
    Tendsto unitBallVolume atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Me, hMe⟩ := (Metric.tendsto_atTop.mp tendsto_even) ε hε
  obtain ⟨Mo, hMo⟩ := (Metric.tendsto_atTop.mp tendsto_odd) ε hε
  refine ⟨2 * Me + 2 * Mo + 1, fun n hn => ?_⟩
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    have hk' : Me ≤ k := by omega
    simpa using hMe k hk'
  · subst hk
    have hk' : Mo ≤ k := by omega
    simpa using hMo k hk'

/-- Restatement: for every `ε > 0` the unit ball volume is eventually `< ε`. -/
theorem unitBallVolume_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, unitBallVolume n < ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp unitBallVolume_tendsto_zero) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (unitBallVolume_nonneg n)] at h
  exact h

/-
## Part V: Measure-theoretic headline

The actual Lebesgue measure of the unit ball in Euclidean space tends to 0.
We derive the Euclidean scaling law directly from `EuclideanSpace.volume_ball`,
keeping the whole development assumption-free.
-/

/-- Bridge identity `(√π)^n = π^(n/2)` between Mathlib's and the gallery's forms. -/
private lemma sqrt_pi_pow_eq (n : ℕ) : (Real.sqrt π) ^ n = π ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul Real.pi_pos.le]
  congr 1
  ring

/-- The Lebesgue measure of the unit ball equals `V_n` for `n ≥ 1`, from
    `EuclideanSpace.volume_ball`. -/
theorem volume_unitBall_eq (n : ℕ) (hn : 0 < n) :
    volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) = ENNReal.ofReal (unitBallVolume n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  unfold unitBallVolume
  rw [sqrt_pi_pow_eq]

/-- **Geometric headline.**  The Lebesgue measure of the unit ball in
    `EuclideanSpace ℝ (Fin n)` tends to 0 as the dimension `n → ∞`. -/
theorem volume_unitBall_toReal_tendsto_zero :
    Tendsto (fun n => (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)
      atTop (𝓝 0) := by
  refine Filter.Tendsto.congr' ?_ unitBallVolume_tendsto_zero
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [volume_unitBall_eq n hn, ENNReal.toReal_ofReal (unitBallVolume_nonneg n)]

end AreaOfCircleOQ02OQ02
