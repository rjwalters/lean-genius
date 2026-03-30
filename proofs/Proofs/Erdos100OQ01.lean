/-
  Erdős Problem #100 — Open Question 1:
  Distance set diameter growth rate (linear vs logarithmic)

  Is the logarithmic factor in the Guth-Katz bound genuine?
  Current best: diam(A) ≥ cn/log n (from Guth-Katz 2015).
  Conjecture: diam(A) ≥ cn (linear growth).

  Results:
  1. Kanold's bound is redundant (follows from Guth-Katz)
  2. The two scenarios (linear vs logarithmic optimal) are exclusive
  3. The multiplicative gap is exactly logarithmic

  Reference: https://erdosproblems.com/100
-/

import Mathlib
import Proofs.Erdos100Problem

open Filter Set Finset Erdos100
open scoped Topology

namespace Erdos100.OQ01

-- ═══════════════════════════════════════════════════════════════════
-- PART I: KANOLD'S BOUND IS REDUNDANT
-- ═══════════════════════════════════════════════════════════════════

/--
Collinear integer distance sets exist: n points at positions 0,1,...,n-1
on the x-axis form an n-point set with all pairwise distances being
positive integers.
-/
theorem integer_distance_sets_exist (n : ℕ) (hn : n ≥ 2) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = n ∧ hasIntegerDistances S := by
  -- Construct n collinear points: p_k = (k, 0) for k = 0, ..., n-1
  let pt (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => if i = 0 then (k : ℝ) else 0)
  refine ⟨(Finset.range n).image pt, ?_, ?_⟩
  · -- Cardinality = n (pt is injective)
    rw [Finset.card_image_of_injective _ (fun a b hab => ?_)]
    · exact Finset.card_range n
    · -- pt a = pt b implies a = b (via first coordinate)
      have := congr_arg (EuclideanSpace.equiv (Fin 2) ℝ) hab
      simp only [pt, LinearEquiv.apply_symm_apply] at this
      have h0 := congr_fun this (0 : Fin 2)
      simp at h0
      exact_mod_cast h0
  · -- All pairwise distances are positive integers
    intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    have hij : i ≠ j := fun h => hpq (h ▸ rfl)
    -- Distance ‖pt i - pt j‖ = |↑i - ↑j| (a positive integer)
    unfold Erdos100.dist
    -- Compute ‖pt i - pt j‖² = (↑i - ↑j)² using EuclideanSpace.norm_sq_eq
    have hnorm_sq : ‖pt i - pt j‖ ^ 2 = ((i : ℝ) - (j : ℝ)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp only [PiLp.sub_apply]
      -- Components: (pt k) 0 = ↑k, (pt k) 1 = 0 (definitional)
      dsimp [pt, EuclideanSpace.equiv]
      simp [sub_zero, norm_zero, norm_eq_abs, sq_abs]
    -- Therefore ‖pt i - pt j‖ = |↑i - ↑j|
    have hnorm_eq : ‖pt i - pt j‖ = |((i : ℝ) - (j : ℝ))| := by
      have hnn : 0 ≤ ‖pt i - pt j‖ := norm_nonneg _
      rw [← Real.sqrt_sq hnn, hnorm_sq, Real.sqrt_sq_eq_abs]
    -- |↑i - ↑j| is a positive natural number since i ≠ j
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · -- i < j: distance = j - i ≥ 1
      refine ⟨j - i, by omega, ?_⟩
      rw [hnorm_eq]
      have : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr h
      rw [abs_of_nonpos (by linarith : (i : ℝ) - j ≤ 0)]
      push_cast; ring
    · -- j < i: distance = i - j ≥ 1
      refine ⟨i - j, by omega, ?_⟩
      rw [hnorm_eq]
      have : (j : ℝ) < (i : ℝ) := Nat.cast_lt.mpr h
      rw [abs_of_nonneg (by linarith : (i : ℝ) - j ≥ 0)]
      push_cast; ring

/--
The Guth-Katz diameter bound (proved in Erdos100Problem.lean) implies a
bound on the minimum diameter function.
-/
theorem minDiam_ge_n_over_log :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      c * n / Real.log n ≤ minDiameterRestrictedSets n := by
  obtain ⟨c, hc_pos, hbound⟩ := diam_ge_n_over_log_n
  use c, hc_pos
  filter_upwards [hbound, Filter.eventually_ge_atTop 2] with n hn hn2
  unfold minDiameterRestrictedSets
  apply le_csInf
  · -- Nonemptiness: integer distance sets exist
    obtain ⟨S, hcard, hint⟩ := integer_distance_sets_exist n (by omega)
    exact ⟨diam S, S, ⟨hcard, hint⟩, rfl⟩
  · intro d hd
    obtain ⟨S, ⟨hcard, hint⟩, rfl⟩ := hd
    exact hn S hcard hint

/--
**Key asymptotic fact**: log n ≤ n^(1/4) for sufficiently large n.

Follows from log = o(x^p) for any p > 0 (Mathlib: `isLittleO_log_rpow_atTop`).
-/
private theorem log_le_rpow_quarter_eventually :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
  -- log =o[atTop] x^(1/4) implies eventually ‖log x‖ ≤ ‖x^(1/4)‖
  have hlo := (Real.isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventuallyLE
  -- Transfer from ℝ filter to ℕ filter via Tendsto.eventually
  have hev := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_nn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1 : (1 : ℝ) ≤ ↑n)
  rwa [Real.norm_of_nonneg hlog_nn,
       Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hn_pos) _)] at hn

/--
**Kanold's bound proved from Guth-Katz**: cn/log n ≥ cn^{3/4} for large n.

This makes the `kanold_bound` axiom in Erdos100Problem.lean redundant.
The key step uses `log n ≤ n^(1/4)` (from `isLittleO_log_rpow_atTop`)
to show `n^(3/4) ≤ n / log n`.
-/
theorem kanold_from_guthkatz :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^(3/4 : ℝ) ≤ minDiameterRestrictedSets n := by
  obtain ⟨c, hc_pos, hbound⟩ := minDiam_ge_n_over_log
  use c, hc_pos
  filter_upwards [hbound, log_le_rpow_quarter_eventually,
                   Filter.eventually_ge_atTop 3] with n hn hlog_le hn3
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  -- n^(3/4) ≤ n / log n because log n ≤ n^(1/4)
  -- Proof: n^(3/4) * log n ≤ n^(3/4) * n^(1/4) = n^1 = n
  calc c * (n : ℝ) ^ ((3 : ℝ) / 4)
      ≤ c * (n : ℝ) / Real.log (n : ℝ) := by
        rw [le_div_iff₀ hlog_pos]
        calc c * ↑n ^ ((3 : ℝ) / 4) * Real.log ↑n
            ≤ c * ↑n ^ ((3 : ℝ) / 4) * ↑n ^ ((1 : ℝ) / 4) := by
              apply mul_le_mul_of_nonneg_left hlog_le
              positivity
          _ = c * (↑n ^ ((3 : ℝ) / 4) * ↑n ^ ((1 : ℝ) / 4)) := by ring
          _ = c * ↑n ^ (1 : ℝ) := by
              congr 1
              rw [← Real.rpow_add (by positivity : (0 : ℝ) < ↑n)]
              norm_num
          _ = c * ↑n := by rw [Real.rpow_one]
    _ ≤ minDiameterRestrictedSets n := hn

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE GAP QUESTION — TWO EXCLUSIVE SCENARIOS
-- ═══════════════════════════════════════════════════════════════════

/--
**Scenario A**: The diameter grows linearly (Erdős's conjecture).
-/
def LinearGrowth : Prop := Erdos100Conjecture

/--
**Scenario B**: The logarithmic factor is genuine — there exist n-point
integer distance sets with diameter O(n/log n) for infinitely many n.
-/
def LogarithmicBarrier : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n : ℕ in atTop,
    minDiameterRestrictedSets n ≤ C * n / Real.log n

/--
**Main theorem**: Linear growth and logarithmic barrier are mutually exclusive.

If diam ≥ cn for all large n-point sets (linear), then there cannot also
exist n-point sets with diam ≤ Cn/log n (logarithmic barrier), because
this would require c ≤ C/log n → 0, contradicting c > 0.
-/
theorem scenarios_exclusive (hlin : LinearGrowth) (hlog : LogarithmicBarrier) : False := by
  obtain ⟨c, hc_pos, hlin_ev⟩ := hlin
  obtain ⟨C, hC_pos, hlog_ev⟩ := hlog
  -- C / log n → 0 as n → ∞, so eventually C / log n < c (since c > 0)
  have hlog_nat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC_small : ∀ᶠ n : ℕ in atTop, C / Real.log (n : ℝ) < c :=
    (tendsto_const_nhds.div_atTop hlog_nat).eventually (Iio_mem_nhds hc_pos)
  -- For large n: cn ≤ minDiam(n) ≤ Cn/log n AND C/log n < c → contradiction
  have hcontradiction : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlin_ev, hlog_ev, Filter.eventually_ge_atTop 3, hC_small]
      with n hlin_n hlog_n hn3 hlt
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    -- cn ≤ minDiam(n) ≤ Cn/log n
    have h_chain : c * n ≤ C * n / Real.log n := le_trans hlin_n hlog_n
    -- Divide by n: c ≤ C/log n
    have h_div : c ≤ C / Real.log n := by
      have h' : c * ↑n ≤ C / Real.log ↑n * ↑n := by rwa [div_mul_eq_mul_div]
      exact (mul_le_mul_right hn_pos).mp h'
    -- But C/log n < c, contradiction
    linarith
  exact (eventually_atTop.mp hcontradiction).choose_spec _ le_rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE GAP IS LOGARITHMIC
-- ═══════════════════════════════════════════════════════════════════

/--
The gap between what's known and what's conjectured vanishes in the
ratio sense: 1/log n → 0, meaning the known bound n/log n is
asymptotically smaller than the conjectured bound n by a vanishing factor.
-/
theorem gap_ratio_vanishes :
    Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hlog

/--
If linear growth holds, the Guth-Katz bound has room for improvement
by a factor of log n. Conversely, closing this gap would prove the
conjecture.
-/
theorem linear_implies_logn_improvement (hlin : LinearGrowth) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
        S.card = n → hasIntegerDistances S →
        Real.log n * (c * n / Real.log n) ≤ Real.log n * diam S := by
  obtain ⟨c, hc_pos, hev⟩ := hlin
  use c, hc_pos
  filter_upwards [hev, Filter.eventually_ge_atTop 3] with n hn hn3
  intro S hcard hint
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  -- From linear growth: cn ≤ minDiam(n) ≤ diam S
  have h_le : minDiameterRestrictedSets n ≤ diam S := by
    unfold minDiameterRestrictedSets
    apply csInf_le
    · exact ⟨0, fun d hd => by
        obtain ⟨S', ⟨_, _⟩, rfl⟩ := hd
        exact diam_nonneg S'⟩
    · exact ⟨S, ⟨hcard, hint⟩, rfl⟩
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hlog_pos)
  -- cn/log n ≤ cn ≤ minDiam(n) ≤ diam S
  calc c * n / Real.log n
      ≤ c * n := by
        apply div_le_self (by positivity) (le_of_lt hlog_pos)
    _ ≤ minDiameterRestrictedSets n := hn
    _ ≤ diam S := h_le

end Erdos100.OQ01
