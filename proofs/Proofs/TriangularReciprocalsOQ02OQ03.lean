/-
# Alternating gap-k reciprocal series: closed form via the alternating harmonic sibling

For an integer gap `k ≥ 1` we evaluate the alternating series

    ∑_{n≥1} (-1)^{n+1} / (n (n+k))

in closed form.  The terms are dominated by `1/n²`, so the series is absolutely
convergent and legitimately `HasSum`-able (unlike the *conditionally* convergent
alternating harmonic series itself, which is **not** `HasSum` in Mathlib's
unconditional sense).  Partial-fraction the *finite* partial sums

    1/(n(n+k)) = (1/k)(1/n − 1/(n+k)),

reindex the shifted piece `n ↦ n+k`, and pass to the limit.  Only one classical
analytic fact enters: the alternating harmonic partial sums converge to `log 2`.

Main result (`hasSum_alternating_gap_k`):

    ∑_{n≥1} (-1)^{n+1} / (n(n+k))
      = (1/k) · ( (1 − (−1)^k)·log 2  +  (−1)^k · A_k ),

where `A_k = ∑_{m=1}^{k} (−1)^{m+1}/m` is the `k`-th alternating harmonic partial
sum.  Equivalently

  * `k` even :  ∑ = A_k / k
  * `k` odd  :  ∑ = (2·log 2 − A_k) / k

Special cases (checked against the sibling `TriangularReciprocalAlternatingOQ03`):
  * `k = 1`:  ∑ (-1)^{n+1}/(n(n+1)) = 2·log 2 − 1
  * `k = 2`:  ∑ (-1)^{n+1}/(n(n+2)) = 1/4

The `log 2` limit is proved here **without axioms**: the alternating series test
gives convergence, and Abel's limit theorem
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) identifies the limit with the
`x → 1⁻` boundary value of the Mercator series for `log(1+x)`.  This mirrors
Mathlib's `Real.tendsto_sum_pi_div_four` (Leibniz's series for π) and upgrades the
sibling entry, which took the boundary value as an (unsound-as-`HasSum`) axiom.
-/
import Mathlib

namespace AlternatingGapKReciprocals

open Finset Filter Topology Real

/-- The `N`-th alternating harmonic partial sum, `1 − 1/2 + 1/3 − ⋯ ± 1/N`,
written in range form `∑_{i<N} (-1)^i/(i+1)`. -/
noncomputable def altH (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / ((i : ℝ) + 1)

-- ═══════════════════════════════════════════════════════════════════
-- Part I: the classical analytic input — alternating harmonic → log 2
-- ═══════════════════════════════════════════════════════════════════

/-- **Alternating harmonic series.** The partial sums `∑_{i<N} (-1)^i/(i+1)`
converge to `log 2`.  Proof: the alternating series test provides convergence to
*some* limit `l`; Abel's limit theorem identifies `l` with the left-hand boundary
value of the Mercator power series `∑ (-1)^n x^n/(n+1) = log(1+x)/x`, which tends
to `log 2` as `x → 1⁻`. -/
theorem tendsto_altH : Tendsto altH atTop (𝓝 (Real.log 2)) := by
  show Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 (Real.log 2))
  -- Convergence to some limit `l` via the alternating series test.
  obtain ⟨l, hl⟩ :
      ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + 1)))
        atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · intro a b hab
      apply one_div_le_one_div_of_le (by positivity)
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Rewrite into `(-1)^i/(i+1)` form.
  have hl' : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 l) := by
    refine hl.congr (fun n => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_one_div]
  -- Abel's limit theorem.
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl'
  -- The same tsum tends to `log 2`, since it equals `log(1+x)/x` near `1⁻`.
  have key :
      Tendsto (fun x : ℝ ↦ ∑' (n : ℕ), ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n)
        (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2)) := by
    -- Pointwise identification for `0 < x < 1`.
    have valLog : ∀ x : ℝ, 0 < x → |x| < 1 →
        (∑' (n : ℕ), ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n) = Real.log (1 + x) / x := by
      intro x hx0 hxlt
      have hxne : x ≠ 0 := ne_of_gt hx0
      have base := Real.hasSum_pow_div_log_of_abs_lt_one
        (x := -x) (by rwa [abs_neg])
      have HS1 : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (n + 1) / ((n : ℝ) + 1))
          (Real.log (1 + x)) := by
        have hb := base.mul_left (-1)
        have hval : (-1 : ℝ) * (-Real.log (1 - -x)) = Real.log (1 + x) := by
          rw [sub_neg_eq_add]; ring
        rw [hval] at hb
        have hfun : (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (n + 1) / ((n : ℝ) + 1))
            = (fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1))) := by
          funext n
          rw [neg_pow]
          ring
        rw [hfun]; exact hb
      have hxT : x * (∑' (n : ℕ), ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n)
          = Real.log (1 + x) := by
        rw [← HS1.tsum_eq, ← tsum_mul_left]
        refine tsum_congr (fun n => ?_)
        rw [pow_succ]; ring
      rw [eq_div_iff hxne, mul_comm]; exact hxT
    -- `log(1+x)/x → log 2` as `x → 1⁻`, by continuity at `1`.
    have hcont : Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2)) := by
      have hca : ContinuousAt (fun x : ℝ => Real.log (1 + x) / x) 1 := by
        apply ContinuousAt.div
        · have h1 : ContinuousAt (fun x : ℝ => (1 : ℝ) + x) 1 := by fun_prop
          have h2 : ContinuousAt Real.log (1 + 1 : ℝ) := Real.continuousAt_log (by norm_num)
          exact h2.comp h1
        · fun_prop
        · norm_num
      have htend := hca.tendsto
      have hfe : Real.log (1 + 1) / 1 = Real.log 2 := by norm_num
      rw [hfe] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    -- Combine: `log(1+x)/x =ᶠ T` near `1⁻`, so `T` tends to `log 2`.
    have heq : (fun x : ℝ => Real.log (1 + x) / x)
        =ᶠ[𝓝[<] (1 : ℝ)] (fun x : ℝ ↦ ∑' (n : ℕ), ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n) := by
      have hlt : ∀ᶠ x in 𝓝[<] (1 : ℝ), x < 1 := by
        filter_upwards [self_mem_nhdsWithin] with x hx using hx
      have hpos : ∀ᶠ x in 𝓝[<] (1 : ℝ), (0 : ℝ) < x := by
        have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
        filter_upwards [hmem] with x hx using hx
      filter_upwards [hlt, hpos] with x hx1 hx0
      have hxlt : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
      exact (valLog x hx0 hxlt).symm
    exact Tendsto.congr' heq hcont
  have hleq : l = Real.log 2 := tendsto_nhds_unique abel key
  rwa [hleq] at hl'

/-- Shifted alternating harmonic partial sums `altH (N+k)` also converge to `log 2`. -/
theorem tendsto_altH_shift (k : ℕ) :
    Tendsto (fun N => altH (N + k)) atTop (𝓝 (Real.log 2)) :=
  tendsto_altH.comp (tendsto_add_atTop_nat k)

-- ═══════════════════════════════════════════════════════════════════
-- Part II: finite algebra — partial fractions and reindexing
-- ═══════════════════════════════════════════════════════════════════

/-- Partial fraction decomposition `1/(n(n+k)) = (1/k)(1/n − 1/(n+k))`. -/
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / ↑k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + ↑k)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (↑k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℝ) + ↑k ≠ 0 := by positivity
  field_simp
  ring

/-- The 1-based alternating harmonic partial sum equals `altH`. -/
theorem altH_Icc_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (n + 1) / (n : ℝ) = altH N := by
  induction N with
  | zero => simp [altH]
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      simp only [altH, Finset.sum_range_succ]
      have hsign : (-1 : ℝ) ^ (M + 1 + 1) = (-1 : ℝ) ^ M := by
        rw [pow_succ, pow_succ]; ring
      rw [hsign]
      push_cast
      ring

/-- Reindexing the shifted sum `∑_{n=1}^N (-1)^{n+1}/(n+k)` by `m = n+k`. -/
theorem shifted_sum_eq (N k : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + ↑k) =
      (-1 : ℝ) ^ k * (altH (N + k) - altH k) := by
  induction N with
  | zero => simp [altH]
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hstep : altH (M + 1 + k)
          = altH (M + k) + (-1 : ℝ) ^ (M + k) / (((M : ℝ) + k) + 1) := by
        have hEq : M + 1 + k = (M + k) + 1 := by omega
        rw [hEq]
        simp only [altH, Finset.sum_range_succ]
        push_cast
        ring
      rw [hstep]
      have hsign : (-1 : ℝ) ^ (M + 1 + 1) = (-1 : ℝ) ^ k * (-1 : ℝ) ^ (M + k) := by
        rw [← pow_add]
        rw [show M + 1 + 1 = M + 2 from rfl, show k + (M + k) = M + 2 * k from by ring]
        rw [pow_add, pow_add, pow_mul]
        norm_num
      rw [hsign]
      push_cast
      ring

-- ═══════════════════════════════════════════════════════════════════
-- Part III: the main HasSum
-- ═══════════════════════════════════════════════════════════════════

/-- **Closed form for the alternating gap-`k` reciprocal series.**  For `k ≥ 1`,

    ∑_{n≥1} (-1)^{n+1} / (n(n+k))
      = (1/k) · ( (1 − (−1)^k)·log 2  +  (−1)^k · A_k ),

with `A_k = altH k = ∑_{m=1}^k (−1)^{m+1}/m`. -/
theorem hasSum_alternating_gap_k {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k)))
      ((1 / (k : ℝ)) * ((1 - (-1) ^ k) * Real.log 2 + (-1) ^ k * altH k)) := by
  have hk0 : k ≠ 0 := by omega
  set g : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k)) with hg
  -- (1) Summability by comparison with the p = 2 series.
  have hbound : ∀ n, ‖g n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hg]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + ↑k) := by positivity
      have hle : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + ↑k) := by nlinarith [hnR, hkR]
      have hnorm : ‖g n‖ = 1 / ((n : ℝ) * ((n : ℝ) + ↑k)) := by
        simp only [hg, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow]
        rw [abs_of_pos hden]
      rw [hnorm]
      exact one_div_le_one_div_of_le (by positivity) hle
  have hsummable : Summable g :=
    Summable.of_norm_bounded (g := fun n => 1 / (n : ℝ) ^ 2)
      (summable_one_div_nat_pow.mpr (by norm_num)) hbound
  -- (2) Partial-sum closed form over `Icc 1 N`.
  have hPS : ∀ N, ∑ n ∈ Finset.Icc 1 N, g n
      = (1 / (k : ℝ)) * (altH N - (-1) ^ k * (altH (N + k) - altH k)) := by
    intro N
    have step1 : ∑ n ∈ Finset.Icc 1 N, g n
        = ∑ n ∈ Finset.Icc 1 N,
            ((1 / (k : ℝ)) * ((-1 : ℝ) ^ (n + 1) / (n : ℝ))
              - (1 / (k : ℝ)) * ((-1 : ℝ) ^ (n + 1) / ((n : ℝ) + ↑k))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn1 : n ≠ 0 := by
        rcases Finset.mem_Icc.mp hn with ⟨h, _⟩; omega
      have hpf := partial_fraction (n := n) (k := k) hn1 hk0
      simp only [hg]
      have hrw : (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k))
          = (-1 : ℝ) ^ (n + 1) * (1 / ((n : ℝ) * ((n : ℝ) + ↑k))) := by
        rw [mul_one_div]
      rw [hrw, hpf]
      ring
    rw [step1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      altH_Icc_eq N, shifted_sum_eq N k]
    ring
  -- (3) Relate range partial sums to the `Icc` partial sums (drop the zero term).
  have hEq_range : ∀ N, ∑ n ∈ Finset.range (N + 1), g n = ∑ n ∈ Finset.Icc 1 N, g n := by
    intro N
    induction N with
    | zero => simp [hg]
    | succ M ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
  -- Limit of the closed form.
  have hlim :
      Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, g n) atTop
        (𝓝 ((1 / (k : ℝ)) * (Real.log 2 - (-1) ^ k * (Real.log 2 - altH k)))) := by
    have hbase :
        Tendsto (fun N => (1 / (k : ℝ)) * (altH N - (-1) ^ k * (altH (N + k) - altH k)))
          atTop (𝓝 ((1 / (k : ℝ)) * (Real.log 2 - (-1) ^ k * (Real.log 2 - altH k)))) := by
      refine Tendsto.const_mul _ ?_
      refine Tendsto.sub tendsto_altH ?_
      refine Tendsto.const_mul _ ?_
      exact (tendsto_altH_shift k).sub_const (altH k)
    exact hbase.congr (fun N => (hPS N).symm)
  -- Limit of the actual partial sums (to the tsum).
  have hrange : Tendsto (fun M => ∑ n ∈ Finset.range M, g n) atTop (𝓝 (∑' n, g n)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hrange' : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, g n) atTop (𝓝 (∑' n, g n)) := by
    have hcomp := hrange.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, hEq_range] using hcomp
  -- Identify the sum value and rewrite into the presented closed form.
  have hval : (∑' n, g n)
      = (1 / (k : ℝ)) * (Real.log 2 - (-1) ^ k * (Real.log 2 - altH k)) :=
    tendsto_nhds_unique hrange' hlim
  have hclosed :
      (1 / (k : ℝ)) * (Real.log 2 - (-1) ^ k * (Real.log 2 - altH k))
        = (1 / (k : ℝ)) * ((1 - (-1) ^ k) * Real.log 2 + (-1) ^ k * altH k) := by
    ring
  have hfin : HasSum g (∑' n, g n) := hsummable.hasSum
  rw [hval, hclosed] at hfin
  exact hfin

-- ═══════════════════════════════════════════════════════════════════
-- Part IV: special cases
-- ═══════════════════════════════════════════════════════════════════

/-- `k = 1`: `∑ (-1)^{n+1}/(n(n+1)) = 2·log 2 − 1`
(matches the sibling `alternating_reciprocal_product_sum`). -/
theorem hasSum_gap_one :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)))
      (2 * Real.log 2 - 1) := by
  have h := hasSum_alternating_gap_k (k := 1) (le_refl 1)
  have e : (1 / ((1 : ℕ) : ℝ)) * ((1 - (-1) ^ (1 : ℕ)) * Real.log 2 + (-1) ^ (1 : ℕ) * altH 1)
      = 2 * Real.log 2 - 1 := by
    have ha : altH 1 = 1 := by simp [altH]
    rw [ha]; push_cast; ring
  rw [e] at h
  simpa using h

/-- `k = 2`: `∑ (-1)^{n+1}/(n(n+2)) = 1/4`. -/
theorem hasSum_gap_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 2)))
      (1 / 4) := by
  have h := hasSum_alternating_gap_k (k := 2) (by norm_num)
  have e : (1 / ((2 : ℕ) : ℝ)) * ((1 - (-1) ^ (2 : ℕ)) * Real.log 2 + (-1) ^ (2 : ℕ) * altH 2)
      = 1 / 4 := by
    have ha : altH 2 = 1 / 2 := by
      simp [altH, Finset.sum_range_succ]
      norm_num
    rw [ha]; push_cast; ring
  rw [e] at h
  simpa using h

end AlternatingGapKReciprocals
