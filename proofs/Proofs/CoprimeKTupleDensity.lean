/-
# Coprime k-Tuple Density = 1/ζ(k)

**Statement**: For every integer `k ≥ 2`, the natural density of coprime
`k`-tuples of positive integers equals `1/ζ(k)`:

  lim_{N→∞} |{a : Fin k → ℕ | 1 ≤ a i ≤ N, gcd(a₁,…,a_k) = 1}| / Nᵏ = 1/ζ(k)

This generalises the classical Cesàro result for pairs (`k = 2`, density `6/π² = 1/ζ(2)`,
formalised in `BaselProblemOQ04OQ03`) to arbitrary dimension. The probability that
`k` random integers share no common factor is `1/ζ(k) = ∏_p (1 − p⁻ᵏ)`.

## Proof Architecture

The proof follows the same three-step skeleton as the `k = 2` case, with the square
`⌊N/d⌋²` replaced by the `k`-th power `⌊N/d⌋ᵏ`.

### Step 1: Möbius Decomposition
Using Möbius inversion (`[n=1] = Σ_{d|n} μ(d)`), a finite Fubini exchange gives

  countCoprimeTuples k N = Σ_{d=1}^N μ(d) · ⌊N/d⌋ᵏ.

The `k`-tuple count of `d`-divisible tuples factors as `⌊N/d⌋ᵏ` (a product over the
`k` coordinates, `Fintype.card_piFinset_const`).

### Step 2: The Möbius Dirichlet Series (key identity)
For integer `k ≥ 2`,

  Σ_{d≥1} μ(d)/dᵏ = 1/ζ(k).

This is the central analytic fact. It generalises `Σ μ(d)/d² = 6/π²` and is proved from
the L-series identity `L(ζ, k)·L(μ, k) = 1` together with `ζ(k) = Σ 1/nᵏ`
(`zeta_nat_eq_tsum_of_gt_one`). No closed form for `ζ(k)` is needed; the value is carried
symbolically as the real number `rZeta k = Σ' n, 1/nᵏ`.

### Step 3: Density Limit
Tannery's dominated-convergence theorem with dominator `1/dᵏ` (summable for `k ≥ 2`,
`summable_one_div_nat_pow`) and pointwise limit `⌊N/d⌋/N → 1/d` upgrades the finite
Möbius sum to the infinite series, yielding the density `1/ζ(k)`.

## Axiom Count: 0

References:
- Nymann, "On the probability that `k` positive integers are relatively prime",
  J. Number Theory 4 (1972), 469–473.
- Hardy & Wright, *Theory of Numbers* §18.5 (the `k = 2` case).
- Mathlib: `LSeries_zeta_mul_Lseries_moebius`, `zeta_nat_eq_tsum_of_gt_one`,
  `tendsto_tsum_of_dominated_convergence`.
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

open Filter Finset BigOperators Real Nat ArithmeticFunction

open scoped LSeries.notation

-- Helper: (⌊N/d⌋ : ℝ) / N → 1/d as N → ∞ (for any fixed d).  [k-independent; identical to
-- the `k = 2` development in BaselProblemOQ04OQ03]
private lemma nat_div_div_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ => (N / d : ℕ) / (N : ℝ)) atTop (nhds (1 / (d : ℝ))) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Nat.div_zero]
  · have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨max 1 ⌈(d : ℝ) / ε⌉₊, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := (Nat.le_max_left 1 _).trans hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hd_ne : (d : ℝ) ≠ 0 := hd'.ne'
    have hN_ne : (N : ℝ) ≠ 0 := hN'.ne'
    have hdm : (N / d : ℕ) * d + N % d = N := by
      rw [Nat.mul_comm (N / d) d]; exact Nat.div_add_mod N d
    have hdmR : ((N / d : ℕ) : ℝ) * d + ((N % d : ℕ) : ℝ) = N := by exact_mod_cast hdm
    have heq : (N / d : ℕ) / (N : ℝ) - 1 / d
        = -(((N % d : ℕ) : ℝ) / ((d : ℝ) * N)) := by
      have h1 : ((N / d : ℕ) : ℝ) = ((N : ℝ) - (N % d : ℕ)) / d := by
        rw [eq_div_iff hd_ne]; linarith [hdmR]
      rw [h1]; field_simp; ring
    rw [Real.dist_eq, heq, abs_neg, abs_of_nonneg (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    have hmod : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N hd
    have hN_ge : (d : ℝ) ≤ ε * N := by
      have h1 : (d : ℝ) / ε ≤ ⌈(d : ℝ) / ε⌉₊ := Nat.le_ceil _
      have h2 : (⌈(d : ℝ) / ε⌉₊ : ℝ) ≤ N := by
        exact_mod_cast (Nat.le_max_right 1 _).trans hN
      calc (d : ℝ) = d / ε * ε := by field_simp
        _ ≤ ↑⌈↑d / ε⌉₊ * ε := by nlinarith
        _ ≤ N * ε := by nlinarith
        _ = ε * N := mul_comm _ _
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hkey : (0 : ℝ) ≤ ((d : ℝ) - 1) * (ε * N) :=
      mul_nonneg (by linarith) (le_of_lt (mul_pos hε hN'))
    nlinarith [hmod, hN_ge, h1d, hkey, mul_pos hε hN', mul_pos hd' hN']

namespace CoprimeKTupleDensity

-- ============================================================
-- SECTION I: The Real ζ(k) Value
-- ============================================================

/-- The real value `ζ(k) = Σ' n, 1/nᵏ`. For `k ≥ 2` this series converges and equals the
(real, positive) Riemann zeta value `riemannZeta k`. -/
noncomputable def rZeta (k : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ k

/-- For `k ≥ 2`, the defining series of `rZeta k` is summable. -/
lemma rZeta_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
  summable_one_div_nat_pow.mpr (by omega)

/-- `rZeta k > 0` (the `n = 1` term contributes `1`). -/
lemma rZeta_pos {k : ℕ} (hk : 2 ≤ k) : 0 < rZeta k := by
  refine (rZeta_summable hk).tsum_pos (fun n => by positivity) 1 ?_
  norm_num

/-- The bridge to the complex Riemann zeta function: for `k ≥ 2`,
`riemannZeta k = rZeta k` (as a complex number via `ofReal`). -/
lemma riemannZeta_nat_eq_ofReal_rZeta {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta (k : ℂ) = ((rZeta k : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < k), rZeta, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  push_cast
  ring

/-- `1 < rZeta k` for `k ≥ 2`: the first two terms `1 + 1/2ᵏ` already exceed `1`.
Hence the density `1/ζ(k)` lies strictly below `1`. -/
lemma one_lt_rZeta {k : ℕ} (hk : 2 ≤ k) : 1 < rZeta k := by
  have hsum := rZeta_summable hk
  -- The partial sum over `{1, 2}` is a lower bound for the (nonneg) series.
  have hle : ∑ n ∈ ({1, 2} : Finset ℕ), 1 / (n : ℝ) ^ k ≤ rZeta k :=
    sum_le_hasSum _ (fun i _ => by positivity) hsum.hasSum
  have hlb : (1 : ℝ) < ∑ n ∈ ({1, 2} : Finset ℕ), 1 / (n : ℝ) ^ k := by
    rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
    have e1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ k = 1 := by simp
    have e2 : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ) ^ k := by positivity
    rw [e1]; linarith
  linarith

-- ============================================================
-- SECTION II: Möbius Inversion Foundation  (k-independent)
-- ============================================================

/-- **Key Lemma** (Möbius Inversion): for `n ≥ 1`, `Σ_{d|n} μ(d) = [n = 1]`.
This is the Dirichlet convolution `μ * ζ = 1`. -/
theorem moebius_sum_divisors (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) =
      if n = 1 then 1 else 0 := by
  trans (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
         ↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ)) n)
  · rw [ArithmeticFunction.mul_apply]
    simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
    have h_simp : ∀ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * (↑(if x.2 = 0 then (0 : ℕ) else 1) : ℤ) =
        ArithmeticFunction.moebius x.1 := by
      intro x hx
      have hmem := Nat.mem_divisorsAntidiagonal.mp hx
      have hx2 : x.2 ≠ 0 := by
        intro h; exact hmem.2 (by rw [← hmem.1, h, mul_zero])
      simp [hx2]
    rw [Finset.sum_congr rfl h_simp]
    symm
    apply Finset.sum_nbij Prod.fst
    · intro x hx
      have hmem := Nat.mem_divisorsAntidiagonal.mp hx
      exact Nat.mem_divisors.mpr ⟨⟨x.2, hmem.1.symm⟩, hmem.2⟩
    · intro x₁ hx₁ x₂ hx₂ h
      have h1 := (Nat.mem_divisorsAntidiagonal.mp hx₁).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp hx₂).1
      have h2_ne := (Nat.mem_divisorsAntidiagonal.mp hx₂).2
      have h_ne : x₂.1 ≠ 0 := by
        intro hz; exact h2_ne (by rw [← h2, hz, zero_mul])
      have h_eq : x₁.1 * x₁.2 = x₂.1 * x₂.2 := h1.trans h2.symm
      ext
      · exact h
      · exact mul_left_cancel₀ h_ne (by rwa [h] at h_eq)
    · intro d hd
      exact ⟨(d, n / d), Nat.mem_divisorsAntidiagonal.mpr
        ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), hn.ne'⟩, rfl⟩
    · intro _ _; rfl
  · rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

-- ============================================================
-- SECTION III: Counting Multiples and Divisible Tuples
-- ============================================================

/-- The number of multiples of `d` in `{1, …, N}` equals `⌊N/d⌋`.  [k-independent] -/
theorem card_multiples (d N : ℕ) (hd : 0 < d) :
    (Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N)).card = N / d := by
  have h_eq : Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N) =
      (Finset.range (N / d)).image (fun j => (j + 1) * d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha1, haN⟩, ⟨k, rfl⟩⟩
      have hk_pos : 0 < k := by
        by_contra h; push_neg at h; interval_cases k; simp at ha1
      have hk_le : k ≤ N / d := by
        rw [Nat.le_div_iff_mul_le hd]
        calc k * d = d * k := mul_comm k d
          _ ≤ N := haN
      exact ⟨k - 1, by omega, by rw [Nat.sub_add_cancel (by omega : 1 ≤ k), mul_comm]⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_left d (j + 1)⟩
      · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hd.ne')
      · calc (j + 1) * d ≤ N / d * d := by nlinarith
          _ ≤ N := Nat.div_mul_le_self N d
  rw [h_eq]
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have := mul_right_cancel₀ hd.ne' h; omega)]
  exact Finset.card_range _

/-- The number of `k`-tuples `a : Fin k → ℕ` with each `a i ∈ {1, …, N}` and `d ∣ a i`
for all `i` equals `⌊N/d⌋ᵏ`. (The `k`-dimensional analogue of `card_pairs_divisible`.) -/
theorem card_tuples_divisible (k d N : ℕ) (hd : 0 < d) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
      (fun a => ∀ i, d ∣ a i)).card = (N / d) ^ k := by
  have h_eq : (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
        (fun a => ∀ i, d ∣ a i)
      = Fintype.piFinset (fun _ : Fin k => Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N)) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨ha, hdvd⟩ i; exact ⟨ha i, hdvd i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [h_eq, Fintype.card_piFinset_const, card_multiples d N hd]

-- ============================================================
-- SECTION IV: The Coprime Tuple Count and Möbius Decomposition
-- ============================================================

/-- The number of `k`-tuples `a : Fin k → ℕ` with `1 ≤ a i ≤ N` for all `i` and
`gcd(a₁, …, a_k) = 1`. -/
noncomputable def countCoprimeTuples (k N : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
    (fun a => Finset.univ.gcd a = 1)).card

/-- **Möbius Decomposition**: `countCoprimeTuples k N = Σ_{d=1}^N μ(d) · ⌊N/d⌋ᵏ`.

Both sides count triples `(a, d)` with `a ∈ [1,N]ᵏ` and `d | gcd(a)`, weighted by `μ(d)`.
A finite Fubini exchange swaps the order of summation. -/
theorem countCoprimeTuples_moebius (k N : ℕ) (hk1 : 0 < k) (hN : 0 < N) :
    (countCoprimeTuples k N : ℤ) =
    ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℤ) * (N / d : ℕ) ^ k := by
  unfold countCoprimeTuples
  -- Step 1: Cardinality = sum of coprimality indicators
  have h_card_sum :
      (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
        (fun a => Finset.univ.gcd a = 1)).card : ℤ) =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N),
        if Finset.univ.gcd a = 1 then (1 : ℤ) else 0 := by
    rw [← Finset.sum_boole]
  rw [h_card_sum]
  -- Step 2: Replace each indicator by `Σ_{e | gcd a} μ(e)` (Möbius inversion).
  have hgcd_pos : ∀ a ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N),
      0 < Finset.univ.gcd a := by
    intro a ha
    have ha0 := (Fintype.mem_piFinset.mp ha) ⟨0, hk1⟩
    rw [Finset.mem_Icc] at ha0
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Finset.gcd_eq_zero_iff]
    push_neg
    exact ⟨⟨0, hk1⟩, Finset.mem_univ _, by omega⟩
  have h_moebius : ∀ a ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N),
      (if Finset.univ.gcd a = 1 then (1 : ℤ) else 0) =
      ∑ e ∈ (Finset.univ.gcd a).divisors, (ArithmeticFunction.moebius e : ℤ) :=
    fun a ha => (moebius_sum_divisors _ (hgcd_pos a ha)).symm
  rw [Finset.sum_congr rfl h_moebius]
  -- Step 3: Inner divisor sum = sum over `e ∈ [1,N]` with `∀ i, e ∣ a i`.
  have h_step3 : ∀ a ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N),
      ∑ e ∈ (Finset.univ.gcd a).divisors, (ArithmeticFunction.moebius e : ℤ) =
      ∑ e ∈ Finset.Icc 1 N,
        if (∀ i, e ∣ a i) then (ArithmeticFunction.moebius e : ℤ) else 0 := by
    intro a ha
    rw [← Finset.sum_filter]
    congr 1
    ext e
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd_gcd, _⟩
      have hall : ∀ i, e ∣ a i := fun i => hdvd_gcd.trans (Finset.gcd_dvd (Finset.mem_univ i))
      have hi0 := hall ⟨0, hk1⟩
      have ha0 := (Fintype.mem_piFinset.mp ha) ⟨0, hk1⟩
      rw [Finset.mem_Icc] at ha0
      exact ⟨⟨Nat.pos_of_dvd_of_pos hi0 (by omega),
        le_trans (Nat.le_of_dvd (by omega) hi0) ha0.2⟩, hall⟩
    · rintro ⟨_, hall⟩
      exact ⟨Finset.dvd_gcd (fun i _ => hall i), (hgcd_pos a ha).ne'⟩
  rw [Finset.sum_congr rfl h_step3, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.mem_Icc] at he
  rw [← Finset.sum_filter, Finset.sum_const, card_tuples_divisible k e N (by omega)]
  simp only [nsmul_eq_mul]
  push_cast
  ring

-- ============================================================
-- SECTION V: The Möbius Dirichlet Series  Σ μ(d)/dᵏ = 1/ζ(k)
-- ============================================================

/-- **Theorem (Möbius Dirichlet Series)**: for integer `k ≥ 2`,

  Σ_{d≥1} μ(d)/dᵏ = 1/ζ(k).

This is the key analytic identity. Generalises `moebius_dirichlet_series_at_two`
(`Σ μ(d)/d² = 6/π²`). Proof: at `s = k` the L-series identity `L(ζ, k)·L(μ, k) = 1`
combined with `L(ζ, k) = ζ(k)` gives `L(μ, k) = 1/ζ(k)`; transfer to a real `HasSum`. -/
theorem moebius_dirichlet_series {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ k)
    (1 / rZeta k) := by
  rw [← Complex.hasSum_ofReal]
  have hval : ((1 / rZeta k : ℝ) : ℂ) = (rZeta k : ℂ)⁻¹ := by
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div]
  rw [hval]
  have hkre : 1 < ((k : ℕ) : ℂ).re := by
    rw [Complex.natCast_re]; exact_mod_cast (show 1 < k by omega)
  have hmu_sum : LSeriesSummable ↗moebius (k : ℂ) :=
    LSeriesSummable_moebius_iff.mpr hkre
  have hprod : L ↗zeta (k : ℂ) * L ↗moebius (k : ℂ) = 1 :=
    LSeries_zeta_mul_Lseries_moebius hkre
  have hzeta : L ↗zeta (k : ℂ) = (rZeta k : ℂ) := by
    rw [LSeries_zeta_eq_riemannZeta hkre, riemannZeta_nat_eq_ofReal_rZeta hk]
  have hz_ne : (rZeta k : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (rZeta_pos hk).ne'
  have hL_mu : L ↗moebius (k : ℂ) = (rZeta k : ℂ)⁻¹ := by
    have h : (rZeta k : ℂ) * L ↗moebius (k : ℂ) = 1 := hzeta ▸ hprod
    calc L ↗moebius (k : ℂ)
        = (rZeta k : ℂ)⁻¹ * ((rZeta k : ℂ) * L ↗moebius (k : ℂ)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hz_ne, one_mul]
      _ = (rZeta k : ℂ)⁻¹ * 1 := by rw [h]
      _ = (rZeta k : ℂ)⁻¹ := mul_one _
  have hLHS : LSeriesHasSum ↗moebius (k : ℂ) ((rZeta k : ℂ)⁻¹) :=
    hL_mu ▸ hmu_sum.LSeriesHasSum
  have hfun : LSeries.term ↗moebius (k : ℂ) =
      fun n : ℕ => (((moebius n : ℝ) / (n : ℝ) ^ k : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_natCast]
      push_cast
      ring
  rwa [← hfun]

/-- The Möbius Dirichlet series as a `tsum`: `Σ' d, μ(d)/dᵏ = 1/ζ(k)`. -/
theorem tsum_moebius_div_pow {k : ℕ} (hk : 2 ≤ k) :
    ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ k = 1 / rZeta k :=
  (moebius_dirichlet_series hk).tsum_eq

-- ============================================================
-- SECTION VI: The Density Limit
-- ============================================================

/-- **Main Theorem** (Nymann 1972): for every integer `k ≥ 2`, the natural density of
coprime `k`-tuples of positive integers equals `1/ζ(k)`:

  lim_{N→∞} countCoprimeTuples k N / Nᵏ = 1/ζ(k).

Proof via Tannery's dominated-convergence theorem: the Möbius decomposition rewrites the
count as `Σ_d μ(d)·(⌊N/d⌋/N)ᵏ`, each term tends to `μ(d)/dᵏ`, the family is dominated by
the summable `1/dᵏ`, and the limit series sums to `1/ζ(k)` (`moebius_dirichlet_series`). -/
theorem coprime_tuple_density_limit {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto
      (fun N : ℕ => (countCoprimeTuples k N : ℝ) / (N : ℝ) ^ k)
      Filter.atTop
      (nhds (1 / rZeta k)) := by
  rw [show (1 / rZeta k) = ∑' d : ℕ, (moebius d : ℝ) / (d : ℝ) ^ k
    from (tsum_moebius_div_pow hk).symm]
  have h_congr : ∀ᶠ N : ℕ in atTop,
      (countCoprimeTuples k N : ℝ) / N ^ k =
      ∑' d : ℕ, (moebius d : ℝ) * ((N / d : ℕ) / (N : ℝ)) ^ k := by
    apply eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hN2 : (N : ℝ) ^ k ≠ 0 := pow_ne_zero k hN'.ne'
    have hdecomp := countCoprimeTuples_moebius k N (by omega) (by omega)
    have hcast : (countCoprimeTuples k N : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) * ((N / d : ℕ) : ℝ) ^ k := by
      have h := congr_arg (Int.cast : ℤ → ℝ) hdecomp
      push_cast at h
      exact h
    have h_fin_eq : ∑' d : ℕ, (moebius d : ℝ) * ((N / d : ℕ) / (N : ℝ)) ^ k =
        ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) * ((N / d : ℕ) / (N : ℝ)) ^ k := by
      apply tsum_eq_sum
      intro d hd
      simp only [Finset.mem_Icc, not_and_or, not_le] at hd
      rcases hd with hd0 | hdN
      · have : d = 0 := by omega
        subst this; simp
      · have hzero : N / d = 0 := Nat.div_eq_of_lt (by omega)
        rw [hzero]; simp [zero_pow (show k ≠ 0 by omega)]
    rw [h_fin_eq, hcast, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_div_assoc, ← div_pow]
  apply (tendsto_tsum_of_dominated_convergence
    (f := fun N d => (moebius d : ℝ) * ((N / d : ℕ) / (N : ℝ)) ^ k)
    (g := fun d => (moebius d : ℝ) / (d : ℝ) ^ k)
    (bound := fun d => 1 / (d : ℝ) ^ k)
    (h_sum := summable_one_div_nat_pow.mpr (by omega : 1 < k))
    (hab := fun d => by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have hμ0 : (moebius 0 : ℝ) = 0 := by simp
        simp only [hμ0, zero_mul, zero_div]
        exact tendsto_const_nhds
      · have h := (nat_div_div_tendsto d).pow k
        have hc : Tendsto (fun _ : ℕ => (moebius d : ℝ)) atTop (nhds (moebius d : ℝ)) :=
          tendsto_const_nhds
        have h2 := hc.mul h
        rwa [show (moebius d : ℝ) * (1 / (d : ℝ)) ^ k = (moebius d : ℝ) / (d : ℝ) ^ k
          from by rw [div_pow, one_pow, mul_one_div]] at h2)
    (h_bound := by
      filter_upwards [eventually_ge_atTop 1] with N hN d
      have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have hμ0 : (moebius 0 : ℝ) = 0 := by simp
        rw [hμ0, zero_mul, norm_zero]
        exact div_nonneg (by norm_num) (by positivity)
      · simp only [Real.norm_eq_abs, abs_mul, abs_pow]
        have hmu : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have hdiv : |(N / d : ℕ) / (N : ℝ)| ≤ 1 / (d : ℝ) := by
          rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hN' (Nat.cast_pos.mpr hd)]
          simp only [one_mul]
          push_cast
          exact_mod_cast Nat.div_mul_le_self N d
        calc |(moebius d : ℝ)| * |(N / d : ℕ) / (N : ℝ)| ^ k
            ≤ 1 * (1 / (d : ℝ)) ^ k :=
              mul_le_mul hmu (pow_le_pow_left₀ (abs_nonneg _) hdiv k)
                (pow_nonneg (abs_nonneg _) k) (by norm_num)
          _ = 1 / (d : ℝ) ^ k := by rw [one_mul, div_pow, one_pow])).congr'
    (Filter.EventuallyEq.symm h_congr)

-- ============================================================
-- SECTION VII: Consequences
-- ============================================================

/-- The density `1/ζ(k)` is strictly positive. -/
theorem density_pos {k : ℕ} (hk : 2 ≤ k) : 0 < 1 / rZeta k :=
  div_pos one_pos (rZeta_pos hk)

/-- The density `1/ζ(k)` is strictly less than `1` (since `ζ(k) > 1`).
So coprimality of `k`-tuples is a genuine, non-degenerate event. -/
theorem density_lt_one {k : ℕ} (hk : 2 ≤ k) : 1 / rZeta k < 1 := by
  rw [div_lt_one (rZeta_pos hk)]
  exact one_lt_rZeta hk

/-- The density lies in the open unit interval `(0, 1)` — a bona fide probability. -/
theorem density_in_unit_interval {k : ℕ} (hk : 2 ≤ k) :
    1 / rZeta k ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨density_pos hk, density_lt_one hk⟩

-- ============================================================
-- SECTION VIII: Consistency with the Pair Case (k = 2)
-- ============================================================

/-- Cross-check: `ζ(2) = π²/6`, recovering the Basel constant. -/
theorem rZeta_two_eq : rZeta 2 = Real.pi ^ 2 / 6 := by
  have h := riemannZeta_nat_eq_ofReal_rZeta (k := 2) (by norm_num)
  rw [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num, riemannZeta_two] at h
  have hc : ((rZeta 2 : ℝ) : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    rw [← h]; push_cast; ring
  exact_mod_cast hc

/-- Cross-check: the `k = 2` density is `6/π²`, matching `coprime_pair_density`
(`BaselProblemOQ04OQ03`). -/
theorem density_two_eq : 1 / rZeta 2 = 6 / Real.pi ^ 2 := by
  rw [rZeta_two_eq, one_div_div]

-- ============================================================
-- SECTION IX: Summary
-- ============================================================

/-
## Summary

**Theorem (Nymann 1972)**: for every integer `k ≥ 2`,
  lim_{N→∞} |{a ∈ [1,N]ᵏ : gcd(a) = 1}| / Nᵏ = 1/ζ(k).

**Proof Architecture** (faithful `k`-dimensional generalisation of the `k = 2` Basel
development in `BaselProblemOQ04OQ03`):
1. Möbius decomposition: `countCoprimeTuples k N = Σ_{d≤N} μ(d)·⌊N/d⌋ᵏ`
   (`countCoprimeTuples_moebius`), via `Fintype.card_piFinset_const`.
2. Dirichlet series: `Σ_{d≥1} μ(d)/dᵏ = 1/ζ(k)` (`moebius_dirichlet_series`),
   via `LSeries_zeta_mul_Lseries_moebius` + `zeta_nat_eq_tsum_of_gt_one`.
3. Density limit: `coprime_tuple_density_limit`, via Tannery's theorem with dominator
   `1/dᵏ` (`summable_one_div_nat_pow`, valid for `k ≥ 2`).

**Specialisation** `k = 2` recovers `6/π² = 1/ζ(2)` (`density_two_eq`).

Axiom count: 0.  Sorry count: 0.
-/

end CoprimeKTupleDensity
