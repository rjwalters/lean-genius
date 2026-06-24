/-
# Frobenius's Theorem: Cesàro summability implies Abel summability

This file formalizes **Frobenius's theorem** (the general form):

> If the partial sums `sₙ = ∑_{k≤n} aₖ` of a real series are **Cesàro summable** to `L`
> (i.e. their averages `τₙ = (s₀+⋯+sₙ)/(n+1) → L`), then the series is **Abel summable**
> to the same value `L`, i.e. `lim_{x→1⁻} ∑ₙ aₙ xⁿ = L`.

This strictly generalizes Abel's theorem (`tendsto_tsum_powerSeries_nhdsWithin_lt` in Mathlib),
whose hypothesis is the *convergence* of `∑ aₙ`. Grandi's series `1 − 1 + 1 − ⋯` is the
canonical witness: it is Cesàro summable to `1/2` and Abel summable to `1/2`, yet **not**
convergent — so Mathlib's Abel theorem does not apply, but Frobenius's does.

## Proof strategy (double Abel summation)

Write `Sₙ = ∑_{k≤n} aₖ` (first partial sums) and `Tₙ = ∑_{k≤n} Sₖ` (second partial sums),
so `Tₙ = (n+1)·τₙ`. For `|x| < 1` two telescoping (Abel-summation) steps give
`∑ aₙ xⁿ = (1−x)·∑ Sₙ xⁿ = (1−x)²·∑ Tₙ xⁿ`, while `(1−x)²·∑ (n+1) xⁿ = 1`. Hence
`∑ aₙ xⁿ − L = (1−x)²·∑ (n+1)(τₙ − L) xⁿ`, and a standard `ε`-split (using `τₙ → L`)
shows the right side `→ 0` as `x → 1⁻`.

Open question of `geometric-series-oq-01-oq-01` (Grandi/Abel), which proved the *concrete*
`x → 1⁻` boundary value `1/2` for Grandi's series.
-/
import Mathlib

namespace FrobeniusCesaroAbel

open Filter Topology Finset

/-- First partial sums `Sₙ = ∑_{k≤n} aₖ`. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k

/-- Second partial sums `Tₙ = ∑_{k≤n} Sₖ`. -/
def partialSum2 (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), partialSum a k

/-- `partialSum2 a n = (n+1)·τₙ` where `τₙ` is the Cesàro mean of the partial sums. -/
theorem partialSum2_eq_cesaro (a : ℕ → ℝ) (n : ℕ) :
    partialSum2 a n = ((n : ℝ) + 1) * (partialSum2 a n / ((n : ℝ) + 1)) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- **Normalization.** For `|x| < 1`, `∑ₙ (n+1) xⁿ = 1/(1−x)²`. This identifies the
constant `L` with `(1−x)²·∑ (n+1) L xⁿ` in the main estimate. -/
theorem tsum_succ_mul_geometric {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * x ^ n = 1 / (1 - x) ^ 2 := by
  have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have hx1 : x ≠ 1 := by
    intro h; rw [h] at hx; simp at hx
  have h1mx : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (fun h => hx1 h.symm)
  -- ∑ n·xⁿ = x/(1-x)²  and  ∑ xⁿ = 1/(1-x)
  have hco : (∑' n : ℕ, (n : ℝ) * x ^ n) = x / (1 - x) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hge : (∑' n : ℕ, x ^ n) = (1 - x)⁻¹ := tsum_geometric_of_norm_lt_one hnorm
  have hsum_co : Summable (fun n : ℕ => (n : ℝ) * x ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hsum_ge : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_norm_lt_one hnorm
  calc ∑' n : ℕ, ((n : ℝ) + 1) * x ^ n
      = ∑' n : ℕ, ((n : ℝ) * x ^ n + x ^ n) := by
        congr 1; ext n; ring
    _ = (∑' n : ℕ, (n : ℝ) * x ^ n) + ∑' n : ℕ, x ^ n := by
        rw [hsum_co.tsum_add hsum_ge]
    _ = x / (1 - x) ^ 2 + (1 - x)⁻¹ := by rw [hco, hge]
    _ = 1 / (1 - x) ^ 2 := by
        field_simp
        ring

/-- **Abel summation (telescoping).** For `|x| < 1`, if the weighted partial-sum series is
summable then `∑ₙ bₙ xⁿ = (1−x)·∑ₙ (∑_{k≤n} bₖ) xⁿ`. Applying this with `b = a` and then
with `b = partialSum a` yields the double-summation identity. -/
theorem tsum_eq_one_sub_mul_tsum_partialSum (b : ℕ → ℝ) {x : ℝ} (hx : |x| < 1)
    (hs : Summable (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), b k) * x ^ n)) :
    ∑' n : ℕ, b n * x ^ n
      = (1 - x) * ∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), b k) * x ^ n := by
  sorry

/-- The same summability for the *second* partial sums `Tₙ`. Proved unconditionally from the
Cesàro hypothesis: the means `τₙ = Tₙ/(n+1)` form a bounded sequence (they converge), so
`Tₙ = (n+1)·τₙ = O(n)`, and `∑ n·|x|ⁿ` converges for `|x| < 1`. -/
theorem summable_partialSum2_mul_geometric (a : ℕ → ℝ) {L x : ℝ} (hx : |x| < 1)
    (hL : Tendsto (fun N : ℕ => partialSum2 a N / ((N : ℝ) + 1)) atTop (𝓝 L)) :
    Summable (fun n : ℕ => partialSum2 a n * x ^ n) := by
  -- The Cesàro means form a bounded sequence since they converge.
  obtain ⟨U, hU⟩ := hL.bddAbove_range
  obtain ⟨V, hV⟩ := hL.bddBelow_range
  set τ : ℕ → ℝ := fun N => partialSum2 a N / ((N : ℝ) + 1) with hτ
  have hM : ∀ n, |τ n| ≤ |U| + |V| := by
    intro n
    have h1 : τ n ≤ U := hU (Set.mem_range_self n)
    have h2 : V ≤ τ n := hV (Set.mem_range_self n)
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [neg_abs_le V, abs_nonneg U]
    · linarith [le_abs_self U, abs_nonneg V]
  have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have hxabs : ‖|x|‖ < 1 := by rwa [Real.norm_eq_abs, abs_abs]
  -- The dominating series `(|U|+|V|)·(n+1)·|x|ⁿ` is summable.
  have hgsum : Summable (fun n : ℕ => (|U| + |V|) * (((n : ℝ) + 1) * |x| ^ n)) := by
    apply Summable.mul_left
    have h1 : Summable (fun n : ℕ => (n : ℝ) * |x| ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxabs
    have h2 : Summable (fun n : ℕ => |x| ^ n) := summable_geometric_of_norm_lt_one hxabs
    refine (h1.add h2).congr (fun n => by ring)
  refine Summable.of_norm_bounded hgsum (fun n => ?_)
  have hTn : partialSum2 a n = ((n : ℝ) + 1) * τ n := by
    rw [hτ]; exact partialSum2_eq_cesaro a n
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, hTn, abs_mul, abs_of_nonneg hnn]
  calc ((n : ℝ) + 1) * |τ n| * |x| ^ n
      ≤ ((n : ℝ) + 1) * (|U| + |V|) * |x| ^ n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hM n) hnn
    _ = (|U| + |V|) * (((n : ℝ) + 1) * |x| ^ n) := by ring

/-- **Growth bound ⇒ summability.** A Cesàro-convergent sequence of partial sums is bounded
in average, so `Tₙ = O(n)`; the first partial sums satisfy `Sₙ₊₁ = Tₙ₊₁ − Tₙ`, hence the
weighted series `∑ Sₙ xⁿ` is the difference of two summable shifts of `∑ Tₙ xⁿ`. -/
theorem summable_partialSum_mul_geometric (a : ℕ → ℝ) {L x : ℝ} (hx : |x| < 1)
    (hL : Tendsto (fun N : ℕ => partialSum2 a N / ((N : ℝ) + 1)) atTop (𝓝 L)) :
    Summable (fun n : ℕ => partialSum a n * x ^ n) := by
  -- The second partial sums are summable against the geometric weight.
  have hT : Summable (fun n : ℕ => partialSum2 a n * x ^ n) :=
    summable_partialSum2_mul_geometric a hx hL
  -- `Sₙ₊₁ = Tₙ₊₁ − Tₙ`, so `Sₙ₊₁ xⁿ⁺¹ = Tₙ₊₁ xⁿ⁺¹ − x·(Tₙ xⁿ)`.
  have key : ∀ n : ℕ, partialSum a (n + 1) * x ^ (n + 1)
      = partialSum2 a (n + 1) * x ^ (n + 1) - x * (partialSum2 a n * x ^ n) := by
    intro n
    have hrec : partialSum2 a (n + 1) = partialSum2 a n + partialSum a (n + 1) := by
      simp [partialSum2, Finset.sum_range_succ]
    rw [pow_succ, hrec]; ring
  -- Both `Tₙ₊₁ xⁿ⁺¹` and `x·(Tₙ xⁿ)` are summable, hence so is the shifted `Sₙ₊₁ xⁿ⁺¹`.
  have hTshift : Summable (fun n : ℕ => partialSum2 a (n + 1) * x ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hT
  have hxT : Summable (fun n : ℕ => x * (partialSum2 a n * x ^ n)) := hT.mul_left x
  have hSshift : Summable (fun n : ℕ => partialSum a (n + 1) * x ^ (n + 1)) :=
    (hTshift.sub hxT).congr (fun n => (key n).symm)
  exact (summable_nat_add_iff 1).mp hSshift

/-- **Frobenius's theorem (general form).** If the Cesàro means `Tₙ/(n+1)` of the partial
sums converge to `L`, then the Abel limit `lim_{x→1⁻} ∑ₙ aₙ xⁿ` equals `L`. -/
theorem frobenius_cesaro_imp_abel (a : ℕ → ℝ) (L : ℝ)
    (hL : Tendsto (fun N : ℕ => partialSum2 a N / ((N : ℝ) + 1)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => ∑' n : ℕ, a n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  sorry

/-- **Specialization to Grandi's series** `aₙ = (−1)ⁿ`: its partial sums are `1,0,1,0,…`,
whose Cesàro means converge to `1/2`, recovering the Abel value `1/2` of
`geometric-series-oq-01-oq-01` as an instance of Frobenius. -/
theorem grandi_abel_via_frobenius :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2)) := by
  have hL : Tendsto
      (fun N : ℕ => partialSum2 (fun n => (-1 : ℝ) ^ n) N / ((N : ℝ) + 1)) atTop (𝓝 (1 / 2)) := by
    sorry
  simpa using frobenius_cesaro_imp_abel (fun n => (-1 : ℝ) ^ n) (1 / 2) hL

end FrobeniusCesaroAbel
