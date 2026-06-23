import Mathlib

/-
# The Roots-of-Unity Multisection Filter for an Absolutely Convergent Series

## What This Proves

Fix an integer modulus `q ≥ 1` and a primitive `q`-th root of unity `ω` in `ℂ`
(canonically `ω = exp(2πi/q)`).  For an **absolutely convergent** complex series
`∑_m f m` (i.e. `Summable (‖f ·‖)`) and a residue `a < q`, the residue subseries
`∑_n f (q·n + a)` is recovered as a discrete-Fourier average of the `q` *rotated*
full sums:

  `∑'_n f (q·n + a)  =  q⁻¹ · ∑_{j<q} (ω^{j·a})⁻¹ · ∑'_m ω^{j·m} · f m`.

This is the classical **roots-of-unity filter** (a.k.a. the multisection / series
multisection formula): the inner sum `∑'_m ω^{j·m} f m` is the original series with
its `m`-th term rotated by `ω^{j·m}`, and the outer DFT-weighted average over
`j = 0, …, q-1` annihilates every residue class except `a`.

## Relation to the Sibling (`…-oq-01`)

The parent's open question has two genuinely different answers.  The combinatorial
one (`geometric-series-oq-09-oq-01-oq-01-oq-01`) realises the multisection as a
*partition / Fubini regrouping* `HasSum.prod_fiberwise` of the reindexing
`ℕ ≃ ℕ × Fin q`; it holds for ANY summable family valued in a complete Hausdorff
abelian group, with no roots of unity and no absolute convergence.  This file gives
the *analytic / Fourier* answer: the same residue subseries expressed as a weighted
average of rotated copies of the WHOLE series.  This genuinely needs the complex
field (roots of unity) and **absolute** convergence — multiplying the conditionally
convergent series by the bounded twist `ω^{j·m}` need not preserve plain
summability, whereas it preserves absolute summability since `‖ω^{j·m}‖ = 1`.  The
two results are complementary facets of the multisection, not variants.

## Why This Is Not Already in Mathlib

Mathlib has primitive roots (`Complex.isPrimitiveRoot_exp`), the finite geometric
sum (`geom_sum_eq`), `pow_eq_pow_iff_modEq`, and the linearity/reindexing toolkit
for `tsum`, but not their assembly into the series multisection filter.  The new
content is the orthogonality computation `q⁻¹ ∑_{j<q} ((ω^a)⁻¹ ω^m)^j = ⟦m ≡ a⟧`
(a `q`-fold geometric sum that collapses to the indicator of the residue class via
`((ω^a)⁻¹ ω^m)^q = 1`), combined with the absolutely-convergent interchange of the
finite DFT sum with the infinite series and the reindexing of the surviving
indicator-weighted series onto the residue subseries.

## Status: 0 sorries, 0 axioms.
-/

namespace GeometricSeriesOQ09OQ01OQ01OQ02

open Complex Finset

variable {f : ℕ → ℂ}

/-- For `q ≠ 0` the residue map `n ↦ q·n + a` is injective `ℕ → ℕ`. -/
theorem residue_injective {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Function.Injective (fun n : ℕ => q * n + a) := by
  intro n m h
  have : q * n = q * m := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

/-- The shift `q·n + a` lies in the residue class `a` modulo `q`. -/
theorem residue_self_modEq {q : ℕ} (n a : ℕ) : (q * n + a) ≡ a [MOD q] := by
  unfold Nat.ModEq
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

/-- For `a < q`, every element of the residue class `a` mod `q` is `q·n + a`. -/
theorem residue_mem_range {q : ℕ} (a m : ℕ) (ha : a < q) (hcong : m ≡ a [MOD q]) :
    m ∈ Set.range (fun n : ℕ => q * n + a) := by
  refine ⟨m / q, ?_⟩
  have hma : m % q = a := by
    have h : m % q = a % q := hcong
    rwa [Nat.mod_eq_of_lt ha] at h
  show q * (m / q) + a = m
  rw [← hma, Nat.div_add_mod]

/-- **Roots-of-unity multisection filter.**  For an absolutely convergent complex
series `f` and a primitive `q`-th root of unity `ω`, the residue subseries
`∑'_n f (q·n + a)` (with `a < q`) equals the DFT-weighted average of the `q`
twisted full sums `∑'_m ω^{j·m} f m`. -/
theorem multisection_filter
    (hf : Summable (fun m => ‖f m‖)) {q : ℕ} (hq : q ≠ 0)
    {ω : ℂ} (hω : IsPrimitiveRoot ω q) {a : ℕ} (ha : a < q) :
    ∑' n : ℕ, f (q * n + a)
      = (q : ℂ)⁻¹ * ∑ j ∈ range q,
          (ω ^ (j * a))⁻¹ * ∑' m : ℕ, ω ^ (j * m) * f m := by
  -- Basic facts about ω.
  have hω1 : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hq
  have hωne : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hω1; exact one_ne_zero hω1.symm
  have hfin : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨q, Nat.pos_of_ne_zero hq, hω.pow_eq_one⟩
  have hord : orderOf ω = q := hω.eq_orderOf.symm
  -- Each twisted series is (absolutely) summable: ‖ω^{j·m} f m‖ = ‖f m‖.
  have htw : ∀ j : ℕ, Summable (fun m => ω ^ (j * m) * f m) := by
    intro j
    apply Summable.of_norm
    have heq : (fun m => ‖ω ^ (j * m) * f m‖) = (fun m => ‖f m‖) := by
      funext m; rw [norm_mul, norm_pow, hω1, one_pow, one_mul]
    rw [heq]; exact hf
  -- The residue subseries is summable.
  have hres : Summable (fun n => f (q * n + a)) := by
    apply Summable.of_norm
    simpa [Function.comp_def] using hf.comp_injective (residue_injective hq a)
  -- Orthogonality: q⁻¹ · ∑_{j<q} (ω^{ja})⁻¹ ω^{jm} = ⟦m ≡ a (mod q)⟧.
  have hEm : ∀ m : ℕ,
      (q : ℂ)⁻¹ * (∑ j ∈ range q, (ω ^ (j * a))⁻¹ * ω ^ (j * m))
        = if m ≡ a [MOD q] then (1 : ℂ) else 0 := by
    intro m
    -- rewrite the j-th term as zʲ with z = (ω^a)⁻¹ · ω^m
    have hterm : ∀ j, (ω ^ (j * a))⁻¹ * ω ^ (j * m) = ((ω ^ a)⁻¹ * ω ^ m) ^ j := by
      intro j
      rw [mul_comm j a, mul_comm j m, pow_mul, pow_mul, ← inv_pow, ← mul_pow]
    have hsum_z : (∑ j ∈ range q, (ω ^ (j * a))⁻¹ * ω ^ (j * m))
        = ∑ j ∈ range q, ((ω ^ a)⁻¹ * ω ^ m) ^ j :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    have hmod : ω ^ m = ω ^ a ↔ m ≡ a [MOD q] := by
      rw [hfin.pow_eq_pow_iff_modEq, hord]
    have hzq : ((ω ^ a)⁻¹ * ω ^ m) ^ q = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a q, mul_comm m q,
        pow_mul, pow_mul]
      simp only [hω.pow_eq_one, one_pow, inv_one, mul_one]
    rw [hsum_z]
    by_cases hcong : m ≡ a [MOD q]
    · rw [if_pos hcong]
      have hmeq : ω ^ m = ω ^ a := hmod.mpr hcong
      have hz1 : (ω ^ a)⁻¹ * ω ^ m = 1 := by
        rw [hmeq, inv_mul_cancel₀ (pow_ne_zero a hωne)]
      rw [hz1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (by exact_mod_cast hq)
    · rw [if_neg hcong]
      have hzne : (ω ^ a)⁻¹ * ω ^ m ≠ 1 := by
        intro h
        apply hcong
        have hmeq : ω ^ m = ω ^ a := by
          have h2 : ω ^ a * ((ω ^ a)⁻¹ * ω ^ m) = ω ^ a * 1 := by rw [h]
          rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hωne), one_mul, mul_one] at h2
        exact hmod.mp hmeq
      rw [geom_sum_eq hzne q, hzq]
      simp
  -- Rewrite the RHS into ∑'_m ⟦m ≡ a⟧ · f m.
  have key :
      (q : ℂ)⁻¹ * ∑ j ∈ range q, (ω ^ (j * a))⁻¹ * ∑' m : ℕ, ω ^ (j * m) * f m
        = ∑' m : ℕ, (if m ≡ a [MOD q] then (1 : ℂ) else 0) * f m := by
    -- pull the coefficient into each tsum
    have step1 : ∀ j ∈ range q,
        (ω ^ (j * a))⁻¹ * ∑' m, ω ^ (j * m) * f m
          = ∑' m, (ω ^ (j * a))⁻¹ * (ω ^ (j * m) * f m) :=
      fun j _ => (tsum_mul_left).symm
    rw [Finset.sum_congr rfl step1]
    -- swap the finite DFT sum with the infinite series
    rw [← Summable.tsum_finsetSum (fun j _ => (htw j).mul_left ((ω ^ (j * a))⁻¹))]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have hfactor : ∑ j ∈ range q, (ω ^ (j * a))⁻¹ * (ω ^ (j * m) * f m)
        = (∑ j ∈ range q, (ω ^ (j * a))⁻¹ * ω ^ (j * m)) * f m := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])
    rw [hfactor, ← mul_assoc, hEm m]
  rw [key]
  -- Reindex ∑'_m ⟦m ≡ a⟧ f m onto the residue subseries ∑'_n f (q·n+a).
  symm
  have hsupp : ∀ x, x ∉ Set.range (fun n : ℕ => q * n + a) →
      (if x ≡ a [MOD q] then (1 : ℂ) else 0) * f x = 0 := by
    intro x hx
    rw [if_neg (fun hcong => hx (residue_mem_range a x ha hcong)), zero_mul]
  have hFe : HasSum (fun m => (if m ≡ a [MOD q] then (1 : ℂ) else 0) * f m)
      (∑' n, f (q * n + a)) := by
    rw [← (residue_injective hq a).hasSum_iff hsupp]
    have hcomp : ((fun m => (if m ≡ a [MOD q] then (1 : ℂ) else 0) * f m)
          ∘ (fun n : ℕ => q * n + a))
        = (fun n => f (q * n + a)) := by
      funext n
      simp only [Function.comp_apply]
      rw [if_pos (residue_self_modEq n a), one_mul]
    rw [hcomp]
    exact hres.hasSum
  exact hFe.tsum_eq

/-- Specialisation to the canonical root `ω = exp(2πi/q)`. -/
theorem multisection_filter_exp
    (hf : Summable (fun m => ‖f m‖)) {q : ℕ} (hq : q ≠ 0) {a : ℕ} (ha : a < q) :
    ∑' n : ℕ, f (q * n + a)
      = (q : ℂ)⁻¹ * ∑ j ∈ range q,
          (Complex.exp (2 * ↑Real.pi * Complex.I / q) ^ (j * a))⁻¹
            * ∑' m : ℕ, Complex.exp (2 * ↑Real.pi * Complex.I / q) ^ (j * m) * f m :=
  multisection_filter hf hq (Complex.isPrimitiveRoot_exp q hq) ha

/-- **Even-part filter (`q = 2`).**  The even subseries of an absolutely convergent
complex series is the half-sum of the series and its alternating twin, via the
primitive square root of unity `ω = -1`:
`∑'_n f (2n) = ½ (∑'_m f m + ∑'_m (-1)^m f m)`. -/
theorem tsum_even_filter (hf : Summable (fun m => ‖f m‖)) :
    ∑' n : ℕ, f (2 * n)
      = (2 : ℂ)⁻¹ * (∑' m : ℕ, f m + ∑' m : ℕ, (-1 : ℂ) ^ m * f m) := by
  have h := multisection_filter (f := f) (q := 2) (a := 0) hf (by norm_num)
    (IsPrimitiveRoot.neg_one 0 (by norm_num)) (by norm_num)
  simp only [Nat.add_zero, pow_zero, inv_one, one_mul,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_mul,
    mul_zero] at h
  simpa using h

end GeometricSeriesOQ09OQ01OQ01OQ02
