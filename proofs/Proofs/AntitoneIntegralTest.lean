import Mathlib

/-
# The Integral Test: a Convergence Criterion for Antitone Series

The parent entry `AntitoneIntegralSumComparison` packaged the two-sided sandwich

  ∑_{i<n} f(x₀ + i + 1)  ≤  ∫_{x₀}^{x₀+n} f  ≤  ∑_{i<n} f(x₀ + i)

for an antitone `f`, and applied it to the single function `f(x) = 1/x`.  This
entry promotes that sandwich into the **general integral test**: for an
antitone, nonnegative `f` on `[1, ∞)`, the series `∑ₙ f(n+1)` converges **iff**
the sequence of definite integrals `∫₁^{1+n} f` is bounded above.

Mathlib supplies the one-step comparisons `AntitoneOn.sum_le_integral` and
`AntitoneOn.integral_le_sum`, but packages them into no convergence dichotomy;
this entry fills that gap.  We then recover, purely through the test, the
classical **divergence of the harmonic series**: the integrals
`∫₁^{1+n} 1/x = log(n+1)` are unbounded, so `∑ 1/(n+1)` cannot converge.

All results are fully machine-verified: 0 sorries, 0 axioms.
-/

namespace AntitoneIntegralTest

open scoped BigOperators
open Finset intervalIntegral

variable {f : ℝ → ℝ}

/-! ## Part I — Windowed antitonicity -/

/-- Restrict antitonicity from `[1, ∞)` to each finite window `[1, 1+n]`. -/
private theorem antitoneOn_window (hmono : AntitoneOn f (Set.Ici (1 : ℝ))) (n : ℕ) :
    AntitoneOn f (Set.Icc 1 (1 + (n : ℝ))) :=
  hmono.mono Set.Icc_subset_Ici_self

/-! ## Part II — The two comparisons, indexed by the series `n ↦ f(n+1)` -/

/-- **Upper comparison.** The integral over `[1, 1+n]` is at most the `n`-term
partial sum `∑_{i<n} f(i+1)` (the left Riemann sum). -/
theorem integral_le_partialSum (hmono : AntitoneOn f (Set.Ici (1 : ℝ))) (n : ℕ) :
    (∫ x in (1 : ℝ)..(1 + n), f x) ≤ ∑ i ∈ Finset.range n, f ((i : ℝ) + 1) := by
  refine ((antitoneOn_window hmono n).integral_le_sum).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- **Lower comparison.** The `(n+1)`-term partial sum `∑_{i<n+1} f(i+1)` is at
most `f 1 + ∫₁^{1+n} f` (the right Riemann sum, shifted by the first term). -/
theorem partialSum_succ_le (hmono : AntitoneOn f (Set.Ici (1 : ℝ))) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f ((i : ℝ) + 1)) ≤ f 1 + ∫ x in (1 : ℝ)..(1 + n), f x := by
  have h := (antitoneOn_window hmono n).sum_le_integral
  -- h : (∑ i ∈ range n, f (1 + ↑(i+1))) ≤ ∫ x in 1..1+↑n, f x
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add]
  -- goal : (∑ i ∈ range n, f (↑(i+1) + 1)) + f 1 ≤ f 1 + ∫ ...
  have e : (∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) + 1))
      = ∑ i ∈ Finset.range n, f (1 + ((i + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [e]
  linarith [h]

/-! ## Part III — The integral test -/

/-- **The integral test.** For an antitone, nonnegative `f` on `[1, ∞)`, the
series `∑ₙ f(n+1)` is summable **iff** the sequence of integrals `∫₁^{1+n} f` is
bounded above.  This is the convergence dichotomy underlying every application
of the sum–integral sandwich. -/
theorem integral_test (hmono : AntitoneOn f (Set.Ici (1 : ℝ)))
    (hnonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) :
    Summable (fun n : ℕ => f ((n : ℝ) + 1)) ↔
      BddAbove (Set.range fun n : ℕ => ∫ x in (1 : ℝ)..(1 + n), f x) := by
  have hgnn : ∀ n : ℕ, 0 ≤ f ((n : ℝ) + 1) := fun n =>
    hnonneg _ (le_add_of_nonneg_left (Nat.cast_nonneg n))
  constructor
  · -- Summable ⟹ integrals bounded (by the total sum)
    intro hsum
    refine ⟨∑' n, f ((n : ℝ) + 1), ?_⟩
    rintro _ ⟨n, rfl⟩
    refine (integral_le_partialSum hmono n).trans ?_
    exact sum_le_hasSum (Finset.range n) (fun i _ => hgnn i) hsum.hasSum
  · -- integrals bounded ⟹ Summable (bounded partial sums of a nonneg series)
    rintro ⟨B, hB⟩
    have hBmem : ∀ n : ℕ, (∫ x in (1 : ℝ)..(1 + n), f x) ≤ B := fun n =>
      hB ⟨n, rfl⟩
    refine summable_of_sum_range_le hgnn (c := f 1 + B) ?_
    intro n
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have h1 : (0 : ℝ) ≤ f 1 := hnonneg 1 le_rfl
      have hB0 : (0 : ℝ) ≤ B := by simpa using hBmem 0
      linarith
    | succ m =>
      refine (partialSum_succ_le hmono m).trans ?_
      linarith [hBmem m]

/-! ## Part IV — Application: divergence of the harmonic series -/

/-- `x ↦ 1/x` is antitone on `[1, ∞)`. -/
private theorem oneDiv_antitone : AntitoneOn (fun x : ℝ => 1 / x) (Set.Ici (1 : ℝ)) := by
  intro x hx y _ hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  exact one_div_le_one_div_of_le (by linarith) hxy

/-- `∫₁^{1+n} 1/x dx = log(n + 1)`. -/
private theorem log_integral (n : ℕ) :
    (∫ x in (1 : ℝ)..(1 + (n : ℝ)), 1 / x) = Real.log ((n : ℝ) + 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (n : ℝ)) :=
    Set.notMem_uIcc_of_lt one_pos (by positivity)
  rw [integral_one_div h0, div_one]
  congr 1
  ring

/-- **The harmonic series diverges.** Applying the integral test to `f(x) = 1/x`:
the integrals `∫₁^{1+n} 1/x = log(n+1)` are unbounded (`log → ∞`), so the series
`∑ₙ 1/(n+1)` is not summable. -/
theorem not_summable_one_div_harmonic :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro hs
  have hbdd :=
    (integral_test oneDiv_antitone (fun x hx => div_nonneg zero_le_one (by linarith))).mp hs
  obtain ⟨B, hB⟩ := hbdd
  -- the integrals `log(n+1)` grow without bound
  have hlim : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := (hlim.eventually_gt_atTop B).exists
  have hval : (∫ x in (1 : ℝ)..(1 + (N : ℝ)), (fun x : ℝ => 1 / x) x) = Real.log ((N : ℝ) + 1) :=
    log_integral N
  have hle : (∫ x in (1 : ℝ)..(1 + (N : ℝ)), (fun x : ℝ => 1 / x) x) ≤ B :=
    hB (Set.mem_range_self N)
  rw [hval] at hle
  linarith [hN, hle]

end AntitoneIntegralTest
