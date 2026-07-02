import Proofs.DerangementsOQ04OQ01
import Proofs.DerangementsConvergence

/-
# Poisson limit for the fixed-point distribution of a random permutation

The parent entry `derangements-oq-04-oq-01`
(`DerangementsOQ04OQ01.card_perms_with_kfixed_closed_form_real`) proves the exact
closed form for the number `S(n,k)` of permutations of `Fin n` with *exactly* `k`
fixed points:

  `S(n,k) = (n! / k!) · ∑_{j=0}^{n-k} (-1)^j / j!`.

Its first open question asks to **divide by `n!`** — turning the count into the
probability that a uniformly random permutation of `Fin n` has exactly `k` fixed
points — and to **take `n → ∞`**, exhibiting the classical limiting law:

  `S(n,k) / n! = (1/k!) · ∑_{j=0}^{n-k} (-1)^j / j!  ⟶  e^{-1} / k!`,

the **Poisson(1)** probability mass function `e^{-1} · 1^k / k!`.  This is the
theorem that the number of fixed points of a random permutation converges in
distribution to a Poisson random variable with mean `1`.

The proof is a clean limit assembly with no new combinatorics:

* the parent supplies the exact per-`n` value `S(n,k)/n! = (1/k!)·altFactPartialSum(n-k)`
  (after cancelling `n!`, valid for `n ≥ k`);
* the sibling analysis file `DerangementsConvergence` supplies
  `altFactPartialSum m = ∑_{j=0}^{m} (-1)^j/j! ⟶ e^{-1}` as `m → ∞`
  (the partial sums of the summable alternating exponential series, whose total
  is `e^{-1}` by `exp_neg_one_eq_tsum_alt`);
* since `k` is fixed, `n - k ⟶ ∞`, so composing gives
  `altFactPartialSum(n-k) ⟶ e^{-1}`, and scaling by the constant `1/k!` gives the
  claim.  The `k = 0` case recovers the parent derangement limit `D_n/n! ⟶ e^{-1}`.

## Status
- [x] Complete proof (0 sorries, 0 axioms beyond Mathlib's foundations).
-/

open Finset Filter Topology

namespace DerangementsOQ04OQ01OQ01

/-- **The partial sums of the alternating exponential series converge to `e^{-1}`.**
`altFactPartialSum m = ∑_{j=0}^{m} (-1)^j / j!` are the truncations of the series
`∑_j (-1)^j/j!`, whose total is `e^{-1}` (`exp_neg_one_eq_tsum_alt`).  Being the
`(m+1)`-term partial sums of a summable series, they tend to that total. -/
theorem altFactPartialSum_tendsto_expNegOne :
    Tendsto altFactPartialSum atTop (nhds (Real.exp (-1))) := by
  have hsum : HasSum altFactTerm (Real.exp (-1)) := by
    rw [exp_neg_one_eq_tsum_alt]
    exact summable_altFactTerm.hasSum
  have hps : Tendsto (fun m => ∑ i ∈ range m, altFactTerm i) atTop (nhds (Real.exp (-1))) :=
    hsum.tendsto_sum_nat
  have hcomp := hps.comp (tendsto_add_atTop_nat 1)
  simpa [altFactPartialSum, Function.comp] using hcomp

/-- **Poisson limit of the fixed-point distribution.**  For a fixed `k`, the
probability that a uniformly random permutation of `Fin n` has exactly `k` fixed
points converges to the Poisson(1) mass `e^{-1} / k!` as `n → ∞`:

  `S(n,k) / n!  ⟶  e^{-1} / k!`.

This answers the parent entry's open question, "divide by `n!` and take `n → ∞`".
The `k = 0` instance recovers the derangement limit `D_n / n! ⟶ e^{-1}`. -/
theorem fixedPoints_tendsto_poisson (k : ℕ) :
    Tendsto (fun n : ℕ =>
        ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
            (univ.filter (fun x => σ x = x)).card = k)).card : ℝ) / (n.factorial : ℝ))
      atTop (nhds (Real.exp (-1) / (k.factorial : ℝ))) := by
  -- `k` is fixed, so `n ↦ n - k` tends to infinity
  have hsubk : Tendsto (fun n : ℕ => n - k) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b + k, fun n hn => by omega⟩)
  -- partial sums evaluated along `n - k` still converge to `e^{-1}`
  have hcomp : Tendsto (fun n : ℕ => altFactPartialSum (n - k)) atTop (nhds (Real.exp (-1))) :=
    altFactPartialSum_tendsto_expNegOne.comp hsubk
  -- scale by the constant `1 / k!`
  have hmul :
      Tendsto (fun n : ℕ => (1 / (k.factorial : ℝ)) * altFactPartialSum (n - k))
        atTop (nhds ((1 / (k.factorial : ℝ)) * Real.exp (-1))) :=
    hcomp.const_mul _
  have hlim : (1 / (k.factorial : ℝ)) * Real.exp (-1)
      = Real.exp (-1) / (k.factorial : ℝ) := by ring
  rw [hlim] at hmul
  -- the scaled partial sums equal `S(n,k)/n!` eventually (for `n ≥ k`)
  refine hmul.congr' ?_
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{n | k ≤ n}, ?_, fun n hn => ?_⟩
  · exact eventually_ge_atTop k
  · -- discharge the pointwise identity via the parent closed form
    dsimp only  -- beta-reduce the `(fun n => …) n` redexes so `rw` can see the terms
    have hcf := DerangementsOQ04OQ01.card_perms_with_kfixed_closed_form_real n k hn
    have hnfac : (n.factorial : ℝ) ≠ 0 := factorial_cast_ne_zero' n
    have hkfac : (k.factorial : ℝ) ≠ 0 := factorial_cast_ne_zero' k
    have hunfold : altFactPartialSum (n - k)
        = ∑ j ∈ range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ) := by
      simp only [altFactPartialSum, altFactTerm]
    rw [hunfold, hcf]
    field_simp

/-- **Consistency with the parent derangement limit.**  Specialising to `k = 0`
recovers `D_n / n! ⟶ e^{-1}`: the probability that a random permutation is a
derangement tends to `e^{-1}`, the Poisson(1) mass at `0`. -/
theorem derangements_tendsto_poisson_zero :
    Tendsto (fun n : ℕ =>
        ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
            (univ.filter (fun x => σ x = x)).card = 0)).card : ℝ) / (n.factorial : ℝ))
      atTop (nhds (Real.exp (-1))) := by
  have h := fixedPoints_tendsto_poisson 0
  simpa using h

end DerangementsOQ04OQ01OQ01
