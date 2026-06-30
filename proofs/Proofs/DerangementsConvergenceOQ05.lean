import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic

/-
# The Fixed-Point Count Distribution of a Random Permutation

This file answers the open question recorded with `derangements-convergence`:

> What is the analogous convergence rate for `D_k(n)/n!`, where `D_k(n)` counts
> the permutations of an `n`-element set with **exactly `k` fixed points**?
> The limit is `e⁻¹ / k!` — the Poisson(1) probability mass at `k`.

The parent entry treats the case `k = 0` (derangements). Here we treat every `k`.

## Main results

* `fixedPointCount_eq` : the combinatorial heart,
  `D_k(n) = C(n, k) · D(n - k)`, where `D = numDerangements`.
  A permutation with exactly `k` fixed points is the choice of *which* `k`
  points are fixed together with a derangement of the remaining `n - k`.

* `sum_fixedPointCount` : `∑_{k=0}^n D_k(n) = n!` — the counts partition `Sym(n)`.

* `fixedPointProb_eq` : for `k ≤ n`,
  `D_k(n)/n! = (1/k!) · (D(n-k)/(n-k)!)`.

* `fixedPointProb_tendsto` : the headline limit,
  `D_k(n)/n! → e⁻¹ / k!` as `n → ∞` (the Poisson(1) mass function),
  obtained from Mathlib's `numDerangements_tendsto_inv_e` via the shift `n ↦ n - k`.

The combinatorial bijection (exactly-`k`-fixed-points permutations ↔ derangements of
the complement) is **not** in Mathlib; the analytic limit reuses Mathlib's
`numDerangements_tendsto_inv_e`.
-/

open Equiv Function Finset Filter Topology
open scoped BigOperators

namespace DerangementsFixedPointDistribution

variable {n : ℕ}

/-- `fixedPointCount n k` is the number of permutations of `Fin n` having
*exactly* `k` fixed points (`D_k(n)` in the literature). -/
def fixedPointCount (n k : ℕ) : ℕ :=
  (univ.filter
    (fun σ : Perm (Fin n) => (univ.filter (fun i => σ i = i)).card = k)).card

/-- For a fixed target set `S`, the permutations of `Fin n` whose fixed-point set is
*exactly* `S` are in bijection with the derangements of the complement `Sᶜ`; hence there
are `numDerangements (n - |S|)` of them. This is the core counting lemma. -/
theorem card_perm_fixedSet_eq (S : Finset (Fin n)) :
    (univ.filter (fun σ : Perm (Fin n) => univ.filter (fun i => σ i = i) = S)).card
      = numDerangements (n - S.card) := by
  -- Rephrase the fixed-set condition as the predicate used by `derangements.subtypeEquiv`.
  have hpred : ∀ σ : Perm (Fin n),
      (univ.filter (fun i => σ i = i) = S)
        ↔ (∀ a, ¬ (a ∈ Sᶜ) ↔ a ∈ fixedPoints σ) := by
    intro σ
    simp only [Finset.ext_iff, mem_filter, mem_univ, true_and, Finset.mem_compl,
      not_not, Function.mem_fixedPoints, Function.IsFixedPt]
    constructor
    · intro h a; exact (h a).symm
    · intro h a; exact (h a).symm
  -- The bijection {σ // fixedSet σ = S} ≃ derangements (↥Sᶜ).
  let e : {σ : Perm (Fin n) // univ.filter (fun i => σ i = i) = S}
        ≃ derangements (Subtype (fun a : Fin n => a ∈ Sᶜ)) :=
    (Equiv.subtypeEquivRight hpred).trans (derangements.subtypeEquiv _).symm
  rw [← Fintype.card_subtype, Fintype.card_congr e, card_derangements_eq_numDerangements]
  congr 1
  have hset : (univ.filter (fun a : Fin n => a ∈ Sᶜ)) = Sᶜ := by ext x; simp
  rw [Fintype.card_subtype, hset, Finset.card_compl, Fintype.card_fin]

/-- **The fixed-point count.** The number of permutations of `Fin n` with exactly `k`
fixed points equals `C(n, k) · D(n - k)`: choose which `k` points are fixed, then
derange the remaining `n - k`. -/
theorem fixedPointCount_eq (n k : ℕ) :
    fixedPointCount n k = n.choose k * numDerangements (n - k) := by
  unfold fixedPointCount
  -- Partition the permutations by their fixed-point set, which has cardinality `k`.
  rw [Finset.card_eq_sum_card_fiberwise
        (t := powersetCard k (univ : Finset (Fin n)))
        (f := fun σ : Perm (Fin n) => univ.filter (fun i => σ i = i))
        (by
          intro σ hσ
          simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hσ
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          exact ⟨Finset.filter_subset _ _, hσ⟩)]
  -- Each fibre over a `k`-subset `S` has `D(n-k)` elements.
  have hterm : ∀ S ∈ powersetCard k (univ : Finset (Fin n)),
      ((univ.filter (fun σ : Perm (Fin n) => (univ.filter (fun i => σ i = i)).card = k)).filter
        (fun σ => univ.filter (fun i => σ i = i) = S)).card = numDerangements (n - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.filter_filter]
    have hcollapse :
        (univ.filter (fun σ : Perm (Fin n) =>
          (univ.filter (fun i => σ i = i)).card = k ∧ univ.filter (fun i => σ i = i) = S))
        = univ.filter (fun σ : Perm (Fin n) => univ.filter (fun i => σ i = i) = S) := by
      apply Finset.filter_congr
      intro σ _
      simp only [and_iff_right_iff_imp]
      intro h; rw [h]; exact hS.2
    rw [hcollapse, card_perm_fixedSet_eq, hS.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Sanity / completeness.** Summing the counts over all possible numbers of fixed
points recovers every permutation: `∑_{k=0}^n D_k(n) = n!`. -/
theorem sum_fixedPointCount (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), fixedPointCount n k = n.factorial := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Perm (Fin n))))
    (t := Finset.range (n + 1))
    (f := fun σ : Perm (Fin n) => (univ.filter (fun i => σ i = i)).card)
    (by
      intro σ _
      simp only [Finset.mem_coe, Finset.mem_range]
      have : (univ.filter (fun i => σ i = i)).card ≤ (univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h]
  rfl

/-- `fixedPointProb n k` is the probability that a uniform random permutation of
`Fin n` has exactly `k` fixed points: `D_k(n) / n!`. -/
noncomputable def fixedPointProb (n k : ℕ) : ℝ :=
  (fixedPointCount n k : ℝ) / (n.factorial : ℝ)

/-- The probability factors as `(1/k!) · (D(n-k)/(n-k)!)` whenever `k ≤ n`. -/
theorem fixedPointProb_eq (n k : ℕ) (h : k ≤ n) :
    fixedPointProb n k
      = (1 / (k.factorial : ℝ)) * ((numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ)) := by
  have hkey : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ)
      = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
  have hnk : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  unfold fixedPointProb
  rw [fixedPointCount_eq]
  push_cast
  field_simp
  linear_combination (numDerangements (n - k) : ℝ) * hkey

/-- **The Poisson(1) limit.** As `n → ∞`, the probability that a random permutation of
`Fin n` has exactly `k` fixed points converges to `e⁻¹ / k!` — the Poisson(1) mass at `k`.
Specialising to `k = 0` recovers the derangement limit `D(n)/n! → e⁻¹`. -/
theorem fixedPointProb_tendsto (k : ℕ) :
    Tendsto (fun n => fixedPointProb n k) atTop (𝓝 (Real.exp (-1) / (k.factorial : ℝ))) := by
  -- `n ↦ n - k` tends to infinity, so we may compose with the derangement limit.
  have hsub : Tendsto (fun n : ℕ => n - k) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b + k, fun n hn => by omega⟩)
  have hcomp : Tendsto (fun n => (numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ)) atTop
      (𝓝 (Real.exp (-1))) := by
    simpa [Function.comp] using numDerangements_tendsto_inv_e.comp hsub
  have hmul := hcomp.const_mul (1 / (k.factorial : ℝ))
  have heq : (1 / (k.factorial : ℝ)) * Real.exp (-1) = Real.exp (-1) / (k.factorial : ℝ) := by
    ring
  rw [heq] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (fixedPointProb_eq n k hn).symm

end DerangementsFixedPointDistribution
