/-
  Derangements: the fixed-point convolution identity
      n! = Σ_{k=0}^{n} C(n,k) · D(n−k)
  Open question: derangements-convergence-oq-07

  ## Context

  The parent file `DerangementsConvergence.lean` studies the derangement numbers
  `D(n) = numDerangements n` analytically (the ratio `D(n)/n! → 1/e`).  A separate,
  purely combinatorial fact underlies the whole subject: the number of permutations
  of an `n`-element set, sorted by the *size of their fixed-point set*, reconstructs
  `n!` as a binomial convolution with the derangement numbers.

  ## What this file adds

  We prove, for any finite type `α` (and hence for `Fin n`), the **fixed-point
  convolution identity**

      |α|! = Σ_{k=0}^{|α|} C(|α|, k) · D(|α| − k).

  The proof is the classical bijective one, made fully formal:

  * `card_fixedPointFinset_fiber` — permutations whose set of fixed points is exactly
    a given subset `S` are in bijection with the derangements of the complement of `S`,
    so there are `D(|α| − |S|)` of them.  This is obtained from Mathlib's
    `derangements.subtypeEquiv`.
  * `card_perm_eq_sum_choose_mul_numDerangements` — summing the fibers over all subsets
    `S`, grouped by `|S| = k` (there are `C(|α|, k)` such subsets), and using
    `Fintype.card_perm` for the left-hand side, yields the identity.
  * `factorial_eq_sum_choose_mul_numDerangements` — the specialization to `α = Fin n`,
    stated purely in terms of `n : ℕ`.

  Mathlib contains the analytic and recursive theory of `numDerangements`
  (`numDerangements_sum`, the `D(n)/n! → 1/e` limit) but **not** this convolution
  identity, so it is a genuine addition rather than a wrapper.

  ## Main results
  - `card_fixedPointFinset_fiber`                    : fiber count = `D(|α| − |S|)`
  - `card_perm_eq_sum_choose_mul_numDerangements`    : `|α|! = Σ C(|α|,k)·D(|α|−k)`
  - `factorial_eq_sum_choose_mul_numDerangements`    : `n! = Σ_{k≤n} C(n,k)·D(n−k)`
-/
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic

open Equiv Function Finset Nat
open scoped BigOperators

namespace DerangementsConvolution

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Permutations of `α` whose set of fixed points is **exactly** `S` are in bijection
with the derangements of the complement of `S`.  Hence there are
`numDerangements (|α| − |S|)` of them. -/
theorem card_fixedPointFinset_fiber (S : Finset α) :
    (univ.filter (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)).card
      = numDerangements (Fintype.card α - S.card) := by
  classical
  -- Rewrite the filter-cardinality as the cardinality of a subtype.
  have hb : (univ.filter (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)).card
      = Fintype.card {σ : Perm α // univ.filter (fun x => σ x = x) = S} := by
    simp [Fintype.card_subtype]
  -- The subtype `{σ // fixedFinset σ = S}` matches the RHS of `derangements.subtypeEquiv`
  -- with predicate `(· ∉ S)`.
  have e1 : {σ : Perm α // univ.filter (fun x => σ x = x) = S}
      ≃ {σ : Perm α // ∀ a, ¬ (a ∉ S) ↔ a ∈ fixedPoints σ} :=
    Equiv.subtypeEquivRight (fun σ => by
      rw [Finset.ext_iff]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
        Function.mem_fixedPoints, Function.IsFixedPt]
      exact ⟨fun h a => (h a).symm, fun h a => (h a).symm⟩)
  have e2 : derangements (Subtype (fun a : α => a ∉ S))
      ≃ {σ : Perm α // ∀ a, ¬ (a ∉ S) ↔ a ∈ fixedPoints σ} :=
    derangements.subtypeEquiv (fun a : α => a ∉ S)
  rw [hb, Fintype.card_congr e1, ← Fintype.card_congr e2,
    card_derangements_eq_numDerangements, Fintype.card_subtype_compl, Fintype.card_coe]

/-- **Fixed-point convolution identity.**  For any finite type `α`,
`|α|! = Σ_{k=0}^{|α|} C(|α|, k) · D(|α| − k)`, where `D = numDerangements`.

Both sides count `Perm α`: the left by `Fintype.card_perm`, the right by partitioning
permutations according to the size `k` of their fixed-point set (there are `C(|α|, k)`
choices of that set, and the remaining `|α| − k` points are deranged). -/
theorem card_perm_eq_sum_choose_mul_numDerangements :
    (Fintype.card α)! =
      ∑ k ∈ range (Fintype.card α + 1),
        (Fintype.card α).choose k * numDerangements (Fintype.card α - k) := by
  classical
  -- Left side is the number of permutations of `α`.
  rw [← Fintype.card_perm, ← Finset.card_univ]
  -- Partition permutations by their fixed-point finset.
  rw [Finset.card_eq_sum_card_fiberwise
        (t := (univ : Finset α).powerset)
        (f := fun σ : Perm α => univ.filter (fun x => σ x = x))
        (fun σ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
  -- Each fiber has `D(|α| − |S|)` elements.
  rw [Finset.sum_congr rfl (fun S _ => card_fixedPointFinset_fiber S)]
  -- Group subsets `S` of `univ` by their cardinality `k`.
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion, Finset.card_univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Inside the block of `k`-subsets, `|S| = i` is constant.
  rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2] :
        ∀ S ∈ powersetCard i univ,
          numDerangements (Fintype.card α - S.card)
            = numDerangements (Fintype.card α - i))]
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]

/-- **Fixed-point convolution identity over `ℕ`.**  For every `n`,
`n! = Σ_{k=0}^{n} C(n, k) · D(n − k)`. -/
theorem factorial_eq_sum_choose_mul_numDerangements (n : ℕ) :
    n ! = ∑ k ∈ range (n + 1), n.choose k * numDerangements (n - k) := by
  have h := card_perm_eq_sum_choose_mul_numDerangements (α := Fin n)
  simpa [Fintype.card_fin] using h

/-- Concrete instance `4! = 24 = 9 + 8 + 6 + 0 + 1`. -/
example :
    (4 : ℕ)! = ∑ k ∈ range 5, (4).choose k * numDerangements (4 - k) :=
  factorial_eq_sum_choose_mul_numDerangements 4

end DerangementsConvolution
