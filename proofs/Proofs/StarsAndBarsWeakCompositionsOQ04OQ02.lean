import Mathlib
import Proofs.StarsAndBarsWeakCompositions

/-
# The bijective witness behind the weak-composition convolution

## What This Proves

The sibling entry `StarsAndBarsWeakCompositionsOQ04.lean` derives the convolution
law of weak-composition counts

  `∑_{i+j=n} C(i+k₁−1, i) · C(j+k₂−1, j) = C(n+k₁+k₂−1, n)`

*algebraically*, by reading off the `n`-th coefficient of the generating-function
identity `W(k₁)·W(k₂) = W(k₁+k₂)`. That proof establishes the numbers are equal but
does not exhibit the underlying bijection.

This entry supplies the **explicit bijection**. A weak composition of `n` into
`k₁ + k₂` parts is a tuple `f : Fin (k₁+k₂) → ℕ` with `∑ i, f i = n`. Splitting the
tuple at index `k₁` — the first `k₁` coordinates `f ∘ castAdd` and the last `k₂`
coordinates `f ∘ natAdd` — sets up a bijection

  `{f : Fin (k₁+k₂) → ℕ // ∑ f = n}
      ≃ Σ p ∈ antidiagonal n,
          ({g : Fin k₁ → ℕ // ∑ g = p.1} × {h : Fin k₂ → ℕ // ∑ h = p.2})`

(`weakCompositionSigmaEquiv`). Taking cardinalities of both sides *reproves the
convolution combinatorially* (`card_weakComposition_split`): the count on the left
is `C(n+k₁+k₂−1, n)` and each fibre contributes `C(i+k₁−1, i)·C(j+k₂−1, j)`.

## The construction

The engine is the "split at index `k₁`" arrow bijection

  `splitArrow : (Fin (k₁+k₂) → ℕ) ≃ (Fin k₁ → ℕ) × (Fin k₂ → ℕ)`,

assembled from `finSumFinEquiv` and `Equiv.sumArrowEquivProdArrow`, together with
the sum-splitting identity `sum_split :
  (∑ i, f (castAdd i)) + (∑ i, f (natAdd i)) = ∑ i, f i`. Carrying the constraint
`∑ f = n` through `Equiv.subtypeEquiv` gives the pair form
`weakCompositionSplitEquiv`; fibering the pair form over the partial sums
`(∑ g, ∑ h)` with `Equiv.sigmaFiberEquiv` gives the antidiagonal-indexed sigma form.

## What Mathlib has — and what this adds

Mathlib has `finSumFinEquiv`, `Equiv.sumArrowEquivProdArrow`, `Equiv.sigmaFiberEquiv`
and the `antidiagonal`, but no weak compositions and no split bijection. The new
content is the explicit `Equiv` witnessing the negative-binomial Vandermonde
convolution of the parent, and its cardinality reading.
-/

open Finset Equiv

namespace StarsAndBars

variable (k₁ k₂ : ℕ)

/-- **Split at index `k₁`.** The bijection between tuples on `Fin (k₁+k₂)` and pairs
of tuples on `Fin k₁` and `Fin k₂`, cutting a tuple into its first `k₁` and last `k₂`
coordinates. Assembled from `finSumFinEquiv` and `Equiv.sumArrowEquivProdArrow`. -/
def splitArrow : (Fin (k₁ + k₂) → ℕ) ≃ (Fin k₁ → ℕ) × (Fin k₂ → ℕ) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl ℕ)).trans
    (Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) ℕ)

@[simp]
theorem splitArrow_apply_fst (f : Fin (k₁ + k₂) → ℕ) (i : Fin k₁) :
    (splitArrow k₁ k₂ f).1 i = f (Fin.castAdd k₂ i) := by
  simp [splitArrow, Equiv.arrowCongr_apply]

@[simp]
theorem splitArrow_apply_snd (f : Fin (k₁ + k₂) → ℕ) (i : Fin k₂) :
    (splitArrow k₁ k₂ f).2 i = f (Fin.natAdd k₁ i) := by
  simp [splitArrow, Equiv.arrowCongr_apply]

/-- **Sum-splitting identity.** The total of a tuple over `Fin (k₁+k₂)` is the total
of its first `k₁` coordinates plus the total of its last `k₂` coordinates. -/
theorem sum_split (f : Fin (k₁ + k₂) → ℕ) :
    (∑ i, f (Fin.castAdd k₂ i)) + (∑ i, f (Fin.natAdd k₁ i)) = ∑ i, f i := by
  rw [← Equiv.sum_comp finSumFinEquiv f, Fintype.sum_sum_type]
  simp

/-- **Split bijection, pair form.** Weak compositions of `n` into `k₁ + k₂` parts
correspond to pairs of tuples whose totals add to `n`: cut the tuple at index `k₁`. -/
def weakCompositionSplitEquiv (n : ℕ) :
    {f : Fin (k₁ + k₂) → ℕ // ∑ i, f i = n}
      ≃ {gh : (Fin k₁ → ℕ) × (Fin k₂ → ℕ) // (∑ i, gh.1 i) + (∑ i, gh.2 i) = n} :=
  (splitArrow k₁ k₂).subtypeEquiv (fun f => by
    simp only [splitArrow_apply_fst, splitArrow_apply_snd]
    rw [sum_split])

/-- The partial-sum map from the pair form to the antidiagonal of `n`:
`(g, h) ↦ (∑ g, ∑ h)`, which lands in `antidiagonal n` exactly when the totals
add to `n`. -/
def splitToAntidiagonal (n : ℕ) :
    {gh : (Fin k₁ → ℕ) × (Fin k₂ → ℕ) // (∑ i, gh.1 i) + (∑ i, gh.2 i) = n} →
      {p : ℕ × ℕ // p ∈ Finset.antidiagonal n} :=
  fun gh => ⟨(∑ i, gh.1.1 i, ∑ i, gh.1.2 i), by
    rw [Finset.mem_antidiagonal]; exact gh.2⟩

/-- **Fibre of the partial-sum map.** Over a fixed split `p = (p₁, p₂)` of `n`, the
pairs `(g, h)` with `(∑ g, ∑ h) = p` are exactly the pairs of tuples with `∑ g = p₁`
and `∑ h = p₂`. -/
def fibreEquiv (n : ℕ) (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n}) :
    {gh : {gh : (Fin k₁ → ℕ) × (Fin k₂ → ℕ) // (∑ i, gh.1 i) + (∑ i, gh.2 i) = n} //
        splitToAntidiagonal k₁ k₂ n gh = p}
      ≃ ({g : Fin k₁ → ℕ // ∑ i, g i = (p : ℕ × ℕ).1} ×
         {h : Fin k₂ → ℕ // ∑ i, h i = (p : ℕ × ℕ).2}) where
  toFun := fun t => by
    -- `splitToAntidiagonal … = p` says `(∑ g, ∑ h) = p.val`.
    have hval : ((∑ i, t.1.1.1 i, ∑ i, t.1.1.2 i) : ℕ × ℕ) = (p : ℕ × ℕ) :=
      congrArg Subtype.val t.2
    exact (⟨t.1.1.1, (Prod.ext_iff.mp hval).1⟩, ⟨t.1.1.2, (Prod.ext_iff.mp hval).2⟩)
  invFun := fun gh =>
    ⟨⟨(gh.1.1, gh.2.1), by
        rw [gh.1.2, gh.2.2]; exact Finset.mem_antidiagonal.mp p.2⟩, by
      apply Subtype.ext
      show ((∑ i, gh.1.1 i, ∑ i, gh.2.1 i) : ℕ × ℕ) = (p : ℕ × ℕ)
      rw [gh.1.2, gh.2.2]⟩
  left_inv := by rintro ⟨⟨⟨g, h⟩, hgh⟩, hσ⟩; rfl
  right_inv := by rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩; rfl

/-- **Split bijection, sigma form.** Weak compositions of `n` into `k₁ + k₂` parts
are in explicit bijection with the disjoint union, over all splits `n = p₁ + p₂`, of
pairs of weak compositions of `p₁` into `k₁` parts and `p₂` into `k₂` parts. This is
the bijective witness behind the negative-binomial Vandermonde convolution. -/
def weakCompositionSigmaEquiv (n : ℕ) :
    {f : Fin (k₁ + k₂) → ℕ // ∑ i, f i = n}
      ≃ Σ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n},
          ({g : Fin k₁ → ℕ // ∑ i, g i = (p : ℕ × ℕ).1} ×
           {h : Fin k₂ → ℕ // ∑ i, h i = (p : ℕ × ℕ).2}) :=
  (weakCompositionSplitEquiv k₁ k₂ n).trans
    (((Equiv.sigmaFiberEquiv (splitToAntidiagonal k₁ k₂ n)).symm).trans
      (Equiv.sigmaCongrRight (fibreEquiv k₁ k₂ n)))

/-- **Cardinality reading: the convolution, combinatorially.** Taking the
cardinality of `weakCompositionSigmaEquiv` recovers the negative-binomial
Vandermonde convolution of the parent, now as a genuine bijective count:

  `#{f : Fin (k₁+k₂) → ℕ // ∑ f = n}
      = ∑_{(p₁,p₂) ∈ antidiagonal n}
          #{g : Fin k₁ → ℕ // ∑ g = p₁} · #{h : Fin k₂ → ℕ // ∑ h = p₂}`. -/
theorem card_weakComposition_split (n : ℕ) :
    Fintype.card {f : Fin (k₁ + k₂) → ℕ // ∑ i, f i = n}
      = ∑ p ∈ Finset.antidiagonal n,
          Fintype.card {g : Fin k₁ → ℕ // ∑ i, g i = p.1}
          * Fintype.card {h : Fin k₂ → ℕ // ∑ i, h i = p.2} := by
  rw [Fintype.card_congr (weakCompositionSigmaEquiv k₁ k₂ n), Fintype.card_sigma]
  rw [← Finset.sum_coe_sort (Finset.antidiagonal n)
    (fun p => Fintype.card {g : Fin k₁ → ℕ // ∑ i, g i = p.1}
      * Fintype.card {h : Fin k₂ → ℕ // ∑ i, h i = p.2})]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.card_prod]

end StarsAndBars
