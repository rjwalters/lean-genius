import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Bijective witness for the weak-composition convolution

## What This Proves

The parent entry `StarsAndBarsWeakCompositionsOQ04.lean` proves the *cardinality*
convolution identity for weak compositions (`vandermonde_negBinomial`): the number
of weak compositions of `n` into `k₁ + k₂` parts equals the sum over all splits
`n = a + b` of the product of the counts into `k₁` and `k₂` parts. That is an
equality of *numbers*.

This entry upgrades it to an explicit **bijection** — a Lean `Equiv`:

  `{f : Fin (k₁+k₂) → ℕ // ∑ f = n}`
    `≃  Σ (a,b) ∈ antidiagonal n, {g : Fin k₁ → ℕ // ∑ g = a} × {h : Fin k₂ → ℕ // ∑ h = b}`.

The map is the honest combinatorial content of the convolution: a weak composition
of length `k₁ + k₂` **splits** at index `k₁` into its first `k₁` coordinates
`g = f ∘ castAdd` and its last `k₂` coordinates `h = f ∘ natAdd`; the pair of block
sums `(∑ g, ∑ h)` lands in `antidiagonal n` precisely because `∑ f = ∑ g + ∑ h`
(`Fin.sum_univ_add`). The inverse **concatenates** two blocks with `Fin.addCases`.
The round trips are the reconstruction identities `Fin.addCases_left` /
`Fin.addCases_right`.

Taking cardinalities of this `Equiv` (`card_weakComposition_convolution`) recovers
the parent's numerical convolution structurally, via `Fintype.card_sigma` and
`Fintype.card_prod` — turning a counting argument into a constructive one.

## What Mathlib has — and what this adds

Mathlib has `Fin.addCases`, `Fin.sum_univ_add`, `Finset.Nat.antidiagonal` and the
`Fintype.card_sigma` / `Fintype.card_prod` idiom, but no notion of weak compositions
and no split bijection for them. The new content is the explicit `Equiv`
`weakCompositionConvEquiv` and its cardinality corollary.
-/

open Finset

namespace StarsAndBars

/-- **The weak-composition split bijection.**

A weak composition of `n` into `k₁ + k₂` parts corresponds bijectively to a choice of
split `n = a + b` together with a weak composition of `a` into the first `k₁` parts
and a weak composition of `b` into the last `k₂` parts.

Forward (**split**): `f ↦ (f ∘ castAdd, f ∘ natAdd)` with fibre index the pair of block
sums `(∑ f∘castAdd, ∑ f∘natAdd)`, which lies in `antidiagonal n` by `Fin.sum_univ_add`.
Inverse (**concatenate**): glue the two blocks with `Fin.addCases`. -/
def weakCompositionConvEquiv (k₁ k₂ n : ℕ) :
    {f : Fin (k₁ + k₂) → ℕ // ∑ i, f i = n} ≃
      Σ ab : {p : ℕ × ℕ // p ∈ antidiagonal n},
        ({g : Fin k₁ → ℕ // ∑ i, g i = ab.1.1} ×
         {h : Fin k₂ → ℕ // ∑ i, h i = ab.1.2}) where
  toFun f :=
    ⟨⟨(∑ i, f.1 (Fin.castAdd k₂ i), ∑ i, f.1 (Fin.natAdd k₁ i)), by
        rw [mem_antidiagonal, ← Fin.sum_univ_add]; exact f.2⟩,
      (⟨fun i => f.1 (Fin.castAdd k₂ i), rfl⟩,
       ⟨fun i => f.1 (Fin.natAdd k₁ i), rfl⟩)⟩
  invFun s :=
    ⟨Fin.addCases (motive := fun _ => ℕ) s.2.1.1 s.2.2.1, by
        rw [Fin.sum_univ_add]
        simp only [Fin.addCases_left, Fin.addCases_right]
        rw [s.2.1.2, s.2.2.2]
        exact mem_antidiagonal.mp s.1.2⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext x
    refine Fin.addCases ?_ ?_ x
    · intro i; simp only [Fin.addCases_left]
    · intro i; simp only [Fin.addCases_right]
  right_inv := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, ⟨g, hg⟩, ⟨h, hh⟩⟩
    subst hg
    subst hh
    have hg' : (fun i => Fin.addCases (motive := fun _ => ℕ) g h (Fin.castAdd k₂ i)) = g := by
      funext i; simp only [Fin.addCases_left]
    have hh' : (fun i => Fin.addCases (motive := fun _ => ℕ) g h (Fin.natAdd k₁ i)) = h := by
      funext i; simp only [Fin.addCases_right]
    simp only [hg', hh']

/-- **Cardinality corollary: the convolution, structurally.**

Taking `Fintype.card` of `weakCompositionConvEquiv` recovers the numerical
convolution identity — the count of weak compositions of `n` into `k₁ + k₂` parts is
the antidiagonal sum of products of block counts — now derived from an explicit
bijection rather than a generating-function coefficient extraction. Combined with the
closed form `card_weakComposition`, this reproves the parent's
`vandermonde_negBinomial`. -/
theorem card_weakComposition_convolution (k₁ k₂ n : ℕ) :
    Fintype.card {f : Fin (k₁ + k₂) → ℕ // ∑ i, f i = n}
      = ∑ p ∈ antidiagonal n,
          Fintype.card {g : Fin k₁ → ℕ // ∑ i, g i = p.1}
            * Fintype.card {h : Fin k₂ → ℕ // ∑ i, h i = p.2} := by
  rw [Fintype.card_congr (weakCompositionConvEquiv k₁ k₂ n), Fintype.card_sigma]
  rw [Finset.sum_coe_sort (antidiagonal n)
    (fun p => Fintype.card ({g : Fin k₁ → ℕ // ∑ i, g i = p.1} ×
      {h : Fin k₂ → ℕ // ∑ i, h i = p.2}))]
  simp_rw [Fintype.card_prod]

end StarsAndBars
