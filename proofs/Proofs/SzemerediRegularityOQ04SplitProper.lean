/-
  Szemerédi Regularity Lemma — OQ-04: the density gap forces a *nontrivial* split.

  `MassFloor.lean` (S14) shrank the item-1 dichotomy's constructive obligation to
  the two nonemptiness facts the mass floors do NOT reach — the complement pieces
  `A₂ = A ∖ A₁`, `B₂ = B ∖ B₁` of the sharp `2×2` split.  The mass floors
  `eps·|A| ≤ |A₁|` pin the *deviating corner* `A₁, B₁` from below but say nothing
  about whether `A₁` exhausts `A` (`A₂ = ∅`).  State (S14):

    "A₂, B₂ nonemptiness is the properness content `A₁ ⊊ A` … which the flat mass
     floor alone does not see."

  This file supplies what the *analytic* data — the `eps`-density gap — genuinely
  does force: the split cannot be **doubly** trivial.  If both complement pieces
  were empty then `A₁ = A` and `B₁ = B`, so the deviating corner `(A₁, B₁)` would
  coincide with the parent pair `(A, B)` and its density deviation
  `|d(A₁,B₁) − d(A,B)|` would be `0` — contradicting the `eps`-gap for `eps > 0`.

  * `gap_forces_complement_nonempty` — split shape + `0 < eps` + the `eps`-gap ⟹
    `A₂.Nonempty ∨ B₂.Nonempty`.  Purely elementary: a `by_contra` collapses both
    empties into `A₁ = A`, `B₁ = B`, and the gap becomes `eps ≤ 0`.

  * `exists_sharp_split_nontrivial_of_not_afksFineRegular` — reruns
    `exists_sharp_split_of_not_afksFineRegular` (Dichotomy, S11) and appends the
    disjunction, so the extracted sharp split is certified to split at least one
    parent block properly whenever the fine tolerance `E` is positive.

  What this leaves: the *symmetric* both-pieces-nonempty demand of
  `isWitnessedSharpStep_of_split_of_gap` is genuinely NOT met by the analytic data
  — when one corner exhausts its block (say `A₁ = A`) the honest refinement is the
  asymmetric 3-piece split `{A, B₁, B₂}`, not the 4-piece `{A₁, A₂, B₁, B₂}`.
  Certifying that degenerate branch needs an asymmetric witnessed-step packaging,
  not a further nonemptiness lemma.  This lemma pins the residual to exactly that
  one degenerate side.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Dichotomy

namespace Szemeredi.RegularityOQ04SplitProper

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Dichotomy
  Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The density gap forbids a doubly-trivial split.**  Given a disjoint `2×2`
    split `A₁ ∪ A₂ = A`, `B₁ ∪ B₂ = B` whose deviating corner `(A₁, B₁)` differs
    in density from the parent pair `(A, B)` by at least `eps > 0`, at least one
    complement piece is nonempty: `A₂.Nonempty ∨ B₂.Nonempty`.

    If both were empty then `A₁ = A` and `B₁ = B`, so
    `edgeDensity G A₁ B₁ = edgeDensity G A B` and the gap `eps ≤ 0` — impossible. -/
theorem gap_forces_complement_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A₁ A₂ B₁ B₂ : Finset V} {eps : ℚ}
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (heps : 0 < eps)
    (hgap : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    A₂.Nonempty ∨ B₂.Nonempty := by
  by_contra h
  push_neg at h
  obtain ⟨hA2e, hB2e⟩ := h
  have hAeq : A₁ = A := by rw [← hsplitA, hA2e, Finset.union_empty]
  have hBeq : B₁ = B := by rw [← hsplitB, hB2e, Finset.union_empty]
  rw [hAeq, hBeq, sub_self, abs_zero] at hgap
  exact absurd hgap (not_le.mpr heps)

/-- **Extracted sharp split splits at least one block properly.**  The S11
    `exists_sharp_split_of_not_afksFineRegular` witness, augmented (for `0 < E`)
    with `A₂.Nonempty ∨ B₂.Nonempty` via `gap_forces_complement_nonempty`.  So a
    fine partition failing AFKS-fine-regularity yields a sharp `2×2` split in which
    the deviating corner does not exhaust *both* parent blocks. -/
theorem exists_sharp_split_nontrivial_of_not_afksFineRegular
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε E : ℚ) (hε : 0 ≤ ε) (hE : 0 < E)
    (parts : Finset (Finset V))
    (hequit : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1)
    (hnot : ¬ IsAFKSFineRegular G ε E parts) :
    ∃ A B A₁ A₂ B₁ B₂ : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧
      A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
      E * A.card ≤ (A₁.card : ℚ) ∧ E * B.card ≤ (B₁.card : ℚ) ∧
      E ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B| ∧
      (A₂.Nonempty ∨ B₂.Nonempty) := by
  obtain ⟨A, B, A₁, A₂, B₁, B₂, hA, hB, hAB, hsA, hsB, hdA, hdB,
    hmA, hmB, hgap⟩ :=
    exists_sharp_split_of_not_afksFineRegular G ε E hε parts hequit hnot
  exact ⟨A, B, A₁, A₂, B₁, B₂, hA, hB, hAB, hsA, hsB, hdA, hdB, hmA, hmB, hgap,
    gap_forces_complement_nonempty G hsA hsB hE hgap⟩

end Szemeredi.RegularityOQ04SplitProper
