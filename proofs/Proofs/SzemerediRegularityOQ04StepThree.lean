/-
  Szemerédi Regularity Lemma — OQ-04: the asymmetric 3-piece witnessed step.

  `SplitProper.lean` (S16) showed the `E`-density gap forbids a *doubly* trivial
  sharp `2×2` split (`gap_forces_complement_nonempty`), and pinned the residual of
  the item-1 dichotomy to exactly one degenerate side: when the deviating corner
  exhausts one parent block (say `A₁ = A`), the honest refinement is the
  **asymmetric 3-piece split** `{A, B₁, B₂}` — the 4-piece packaging
  `IsWitnessedSharpStep` cannot fire because `A₂ = ∅` violates its freshness
  clauses (`A₁ ≠ A₂` would force a nonempty complement).

  This file supplies the S17 layer for that degenerate side:

  * `IsWitnessedSharpStep3` — the 3-piece analogue of `Outer.lean`'s
    `IsWitnessedSharpStep`: `parts n = insert A (insert B R)`,
    `parts (n+1) = insert A (insert B₁ (insert B₂ R))` (only `B` splits), with the
    disjoint-split shape, the nested freshness clauses, the coarse mass floors
    `m ≤ |A|, |B|`, the `eps`-mass floor on the deviating piece `B₁`, and the
    `eps`-density gap `eps ≤ |d(A,B₁) − d(A,B)|`.

  * `isWitnessedSharpStep3_of_split` — the packaging lemma, mirroring
    `Packaging.lean`: the canonical residual `R := ((parts n).erase A).erase B` is
    built here, the coarse-side freshnesses derived, and the nested-insert
    freshnesses reduced to flat pairwise-`≠` / `∉ R` data.

  * `exists_proper_or_semitrivial_split_of_not_afksFineRegular` — the case split
    the S16 file called for, at the split-data level: a non-AFKS-fine-regular
    equitable partition yields **either** a sharp `2×2` split whose complement
    pieces are BOTH nonempty (the symmetric 4-piece branch, now with genuinely
    proper splits on both blocks), **or** 3-piece-shaped data: two distinct parts
    `A, B` and a proper split `B = B₁ ∪ B₂` (`B₂ ≠ ∅`) with the `E`-mass floor on
    `B₁` and the `E`-gap `E ≤ |d(A,B₁) − d(A,B)|`.  The `B₂ = ∅` degenerate side
    is *normalized* onto the same 3-piece shape by swapping the roles of `A` and
    `B` via `edgeDensity_symm` — so ONE asymmetric predicate covers both
    degenerate sides.

  What this leaves (recorded in state): the energy content of the 3-piece step —
  the one-sided defect inequality (splitting only `B` with a `≥ eps` deviation on
  a `≥ eps·|B|` mass piece gains `≥ eps³·|A||B|/n²` energy, mean preserved since
  `e(A,B) = e(A,B₁) + e(A,B₂)`) — and threading both step shapes through the
  outer-loop chain construction.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04SplitProper
import Proofs.SzemerediCoreOQ01

namespace Szemeredi.RegularityOQ04StepThree

open Classical Szemeredi.Core Szemeredi.EnergyIncrement
  Szemeredi.RegularityOQ04Dichotomy Szemeredi.RegularityOQ04ToleranceBridge
  Szemeredi.RegularityOQ04SplitProper

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The asymmetric 3-piece witnessed step.**  The step `parts n → parts (n+1)`
    keeps the block `A` intact and splits only `B` into `B₁ ∪ B₂`, with the
    deviating piece `B₁` carrying the `eps`-mass floor and the `eps`-density gap
    against the parent pair `(A, B)`.  This is the honest refinement shape for the
    degenerate side of the sharp `2×2` dichotomy, where the deviating corner
    exhausts one parent block (`SplitProper.lean`, S16). -/
def IsWitnessedSharpStep3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ) : Prop :=
  ∃ R : Finset (Finset V), ∃ A B B₁ B₂ : Finset V,
    parts n = insert A (insert B R) ∧
    parts (n + 1) = insert A (insert B₁ (insert B₂ R)) ∧
    B₁ ∪ B₂ = B ∧ Disjoint B₁ B₂ ∧
    A ∉ insert B R ∧ B ∉ R ∧
    A ∉ insert B₁ (insert B₂ R) ∧ B₁ ∉ insert B₂ R ∧ B₂ ∉ R ∧
    m ≤ (A.card : ℚ) ∧ m ≤ (B.card : ℚ) ∧
    eps * B.card ≤ (B₁.card : ℚ) ∧
    eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|

/-- **Packaging the 3-piece split into a witnessed step.**  Mirrors
    `Packaging.isWitnessedSharpStep_of_split`: given two distinct parts
    `A, B ∈ parts n`, the refinement value at `n+1` over the canonical residual
    `R := ((parts n).erase A).erase B`, the disjoint split of `B` only, the flat
    freshness data (`A, B₁, B₂` pairwise distinct, `B₁, B₂ ∉ R`), the coarse mass
    floors, the `eps`-mass floor on `B₁`, and the `eps`-gap, the step is a
    witnessed 3-piece step.  The residual construction, the coarse-side
    freshnesses, and the nested-insert reductions are done here, once. -/
theorem isWitnessedSharpStep3_of_split
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hnext : parts (n + 1) =
      insert A (insert B₁ (insert B₂ (((parts n).erase A).erase B))))
    (hsplitB : B₁ ∪ B₂ = B) (hdB : Disjoint B₁ B₂)
    (hAB1 : A ≠ B₁) (hAB2 : A ≠ B₂) (hB1B2 : B₁ ≠ B₂)
    (hB1R : B₁ ∉ ((parts n).erase A).erase B)
    (hB2R : B₂ ∉ ((parts n).erase A).erase B)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hfloor : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep3 G parts n eps m := by
  set R := ((parts n).erase A).erase B with hR
  have hBeR : B ∈ (parts n).erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hpartsn : parts n = insert A (insert B R) := by
    rw [hR, Finset.insert_erase hBeR, Finset.insert_erase hA]
  have hBR : B ∉ R := by rw [hR]; exact Finset.notMem_erase B _
  have hAR : A ∉ R := fun h =>
    Finset.notMem_erase A (parts n) (Finset.mem_of_mem_erase h)
  have hAinsBR : A ∉ insert B R := by
    rw [Finset.mem_insert]; push_neg; exact ⟨hAB, hAR⟩
  refine ⟨R, A, B, B₁, B₂, hpartsn, hnext, hsplitB, hdB, hAinsBR, hBR, ?_, ?_,
    hB2R, hmA, hmB, hfloor, hgap⟩
  · -- `A ∉ insert B₁ (insert B₂ R)`
    simp only [Finset.mem_insert]; push_neg
    exact ⟨hAB1, hAB2, hAR⟩
  · -- `B₁ ∉ insert B₂ R`
    simp only [Finset.mem_insert]; push_neg
    exact ⟨hB1B2, hB1R⟩

/-- **The dichotomy case split: proper `2×2` or normalized 3-piece data.**  From a
    non-AFKS-fine-regular equitable partition, `SplitProper` (S16) extracts a sharp
    `2×2` split in which at least one complement piece is nonempty.  Splitting on
    which, this theorem yields **either** the symmetric branch — the full `2×2`
    split data with BOTH complement pieces nonempty (so both parent blocks split
    properly and the 4-piece `IsWitnessedSharpStep` freshness clauses are
    satisfiable) — **or** the asymmetric branch in the normalized 3-piece shape of
    `IsWitnessedSharpStep3`: distinct parts `A, B ∈ parts`, a proper split
    `B = B₁ ∪ B₂` with `B₂ ≠ ∅`, the `E`-mass floor on `B₁`, and the `E`-gap
    `E ≤ |d(A,B₁) − d(A,B)|`.

    The two degenerate sides are folded into ONE shape: if `A₂ = ∅` then `A₁ = A`
    and the gap already reads `|d(A,B₁) − d(A,B)|`; if `B₂ = ∅` then `B₁ = B`, and
    swapping the roles of the parents via `edgeDensity_symm` turns
    `|d(A₁,B) − d(A,B)|` into `|d(B,A₁) − d(B,A)|`, i.e. the same 3-piece shape
    with `(A,B,B₁,B₂) := (B,A,A₁,A₂)`. -/
theorem exists_proper_or_semitrivial_split_of_not_afksFineRegular
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε E : ℚ) (hε : 0 ≤ ε) (hE : 0 < E)
    (parts : Finset (Finset V))
    (hequit : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1)
    (hnot : ¬ IsAFKSFineRegular G ε E parts) :
    (∃ A B A₁ A₂ B₁ B₂ : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧
      A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
      E * A.card ≤ (A₁.card : ℚ) ∧ E * B.card ≤ (B₁.card : ℚ) ∧
      E ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B| ∧
      A₂.Nonempty ∧ B₂.Nonempty) ∨
    (∃ A B B₁ B₂ : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧
      B₁ ∪ B₂ = B ∧ Disjoint B₁ B₂ ∧
      E * B.card ≤ (B₁.card : ℚ) ∧
      E ≤ |edgeDensity G A B₁ - edgeDensity G A B| ∧
      B₂.Nonempty) := by
  obtain ⟨A, B, A₁, A₂, B₁, B₂, hA, hB, hAB, hsA, hsB, hdA, hdB,
    hmA, hmB, hgap, hnontriv⟩ :=
    exists_sharp_split_nontrivial_of_not_afksFineRegular G ε E hε hE
      parts hequit hnot
  rcases Finset.eq_empty_or_nonempty A₂ with hA2e | hA2ne
  · -- `A₂ = ∅`: `A₁ = A`, only `B` splits; already in the 3-piece shape.
    have hB2ne : B₂.Nonempty := by
      rcases hnontriv with h | h
      · rw [hA2e] at h; exact absurd h Finset.not_nonempty_empty
      · exact h
    have hA1A : A₁ = A := by rw [← hsA, hA2e, Finset.union_empty]
    rw [hA1A] at hgap
    exact Or.inr ⟨A, B, B₁, B₂, hA, hB, hAB, hsB, hdB, hmB, hgap, hB2ne⟩
  · rcases Finset.eq_empty_or_nonempty B₂ with hB2e | hB2ne
    · -- `B₂ = ∅`: `B₁ = B`, only `A` splits; normalize by swapping the parents.
      have hB1B : B₁ = B := by rw [← hsB, hB2e, Finset.union_empty]
      rw [hB1B] at hgap
      have hgap' : E ≤ |edgeDensity G B A₁ - edgeDensity G B A| := by
        rwa [edgeDensity_symm G B A₁, edgeDensity_symm G B A]
      exact Or.inr ⟨B, A, A₁, A₂, hB, hA, hAB.symm, hsA, hdA, hmA, hgap', hA2ne⟩
    · -- both complement pieces nonempty: the genuinely proper `2×2` branch.
      exact Or.inl ⟨A, B, A₁, A₂, B₁, B₂, hA, hB, hAB, hsA, hsB, hdA, hdB,
        hmA, hmB, hgap, hA2ne, hB2ne⟩

end Szemeredi.RegularityOQ04StepThree
