/-
  Szemerédi Regularity Lemma — OQ-04: discharging the sharp-`2×2` split freshness
  from nonemptiness of the split pieces.

  `Packaging.lean` (S12) reduced the item-1 dichotomy obligation to a purely
  **constructive** one: build the refinement chain so that
  `parts (n+1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))`, with the four new
  blocks *pairwise distinct and fresh from* `R = parts n \ {A, B}`.  `isWitnessedSharpStep_of_split`
  still takes those ten freshness facts (six pairwise `≠`, four `∉ R`) as explicit hypotheses.

  This file removes them.  `split_freshness` derives all ten from two structural inputs that
  the outer loop already guarantees:

    * the partition `parts n` is **pairwise disjoint** (distinct blocks are `Disjoint` — the
      `hdisjoint` hypothesis threaded through `exists_afksTwoLevel_of_dichotomy`); and
    * the four split pieces `A₁, A₂, B₁, B₂` are **nonempty**.

  The mechanism is elementary: each piece is a nonempty subset of `A` (resp. `B`), and two
  distinct blocks of a partition are disjoint, so
    * within a block, `A₁ ∪ A₂ = A` disjoint with both nonempty forces `A₁ ≠ A₂`;
    * across blocks, a nonempty `X ⊆ A` cannot equal a `Y ⊆ B` (`A ∩ B = ∅`);
    * a nonempty `X ⊆ A` with `X ≠ A` cannot lie in `parts n` (it would be a block disjoint
      from `A` yet a nonempty subset of it), hence `X ∉ R`.

  `isWitnessedSharpStep_of_split_of_nonempty` then chains this with the S12 packaging: the full
  witnessed step follows from the split data, the mass floors, the gap, **and nonemptiness of the
  four pieces** — no freshness bookkeeping.  This is the exact shape the remaining constructive
  obligation (exhibiting the chain with nonempty split pieces) needs.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Packaging

namespace Szemeredi.RegularityOQ04Freshness

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04Packaging

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Split freshness from nonemptiness.**  Given two distinct blocks `A, B` of a pairwise
    disjoint partition `parts n`, a disjoint `2×2` split `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` whose
    four pieces are nonempty, the four new blocks are pairwise distinct and fresh from the
    canonical residual `R = ((parts n).erase A).erase B`.  Returned as the ten-fold conjunction
    consumed by `isWitnessedSharpStep_of_split`. -/
theorem split_freshness
    (parts : ℕ → Finset (Finset V)) (n : ℕ)
    (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂)
    (hA1 : A₁.Nonempty) (hA2 : A₂.Nonempty) (hB1 : B₁.Nonempty) (hB2 : B₂.Nonempty) :
    A₁ ≠ A₂ ∧ A₁ ≠ B₁ ∧ A₁ ≠ B₂ ∧ A₂ ≠ B₁ ∧ A₂ ≠ B₂ ∧ B₁ ≠ B₂ ∧
      A₁ ∉ ((parts n).erase A).erase B ∧ A₂ ∉ ((parts n).erase A).erase B ∧
      B₁ ∉ ((parts n).erase A).erase B ∧ B₂ ∉ ((parts n).erase A).erase B := by
  -- Each split piece is a subset of its block.
  have sA1 : A₁ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_left
  have sA2 : A₂ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_right
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  -- Cross-block: a nonempty `X ⊆ A` cannot equal a `Y ⊆ B` (blocks are disjoint).
  have cross : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → X.Nonempty → X ≠ Y := by
    intro X Y hX hY hXne h
    apply hXne.ne_empty
    have hXB : X ⊆ B := by rw [h]; exact hY
    have hsub : X ⊆ A ∩ B := Finset.subset_inter hX hXB
    have hAB0 : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hdisj A B hA hB hAB)
    rw [hAB0] at hsub; exact Finset.subset_empty.mp hsub
  -- Within a block: `X ∪ Y = C` disjoint with `Y` nonempty forces `X ≠ C`.
  have pieceNe : ∀ {X Y C : Finset V}, X ∪ Y = C → Disjoint X Y → Y.Nonempty → X ≠ C := by
    intro X Y C hU hd hYne h
    apply hYne.ne_empty
    have sY : Y ⊆ C := by rw [← hU]; exact Finset.subset_union_right
    have hsub : Y ⊆ X := by rw [h]; exact sY
    have hi : Y ∩ X = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd.symm
    rwa [Finset.inter_eq_left.mpr hsub] at hi
  -- Disjoint nonempty sets are distinct.
  have wNe : ∀ {X Y : Finset V}, Disjoint X Y → X.Nonempty → X ≠ Y := by
    intro X Y hd hXne h
    apply hXne.ne_empty
    have hi : X ∩ Y = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    rw [← h] at hi; simpa using hi
  -- A nonempty proper subset of a block is not itself a (distinct) block: `∉ R`.
  have core : ∀ {X C : Finset V}, X ⊆ C → C ∈ parts n → X ≠ C → X.Nonempty →
      X ∉ ((parts n).erase A).erase B := by
    intro X C hXC hCP hXneC hXne hmem
    have hXP : X ∈ parts n := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
    have hd : Disjoint X C := hdisj X C hXP hCP hXneC
    apply hXne.ne_empty
    have hi : X ∩ C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    rwa [Finset.inter_eq_left.mpr hXC] at hi
  -- Piece ≠ its own block (the other piece is nonempty).
  have hA1neA : A₁ ≠ A := pieceNe hsplitA hdA hA2
  have hA2neA : A₂ ≠ A := pieceNe (by rw [Finset.union_comm]; exact hsplitA) hdA.symm hA1
  have hB1neB : B₁ ≠ B := pieceNe hsplitB hdB hB2
  have hB2neB : B₂ ≠ B := pieceNe (by rw [Finset.union_comm]; exact hsplitB) hdB.symm hB1
  exact ⟨wNe hdA hA1, cross sA1 sB1 hA1, cross sA1 sB2 hA1, cross sA2 sB1 hA2,
    cross sA2 sB2 hA2, wNe hdB hB1,
    core sA1 hA hA1neA hA1, core sA2 hA hA2neA hA2,
    core sB1 hB hB1neB hB1, core sB2 hB hB2neB hB2⟩

/-- **Witnessed sharp step from the split + nonempty pieces (freshness-free).**  Combining
    `split_freshness` with `isWitnessedSharpStep_of_split`, the full `IsWitnessedSharpStep`
    follows from the split data (the shape of `parts (n+1)`, the disjoint `2×2` split, the mass
    floors, and the `eps`-gap) together with **nonemptiness of the four pieces** — the freshness
    side-conditions are discharged automatically.  This is the exact obligation the remaining
    constructive step of `exists_afksTwoLevel_of_dichotomy`'s dichotomy must meet. -/
theorem isWitnessedSharpStep_of_split_of_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hnext : parts (n + 1) =
      insert A₁ (insert A₂ (insert B₁ (insert B₂ (((parts n).erase A).erase B)))))
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂)
    (hA1 : A₁.Nonempty) (hA2 : A₂.Nonempty) (hB1 : B₁.Nonempty) (hB2 : B₂.Nonempty)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hgapA : eps * A.card ≤ (A₁.card : ℚ)) (hgapB : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep G parts n eps m := by
  obtain ⟨hA1A2, hA1B1, hA1B2, hA2B1, hA2B2, hB1B2, hA1R, hA2R, hB1R, hB2R⟩ :=
    split_freshness parts n A B A₁ A₂ B₁ B₂ hA hB hAB hdisj hsplitA hsplitB hdA hdB
      hA1 hA2 hB1 hB2
  exact isWitnessedSharpStep_of_split G parts n eps m A B A₁ A₂ B₁ B₂
    hA hB hAB hnext hsplitA hsplitB hdA hdB
    hA1A2 hA1B1 hA1B2 hA2B1 hA2B2 hB1B2 hA1R hA2R hB1R hB2R
    hmA hmB hgapA hgapB hgap

end Szemeredi.RegularityOQ04Freshness
