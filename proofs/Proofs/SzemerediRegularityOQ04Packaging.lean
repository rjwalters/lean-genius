/-
  Szemerédi Regularity Lemma — OQ-04: packaging the sharp `2×2` split into
  `IsWitnessedSharpStep`.

  S11 (`Dichotomy.lean`) discharged the **analytic realizability core** of the
  regular-or-refine dichotomy: `exists_sharp_split_of_not_afksFineRegular` produces,
  from a non-AFKS-fine-regular equitable partition, two distinct parts `A, B` and a
  disjoint `2×2` split `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` realizing the `E`-mass floors and
  the `E`-density gap — exactly the *quantitative* clauses of `IsWitnessedSharpStep`
  (`Outer.lean`).

  What separated that from the full witness (the item-1 dichotomy hypothesis of
  `exists_afksTwoLevel_of_dichotomy`) was the **chain-and-freshness packaging**: writing
  `parts n = insert A (insert B R)` and
  `parts (n+1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))` together with all the
  nested `∉` freshness side-conditions.  `state.md` (S11) records this as the residual
  "combinatorial not analytic" piece.

  This file discharges the reusable half of that bookkeeping.
  `isWitnessedSharpStep_of_split` takes the split data together with the **flat**
  side-conditions — the refinement value at `n+1` over the *canonical* residual
  `R := parts n \ {A, B}` (double `erase`); the six pairwise distinctnesses of the four
  new blocks; their four `∉ R` freshnesses; and the two mass floors and the gap — and
  produces the full `IsWitnessedSharpStep`.  The residual-`R` construction, the two
  coarse-side freshnesses (`A ∉ insert B R`, `B ∉ R`), and the reduction of the three
  nested-insert freshnesses to the flat pairwise/`∉ R` form are done here, once.

  Net effect: the remaining open piece of the dichotomy becomes a purely **constructive**
  obligation — build the refinement chain so that `parts (n+1)` has the stated `insert…`
  shape and the four new blocks are pairwise distinct and fresh from `R` — with no further
  nested-membership wrangling.  The mathematics (that such a split with its mass floors and
  gap exists) is already closed by S11; what remains is exhibiting the chain.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Outer

namespace Szemeredi.RegularityOQ04Packaging

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Outer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Packaging the sharp `2×2` split into a witnessed step.**  Given the split data of
    `exists_sharp_split_of_not_afksFineRegular` (two distinct parts `A, B ∈ parts n` and a
    disjoint split `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` with the mass floors and the `eps`-gap),
    the refinement value `parts (n+1)` over the canonical residual `R = parts n \ {A, B}`,
    and the *flat* freshness data (the four new blocks pairwise distinct and each `∉ R`),
    the step `parts n → parts (n+1)` is a witnessed sharp `2×2` step.

    The residual `R := ((parts n).erase A).erase B` is built here, the coarse-side
    freshnesses `A ∉ insert B R` and `B ∉ R` are derived, and the nested-insert freshnesses
    are reduced to the supplied pairwise-`≠`/`∉ R` facts. -/
theorem isWitnessedSharpStep_of_split
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hnext : parts (n + 1) =
      insert A₁ (insert A₂ (insert B₁ (insert B₂ (((parts n).erase A).erase B)))))
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂)
    (hA1A2 : A₁ ≠ A₂) (hA1B1 : A₁ ≠ B₁) (hA1B2 : A₁ ≠ B₂)
    (hA2B1 : A₂ ≠ B₁) (hA2B2 : A₂ ≠ B₂) (hB1B2 : B₁ ≠ B₂)
    (hA1R : A₁ ∉ ((parts n).erase A).erase B)
    (hA2R : A₂ ∉ ((parts n).erase A).erase B)
    (hB1R : B₁ ∉ ((parts n).erase A).erase B)
    (hB2R : B₂ ∉ ((parts n).erase A).erase B)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hgapA : eps * A.card ≤ (A₁.card : ℚ)) (hgapB : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep G parts n eps m := by
  set R := ((parts n).erase A).erase B with hR
  -- `parts n = insert A (insert B R)` and the two coarse-side freshnesses.
  have hBeR : B ∈ (parts n).erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hpartsn : parts n = insert A (insert B R) := by
    rw [hR, Finset.insert_erase hBeR, Finset.insert_erase hA]
  have hBR : B ∉ R := by rw [hR]; exact Finset.notMem_erase B _
  have hAR : A ∉ R := fun h => Finset.notMem_erase A (parts n) (Finset.mem_of_mem_erase h)
  have hAinsBR : A ∉ insert B R := by
    rw [Finset.mem_insert]; push_neg; exact ⟨hAB, hAR⟩
  refine ⟨R, A, B, A₁, A₂, B₁, B₂, hpartsn, hnext, hsplitA, hsplitB, hdA, hdB,
    hAinsBR, hBR, ?_, ?_, ?_, hB2R, hmA, hmB, hgapA, hgapB, hgap⟩
  · -- `A₁ ∉ insert A₂ (insert B₁ (insert B₂ R))`
    simp only [Finset.mem_insert]; push_neg
    exact ⟨hA1A2, hA1B1, hA1B2, hA1R⟩
  · -- `A₂ ∉ insert B₁ (insert B₂ R)`
    simp only [Finset.mem_insert]; push_neg
    exact ⟨hA2B1, hA2B2, hA2R⟩
  · -- `B₁ ∉ insert B₂ R`
    simp only [Finset.mem_insert]; push_neg
    exact ⟨hB1B2, hB1R⟩

end Szemeredi.RegularityOQ04Packaging
