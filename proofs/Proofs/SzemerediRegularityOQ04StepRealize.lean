/-
  Szemerédi Regularity Lemma — OQ-04: the single-step realization (S20).

  The outer AFKS loop (`exists_afksTwoLevel_of_dichotomy`, and its two-shape
  refinement in the S19 layer) consumes a *chain* `parts : ℕ → Finset (Finset V)`
  together with the regular-or-refine dichotomy: whenever `parts n` fails to be
  AFKS-fine-regular, the step `parts n → parts (n+1)` is a witnessed sharp step
  (symmetric 4-piece `IsWitnessedSharpStep` or asymmetric 3-piece
  `IsWitnessedSharpStep3`).  The S17 case split
  (`exists_proper_or_semitrivial_split_of_not_afksFineRegular`) produces the raw
  *split data* for a non-fine-regular partition, but nobody had yet shown that this
  data can be **realized** as an actual successor partition — the induction-step
  brick of the still-open recursive chain construction.

  This file supplies that brick, in three layers:

  * **3-piece freshness/nonemptiness capstones** — the missing mirror of the
    S13/S14 ladder for the asymmetric shape.  `split_freshness3` derives the five
    flat freshness side-conditions of `isWitnessedSharpStep3_of_split` from
    pairwise disjointness of the ambient partition plus nonemptiness of the two
    split pieces; `isWitnessedSharpStep3_of_split_of_nonempty` and
    `isWitnessedSharpStep3_of_split_of_gap` then package the witnessed 3-piece
    step from pure split data (the `eps`-mass floor supplying `B₁.Nonempty`
    exactly as in the 4-piece S14 capstone).

  * **Partition-invariant maintenance** — the refined family (either shape) is
    again a genuine partition: it covers the vertices (`refined4_cover`,
    `refined3_cover`), is pairwise disjoint (`refined4_disjoint`,
    `refined3_disjoint`), and refines every coarse partition the parent refines
    (`refined4_refines`, `refined3_refines`).  These are the invariants
    (`hcover`, `hdisjoint`, `href`) that the outer loop demands of every term of
    the chain.

  * **The single-step realization** —
    `exists_witnessed_next_of_not_afksFineRegular`: an equitable, pairwise
    disjoint, covering partition with per-part mass floor `m` that is *not*
    AFKS-fine-regular admits a concrete successor partition `q'` which (i)
    covers, (ii) is pairwise disjoint, (iii) refines whatever the parent
    refines, and (iv) makes ANY chain passing through `q, q'` at steps
    `n, n+1` a witnessed sharp step (4-piece or 3-piece).  This is precisely
    the statement the recursive chain construction (`Classical.choose` +
    `Nat.rec`) must invoke at each non-regular step.

  What this leaves (the standing deep blocker, recorded in state): iterating the
  step — the recursion must maintain the *equitability* and *mass-floor*
  hypotheses across steps, which splitting alone destroys; that is the classical
  re-equitization bookkeeping ("nonempty-equipartition model" blocker in
  `Assembly.lean`).  The set-theoretic and analytic content of a single step is,
  with this file, fully discharged.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04StepThree
import Proofs.SzemerediRegularityOQ04MassFloor
import Proofs.SzemerediRegularityOQ04TwoLevel
import Proofs.SzemerediRegularityOQ04Fresh

namespace Szemeredi.RegularityOQ04StepRealize

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04StepThree Szemeredi.RegularityOQ04MassFloor
  Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge
  Szemeredi.RegularityOQ04Fresh

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: 3-PIECE FRESHNESS FROM NONEMPTINESS (the S13 mirror)
-- ═══════════════════════════════════════════════════════════════════

/-- **3-piece split freshness from nonemptiness.**  Given two distinct blocks
    `A, B` of a pairwise disjoint partition `parts n` and a disjoint split
    `B = B₁ ∪ B₂` with both pieces nonempty, the five flat freshness
    side-conditions of `isWitnessedSharpStep3_of_split` hold: `A, B₁, B₂` are
    pairwise distinct and `B₁, B₂` avoid the canonical residual
    `R = ((parts n).erase A).erase B`.  Mirrors S13's `split_freshness` for the
    asymmetric shape. -/
theorem split_freshness3
    (parts : ℕ → Finset (Finset V)) (n : ℕ)
    (A B B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hsplitB : B₁ ∪ B₂ = B) (hdB : Disjoint B₁ B₂)
    (hB1 : B₁.Nonempty) (hB2 : B₂.Nonempty) :
    A ≠ B₁ ∧ A ≠ B₂ ∧ B₁ ≠ B₂ ∧
      B₁ ∉ ((parts n).erase A).erase B ∧ B₂ ∉ ((parts n).erase A).erase B := by
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  have hABd : Disjoint A B := hdisj A B hA hB hAB
  -- Every residual block is a block of `parts n` distinct from both `A` and `B`,
  -- hence disjoint from `B`.
  have hRB : ∀ Q ∈ ((parts n).erase A).erase B, Disjoint Q B := by
    intro Q hQ
    obtain ⟨hQB, hQ'⟩ := Finset.mem_erase.mp hQ
    obtain ⟨_, hQP⟩ := Finset.mem_erase.mp hQ'
    exact hdisj Q B hQP hB hQB
  refine ⟨?_, ?_, ne_of_disjoint_nonempty hdB hB1, ?_, ?_⟩
  · exact (ne_of_subset_disjoint sB1 (Finset.Subset.refl A) hABd.symm hB1).symm
  · exact (ne_of_subset_disjoint sB2 (Finset.Subset.refl A) hABd.symm hB2).symm
  · exact not_mem_of_subset_forall_disjoint sB1 hRB hB1
  · exact not_mem_of_subset_forall_disjoint sB2 hRB hB2

/-- **Witnessed 3-piece step from the split + nonempty pieces (freshness-free).**
    The 3-piece mirror of S13's `isWitnessedSharpStep_of_split_of_nonempty`: the
    full `IsWitnessedSharpStep3` follows from the split data (shape of
    `parts (n+1)`, disjoint split of `B`, coarse mass floors, `eps`-mass floor on
    `B₁`, `eps`-gap) plus nonemptiness of the two pieces — the freshness
    side-conditions are discharged automatically. -/
theorem isWitnessedSharpStep3_of_split_of_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hnext : parts (n + 1) =
      insert A (insert B₁ (insert B₂ (((parts n).erase A).erase B))))
    (hsplitB : B₁ ∪ B₂ = B) (hdB : Disjoint B₁ B₂)
    (hB1 : B₁.Nonempty) (hB2 : B₂.Nonempty)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hfloor : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep3 G parts n eps m := by
  obtain ⟨hAB1, hAB2, hB1B2, hB1R, hB2R⟩ :=
    split_freshness3 parts n A B B₁ B₂ hA hB hAB hdisj hsplitB hdB hB1 hB2
  exact isWitnessedSharpStep3_of_split G parts n eps m A B B₁ B₂ hA hB hAB hnext
    hsplitB hdB hAB1 hAB2 hB1B2 hB1R hB2R hmA hmB hfloor hgap

/-- **Witnessed 3-piece step from the split + mass floor (`B₁` nonemptiness
    derived).**  The 3-piece mirror of S14's `isWitnessedSharpStep_of_split_of_gap`:
    the deviating piece `B₁` is nonempty because `|B₁| ≥ eps·|B| ≥ eps·m > 0`; only
    the complement piece `B₂` — which the `eps`-mass floor does not constrain —
    remains as a nonemptiness side-condition, and the S17 extraction supplies
    exactly that. -/
theorem isWitnessedSharpStep3_of_split_of_gap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hnext : parts (n + 1) =
      insert A (insert B₁ (insert B₂ (((parts n).erase A).erase B))))
    (hsplitB : B₁ ∪ B₂ = B) (hdB : Disjoint B₁ B₂)
    (hB2 : B₂.Nonempty)
    (heps : 0 < eps) (hm : 0 < m)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hfloor : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep3 G parts n eps m := by
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℚ) < (B.card : ℚ) := lt_of_lt_of_le hm hmB
    exact_mod_cast this
  have hB1 : B₁.Nonempty := nonempty_of_massFloor heps hBne hfloor
  exact isWitnessedSharpStep3_of_split_of_nonempty G parts n eps m A B B₁ B₂
    hA hB hAB hdisj hnext hsplitB hdB hB1 hB2 hmA hmB hfloor hgap

-- ═══════════════════════════════════════════════════════════════════
-- PART II: PARTITION-INVARIANT MAINTENANCE
-- ═══════════════════════════════════════════════════════════════════

/-- The 4-piece refined family still covers the vertices: a vertex of `A` lands
    in `A₁` or `A₂`, a vertex of `B` in `B₁` or `B₂`, and any other vertex keeps
    its (untouched) block in the residual. -/
theorem refined4_cover
    (q : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B) :
    ∀ v : V, ∃ P ∈ insert A₁ (insert A₂ (insert B₁ (insert B₂ ((q.erase A).erase B)))),
      v ∈ P := by
  intro v
  obtain ⟨P, hP, hvP⟩ := hcover v
  by_cases hPA : P = A
  · rw [hPA, ← hsplitA] at hvP
    rcases Finset.mem_union.mp hvP with h | h
    · exact ⟨A₁, Finset.mem_insert_self _ _, h⟩
    · exact ⟨A₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
  by_cases hPB : P = B
  · rw [hPB, ← hsplitB] at hvP
    rcases Finset.mem_union.mp hvP with h | h
    · exact ⟨B₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)), h⟩
    · exact ⟨B₂, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))), h⟩
  · have hPR : P ∈ (q.erase A).erase B :=
      Finset.mem_erase.mpr ⟨hPB, Finset.mem_erase.mpr ⟨hPA, hP⟩⟩
    exact ⟨P, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hPR))), hvP⟩

/-- The 4-piece refined family is pairwise disjoint: pieces of one block are
    disjoint by the split, pieces of different blocks inherit the blocks'
    disjointness, and residual blocks were already pairwise disjoint. -/
theorem refined4_disjoint
    (q : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ q) (hB : B ∈ q) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q)
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂) :
    ∀ P Q : Finset V,
      P ∈ insert A₁ (insert A₂ (insert B₁ (insert B₂ ((q.erase A).erase B)))) →
      Q ∈ insert A₁ (insert A₂ (insert B₁ (insert B₂ ((q.erase A).erase B)))) →
      P ≠ Q → Disjoint P Q := by
  have sA1 : A₁ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_left
  have sA2 : A₂ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_right
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  have hABd : Disjoint A B := hdisj A B hA hB hAB
  have hRA : ∀ {X : Finset V}, X ∈ (q.erase A).erase B → Disjoint A X := by
    intro X hX
    obtain ⟨_, hX'⟩ := Finset.mem_erase.mp hX
    obtain ⟨hXA, hXq⟩ := Finset.mem_erase.mp hX'
    exact hdisj A X hA hXq (Ne.symm hXA)
  have hRB : ∀ {X : Finset V}, X ∈ (q.erase A).erase B → Disjoint B X := by
    intro X hX
    obtain ⟨hXB, hX'⟩ := Finset.mem_erase.mp hX
    obtain ⟨_, hXq⟩ := Finset.mem_erase.mp hX'
    exact hdisj B X hB hXq (Ne.symm hXB)
  have hRR : ∀ {X Y : Finset V}, X ∈ (q.erase A).erase B → Y ∈ (q.erase A).erase B →
      X ≠ Y → Disjoint X Y := by
    intro X Y hX hY hXY
    exact hdisj X Y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hX))
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hY)) hXY
  intro P Q hP hQ hPQ
  simp only [Finset.mem_insert] at hP hQ
  rcases hP with rfl | rfl | rfl | rfl | hPR <;>
    rcases hQ with rfl | rfl | rfl | rfl | hQR
  · exact absurd rfl hPQ
  · exact hdA
  · exact hABd.mono sA1 sB1
  · exact hABd.mono sA1 sB2
  · exact (hRA hQR).mono_left sA1
  · exact hdA.symm
  · exact absurd rfl hPQ
  · exact hABd.mono sA2 sB1
  · exact hABd.mono sA2 sB2
  · exact (hRA hQR).mono_left sA2
  · exact (hABd.mono sA1 sB1).symm
  · exact (hABd.mono sA2 sB1).symm
  · exact absurd rfl hPQ
  · exact hdB
  · exact (hRB hQR).mono_left sB1
  · exact (hABd.mono sA1 sB2).symm
  · exact (hABd.mono sA2 sB2).symm
  · exact hdB.symm
  · exact absurd rfl hPQ
  · exact (hRB hQR).mono_left sB2
  · exact ((hRA hPR).mono_left sA1).symm
  · exact ((hRA hPR).mono_left sA2).symm
  · exact ((hRB hPR).mono_left sB1).symm
  · exact ((hRB hPR).mono_left sB2).symm
  · exact hRR hPR hQR hPQ

/-- The 4-piece refined family refines every coarse partition the parent
    refines: pieces sit inside their block's coarse host, residual blocks keep
    their own host. -/
theorem refined4_refines
    (q Vparts : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ q) (hB : B ∈ q)
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (href : IsRefinement q Vparts) :
    IsRefinement (insert A₁ (insert A₂ (insert B₁ (insert B₂ ((q.erase A).erase B)))))
      Vparts := by
  have sA1 : A₁ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_left
  have sA2 : A₂ ⊆ A := by rw [← hsplitA]; exact Finset.subset_union_right
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  obtain ⟨VA, hVA, hAVA⟩ := href A hA
  obtain ⟨VB, hVB, hBVB⟩ := href B hB
  intro W hW
  simp only [Finset.mem_insert] at hW
  rcases hW with rfl | rfl | rfl | rfl | hWR
  · exact ⟨VA, hVA, sA1.trans hAVA⟩
  · exact ⟨VA, hVA, sA2.trans hAVA⟩
  · exact ⟨VB, hVB, sB1.trans hBVB⟩
  · exact ⟨VB, hVB, sB2.trans hBVB⟩
  · exact href W (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hWR))

/-- The 3-piece refined family still covers the vertices: `A` survives intact, a
    vertex of `B` lands in `B₁` or `B₂`, other vertices keep their block. -/
theorem refined3_cover
    (q : Finset (Finset V)) (A B B₁ B₂ : Finset V)
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (hsplitB : B₁ ∪ B₂ = B) :
    ∀ v : V, ∃ P ∈ insert A (insert B₁ (insert B₂ ((q.erase A).erase B))), v ∈ P := by
  intro v
  obtain ⟨P, hP, hvP⟩ := hcover v
  by_cases hPA : P = A
  · rw [hPA] at hvP
    exact ⟨A, Finset.mem_insert_self _ _, hvP⟩
  by_cases hPB : P = B
  · rw [hPB, ← hsplitB] at hvP
    rcases Finset.mem_union.mp hvP with h | h
    · exact ⟨B₁, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨B₂, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)), h⟩
  · have hPR : P ∈ (q.erase A).erase B :=
      Finset.mem_erase.mpr ⟨hPB, Finset.mem_erase.mpr ⟨hPA, hP⟩⟩
    exact ⟨P, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem hPR)), hvP⟩

/-- The 3-piece refined family is pairwise disjoint. -/
theorem refined3_disjoint
    (q : Finset (Finset V)) (A B B₁ B₂ : Finset V)
    (hA : A ∈ q) (hB : B ∈ q) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q)
    (hsplitB : B₁ ∪ B₂ = B) (hdB : Disjoint B₁ B₂) :
    ∀ P Q : Finset V,
      P ∈ insert A (insert B₁ (insert B₂ ((q.erase A).erase B))) →
      Q ∈ insert A (insert B₁ (insert B₂ ((q.erase A).erase B))) →
      P ≠ Q → Disjoint P Q := by
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  have hABd : Disjoint A B := hdisj A B hA hB hAB
  have hRA : ∀ {X : Finset V}, X ∈ (q.erase A).erase B → Disjoint A X := by
    intro X hX
    obtain ⟨_, hX'⟩ := Finset.mem_erase.mp hX
    obtain ⟨hXA, hXq⟩ := Finset.mem_erase.mp hX'
    exact hdisj A X hA hXq (Ne.symm hXA)
  have hRB : ∀ {X : Finset V}, X ∈ (q.erase A).erase B → Disjoint B X := by
    intro X hX
    obtain ⟨hXB, hX'⟩ := Finset.mem_erase.mp hX
    obtain ⟨_, hXq⟩ := Finset.mem_erase.mp hX'
    exact hdisj B X hB hXq (Ne.symm hXB)
  have hRR : ∀ {X Y : Finset V}, X ∈ (q.erase A).erase B → Y ∈ (q.erase A).erase B →
      X ≠ Y → Disjoint X Y := by
    intro X Y hX hY hXY
    exact hdisj X Y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hX))
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hY)) hXY
  intro P Q hP hQ hPQ
  simp only [Finset.mem_insert] at hP hQ
  rcases hP with rfl | rfl | rfl | hPR <;>
    rcases hQ with rfl | rfl | rfl | hQR
  · exact absurd rfl hPQ
  · exact hABd.mono_right sB1
  · exact hABd.mono_right sB2
  · exact hRA hQR
  · exact (hABd.mono_right sB1).symm
  · exact absurd rfl hPQ
  · exact hdB
  · exact (hRB hQR).mono_left sB1
  · exact (hABd.mono_right sB2).symm
  · exact hdB.symm
  · exact absurd rfl hPQ
  · exact (hRB hQR).mono_left sB2
  · exact (hRA hPR).symm
  · exact ((hRB hPR).mono_left sB1).symm
  · exact ((hRB hPR).mono_left sB2).symm
  · exact hRR hPR hQR hPQ

/-- The 3-piece refined family refines every coarse partition the parent
    refines. -/
theorem refined3_refines
    (q Vparts : Finset (Finset V)) (A B B₁ B₂ : Finset V)
    (hA : A ∈ q) (hB : B ∈ q)
    (hsplitB : B₁ ∪ B₂ = B)
    (href : IsRefinement q Vparts) :
    IsRefinement (insert A (insert B₁ (insert B₂ ((q.erase A).erase B)))) Vparts := by
  have sB1 : B₁ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_left
  have sB2 : B₂ ⊆ B := by rw [← hsplitB]; exact Finset.subset_union_right
  obtain ⟨VB, hVB, hBVB⟩ := href B hB
  intro W hW
  simp only [Finset.mem_insert] at hW
  rcases hW with rfl | rfl | rfl | hWR
  · exact href _ hA
  · exact ⟨VB, hVB, sB1.trans hBVB⟩
  · exact ⟨VB, hVB, sB2.trans hBVB⟩
  · exact href W (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hWR))

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE SINGLE-STEP REALIZATION
-- ═══════════════════════════════════════════════════════════════════

/-- **The single-step realization of the AFKS dichotomy.**  An equitable,
    pairwise disjoint, covering partition `q` with per-part mass floor `m` that
    is *not* AFKS-fine-regular at tolerances `(ε, E)` admits a concrete successor
    partition `q'` such that

    * `q'` covers the vertices,
    * `q'` is pairwise disjoint,
    * `q'` refines every coarse partition `q` refines, and
    * **any** chain `parts` passing through `q, q'` at steps `n, n+1` makes a
      witnessed sharp step there — the symmetric 4-piece `IsWitnessedSharpStep`
      or the asymmetric 3-piece `IsWitnessedSharpStep3`, exactly the disjunction
      the S19 two-shape outer loop consumes as its dichotomy hypothesis.

    This is the induction-step brick of the outstanding recursive chain
    construction: at each non-regular step the recursion invokes this theorem
    (via `Classical.choose`) to produce the next term.  What the recursion must
    still supply on its own is the *maintenance* of the equitability and
    mass-floor hypotheses across steps — the classical re-equitization
    bookkeeping, which a bare split does not preserve. -/
theorem exists_witnessed_next_of_not_afksFineRegular
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε E m : ℚ)
    (hε : 0 ≤ ε) (hE : 0 < E) (hm : 0 < m)
    (q : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (hdisj : ∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q)
    (hequit : ∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1)
    (hmass : ∀ P ∈ q, m ≤ (P.card : ℚ))
    (hnot : ¬ IsAFKSFineRegular G ε E q) :
    ∃ q' : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
      (∀ Vparts : Finset (Finset V), IsRefinement q Vparts → IsRefinement q' Vparts) ∧
      (∀ parts : ℕ → Finset (Finset V), ∀ n : ℕ,
        parts n = q → parts (n + 1) = q' →
        IsWitnessedSharpStep G parts n E m ∨ IsWitnessedSharpStep3 G parts n E m) := by
  rcases exists_proper_or_semitrivial_split_of_not_afksFineRegular G ε E hε hE q
      hequit hnot with
    ⟨A, B, A₁, A₂, B₁, B₂, hA, hB, hAB, hsA, hsB, hdA, hdB,
      hfA, hfB, hgap, hA2ne, hB2ne⟩ |
    ⟨A, B, B₁, B₂, hA, hB, hAB, hsB, hdB, hfB, hgap, hB2ne⟩
  · -- Symmetric branch: the genuinely proper 2×2 split.
    refine ⟨insert A₁ (insert A₂ (insert B₁ (insert B₂ ((q.erase A).erase B)))),
      refined4_cover q A B A₁ A₂ B₁ B₂ hcover hsA hsB,
      refined4_disjoint q A B A₁ A₂ B₁ B₂ hA hB hAB hdisj hsA hsB hdA hdB,
      fun Vparts href => refined4_refines q Vparts A B A₁ A₂ B₁ B₂ hA hB hsA hsB href,
      ?_⟩
    intro parts n hqn hqn1
    left
    refine isWitnessedSharpStep_of_split_of_gap G parts n E m A B A₁ A₂ B₁ B₂
      (by rw [hqn]; exact hA) (by rw [hqn]; exact hB) hAB
      (by rw [hqn]; exact hdisj)
      (by rw [hqn1, hqn]) hsA hsB hdA hdB hA2ne hB2ne hE hm
      (hmass A hA) (hmass B hB) hfA hfB hgap
  · -- Asymmetric branch: the normalized 3-piece split.
    refine ⟨insert A (insert B₁ (insert B₂ ((q.erase A).erase B))),
      refined3_cover q A B B₁ B₂ hcover hsB,
      refined3_disjoint q A B B₁ B₂ hA hB hAB hdisj hsB hdB,
      fun Vparts href => refined3_refines q Vparts A B B₁ B₂ hA hB hsB href,
      ?_⟩
    intro parts n hqn hqn1
    right
    refine isWitnessedSharpStep3_of_split_of_gap G parts n E m A B B₁ B₂
      (by rw [hqn]; exact hA) (by rw [hqn]; exact hB) hAB
      (by rw [hqn]; exact hdisj)
      (by rw [hqn1, hqn]) hsB hdB hB2ne hE hm
      (hmass A hA) (hmass B hB) hfB hgap

end Szemeredi.RegularityOQ04StepRealize
