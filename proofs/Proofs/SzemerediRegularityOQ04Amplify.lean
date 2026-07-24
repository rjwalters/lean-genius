/-
  Szemerédi Regularity Lemma — OQ-04, S28b: the summed (amplified)
  energy-increment assembly over a *marked set* of irregular pairs.

  ## Where this sits in the OQ-04 tower

  S27b-ii (`SzemerediRegularityOQ04Assemble`) closed the invariant-restoration
  loop but exposed a hard deficit: the *single-witness* energy gain
  `ε⁴m²/n²` of the S12–S21 dichotomy machinery is strictly smaller than the
  restoration cost `2m/n` for every admissible parameter choice — no
  bookkeeping closes it (structured blocker on the tracker).  The true AFKS
  increment refines by the witnesses of **all** irregular pairs at once: with
  more than `ε·k(k−1)` irregular pairs each contributing `ε⁴|A||B|/n²`, the
  summed gain is `ε⁵`-scale — independent of `m` and `n` — and dwarfs the
  restoration cost.  That amplification (S28) needs three layers:

  * **(this file, S28b)** the *analytic assembly*: a common refinement whose
    cells split along each marked pair's `2×2` witness grid raises
    `partitionEnergy` by the **sum** of the per-pair grid gains;
  * (S28c) the *witness-atomising engine*: constructing, per part, a common
    refinement splitting along every chosen witness set simultaneously;
  * (S28d) the *counting step*: `> ε·k(k−1)` marked pairs × mass floors
    `m ≤ |A|` turn the summed gain into the `ε⁵`-scale constant fed to
    `exists_afksTwoLevel_of_maintained_oracle`.

  ## Contents

  * `filter_split_covers` — if every cell of a cover of `A` lies inside `A′`
    or inside `A \ A′`, the cells inside `A′` cover exactly `A′` and the rest
    cover exactly `A \ A′`.
  * `grid_le_cells_sum` — **quadrant grouping**: cell families of `A` and `B`
    splitting along `A′ ⊆ A`, `B′ ⊆ B` dominate the four-term `2×2` grid
    energy `pe(A′,B′) + pe(A′,B∖B′) + pe(A∖A′,B′) + pe(A∖A′,B∖B′)`.
  * `partitionEnergy_refine_gain_marked` — the marked-pair upgrade of
    `partitionEnergy_refine_mono`: monotonicity on unmarked pairs, the
    caller's per-pair gain on marked pairs, summed.
  * `partitionEnergy_refine_gain_of_grid_splits` — capstone: a common
    refinement splitting along each marked pair's witness grid gains the
    **sum** of the grid gains.
  * `partitionEnergy_refine_gain_marked_card` — numeric form: a uniform
    per-pair floor `γ` yields total gain `≥ |M|·γ` (the shape S28d consumes).
  * `exists_grid_witnesses_of_irregular` — choice packaging: witness
    *functions* `wA, wB` with the sharp `ε⁴|A||B|/n²` grid gain for every
    pair in a marked set of `ε`-irregular pairs (the interface S28c's
    atomiser builds against).

  All results are fully machine-checked (0 axioms, 0 sorries) on the
  established primitives `pairEnergy_biUnion_split_mono_prod` (FullRefine)
  and `pairEnergy_prod_gain_of_irregular_eps4` (Bridge).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996), §2 (the
  summed-defect step of the classical energy-increment argument).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FullRefine

namespace Szemeredi.RegularityOQ04Amplify

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04FamilySplit
open Szemeredi.RegularityOQ04FullRefine

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: QUADRANT GROUPING — CELLS SPLITTING ALONG A WITNESS GRID
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] in
/-- **Split cover identities.**  If the cells `CA` cover `A` and each cell lies
    inside `A′` or inside `A \ A′`, then the cells inside `A′` cover exactly
    `A′`, and the remaining cells cover exactly `A \ A′`.  (A cell meeting both
    sides would have to be empty, and an inhabited cell decides its side.) -/
theorem filter_split_covers {A A' : Finset V} (hA' : A' ⊆ A)
    {CA : Finset (Finset V)} (hcov : CA.biUnion id = A)
    (hsplit : ∀ c ∈ CA, c ⊆ A' ∨ c ⊆ A \ A') :
    (CA.filter (fun c => c ⊆ A')).biUnion id = A' ∧
      (CA.filter (fun c => ¬ c ⊆ A')).biUnion id = A \ A' := by
  classical
  constructor
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨c, ⟨_, hcA'⟩, hxc⟩
      exact hcA' hxc
    · intro hxA'
      have hxA : x ∈ CA.biUnion id := by rw [hcov]; exact hA' hxA'
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxA
      simp only [id_eq] at hxc
      rcases hsplit c hc with hpos | hneg
      · exact ⟨c, ⟨hc, hpos⟩, hxc⟩
      · exact absurd hxA' (Finset.mem_sdiff.mp (hneg hxc)).2
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨c, ⟨hc, hnc⟩, hxc⟩
      exact ((hsplit c hc).resolve_left hnc) hxc
    · intro hx
      have hxA : x ∈ CA.biUnion id := by
        rw [hcov]; exact (Finset.mem_sdiff.mp hx).1
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxA
      simp only [id_eq] at hxc
      refine ⟨c, ⟨hc, fun hcs => ?_⟩, hxc⟩
      exact (Finset.mem_sdiff.mp hx).2 (hcs hxc)

/-- **Quadrant grouping.**  Let `CA` be a disjoint cell family covering `A`
    whose every cell lies inside `A′` or inside `A \ A′`, and likewise `CB`
    for `B` along `B′`.  Grouping the cells by quadrant and applying two-sided
    split monotonicity on each quadrant, the total fine-cell energy dominates
    the four-term `2×2` witness-grid energy:

    `pe(A′,B′) + pe(A′,B∖B′) + pe(A∖A′,B′) + pe(A∖A′,B∖B′) ≤ Σ_c Σ_d pe(c,d)`.

    This is the bridge that lets a *common* refinement (which shatters the
    witness sets into many small cells, none of which need carry the witness
    density) still collect the full grid gain of every marked pair. -/
theorem grid_le_cells_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B A' B' : Finset V) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (CA CB : Finset (Finset V))
    (hcovA : CA.biUnion id = A)
    (hdisjA : (↑CA : Set (Finset V)).PairwiseDisjoint id)
    (hsplitA : ∀ c ∈ CA, c ⊆ A' ∨ c ⊆ A \ A')
    (hcovB : CB.biUnion id = B)
    (hdisjB : (↑CB : Set (Finset V)).PairwiseDisjoint id)
    (hsplitB : ∀ d ∈ CB, d ⊆ B' ∨ d ⊆ B \ B') :
    pairEnergy G A' B' + pairEnergy G A' (B \ B') +
        pairEnergy G (A \ A') B' + pairEnergy G (A \ A') (B \ B') ≤
      ∑ c ∈ CA, ∑ d ∈ CB, pairEnergy G c d := by
  classical
  obtain ⟨hcovA1, hcovA2⟩ := filter_split_covers hA' hcovA hsplitA
  obtain ⟨hcovB1, hcovB2⟩ := filter_split_covers hB' hcovB hsplitB
  -- Two-sided split monotonicity on any pair of subfamilies.
  have quad : ∀ SA SB : Finset (Finset V), SA ⊆ CA → SB ⊆ CB →
      pairEnergy G (SA.biUnion id) (SB.biUnion id) ≤
        ∑ c ∈ SA, ∑ d ∈ SB, pairEnergy G c d := by
    intro SA SB hSA hSB
    have h := pairEnergy_biUnion_split_mono_prod G SA id SB id
      (hdisjA.subset (Finset.coe_subset.mpr hSA))
      (hdisjB.subset (Finset.coe_subset.mpr hSB))
    simpa using h
  -- The four quadrant bounds.
  have h11 : pairEnergy G A' B' ≤
      ∑ c ∈ CA.filter (fun c => c ⊆ A'),
        ∑ d ∈ CB.filter (fun d => d ⊆ B'), pairEnergy G c d := by
    have h := quad (CA.filter (fun c => c ⊆ A')) (CB.filter (fun d => d ⊆ B'))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rwa [hcovA1, hcovB1] at h
  have h12 : pairEnergy G A' (B \ B') ≤
      ∑ c ∈ CA.filter (fun c => c ⊆ A'),
        ∑ d ∈ CB.filter (fun d => ¬ d ⊆ B'), pairEnergy G c d := by
    have h := quad (CA.filter (fun c => c ⊆ A')) (CB.filter (fun d => ¬ d ⊆ B'))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rwa [hcovA1, hcovB2] at h
  have h21 : pairEnergy G (A \ A') B' ≤
      ∑ c ∈ CA.filter (fun c => ¬ c ⊆ A'),
        ∑ d ∈ CB.filter (fun d => d ⊆ B'), pairEnergy G c d := by
    have h := quad (CA.filter (fun c => ¬ c ⊆ A')) (CB.filter (fun d => d ⊆ B'))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rwa [hcovA2, hcovB1] at h
  have h22 : pairEnergy G (A \ A') (B \ B') ≤
      ∑ c ∈ CA.filter (fun c => ¬ c ⊆ A'),
        ∑ d ∈ CB.filter (fun d => ¬ d ⊆ B'), pairEnergy G c d := by
    have h := quad (CA.filter (fun c => ¬ c ⊆ A')) (CB.filter (fun d => ¬ d ⊆ B'))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rwa [hcovA2, hcovB2] at h
  -- The full cell sum decomposes into the four quadrant sums.
  have htot : ∑ c ∈ CA, ∑ d ∈ CB, pairEnergy G c d
      = ∑ c ∈ CA.filter (fun c => c ⊆ A'),
          ∑ d ∈ CB.filter (fun d => d ⊆ B'), pairEnergy G c d
      + ∑ c ∈ CA.filter (fun c => c ⊆ A'),
          ∑ d ∈ CB.filter (fun d => ¬ d ⊆ B'), pairEnergy G c d
      + (∑ c ∈ CA.filter (fun c => ¬ c ⊆ A'),
          ∑ d ∈ CB.filter (fun d => d ⊆ B'), pairEnergy G c d
      + ∑ c ∈ CA.filter (fun c => ¬ c ⊆ A'),
          ∑ d ∈ CB.filter (fun d => ¬ d ⊆ B'), pairEnergy G c d) := by
    have hinner : ∀ c : Finset V, ∑ d ∈ CB, pairEnergy G c d
        = ∑ d ∈ CB.filter (fun d => d ⊆ B'), pairEnergy G c d
        + ∑ d ∈ CB.filter (fun d => ¬ d ⊆ B'), pairEnergy G c d :=
      fun c => (Finset.sum_filter_add_sum_filter_not CB (fun d => d ⊆ B') _).symm
    rw [← Finset.sum_filter_add_sum_filter_not CA (fun c => c ⊆ A')
        (fun c => ∑ d ∈ CB, pairEnergy G c d)]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [h11, h12, h21, h22, htot]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: MARKED-PAIR SUMMED-GAIN REFINEMENT
-- ═══════════════════════════════════════════════════════════════════

/-- **Marked-pair summed-gain refinement.**  The gain-aware upgrade of
    `partitionEnergy_refine_mono`: refine every part `A ∈ P` into disjoint
    cells `pieces A`, and mark a set `M ⊆ P ×ˢ P` of ordered pairs on which the
    caller certifies a per-pair energy gain `g p` at the cell level.  Unmarked
    pairs contribute by plain two-sided split monotonicity; the marked gains
    **add up**:

    `partitionEnergy G P + Σ_{p ∈ M} g p ≤ partitionEnergy G (P.biUnion pieces)`.

    This is the summed (amplified) form of the energy-increment step: with the
    marked set taken to be the irregular pairs of a too-irregular partition,
    the total gain is `ε⁵`-scale rather than the single-witness `ε⁴m²/n²`. -/
theorem partitionEnergy_refine_gain_marked (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (pieces : Finset V → Finset (Finset V))
    (hcover : ∀ A ∈ P, (pieces A).biUnion id = A)
    (hdisjIn : ∀ A ∈ P, (↑(pieces A) : Set (Finset V)).PairwiseDisjoint id)
    (hdisjOut : (↑P : Set (Finset V)).PairwiseDisjoint pieces)
    (M : Finset (Finset V × Finset V)) (hM : M ⊆ P ×ˢ P)
    (g : Finset V × Finset V → ℚ)
    (hgain : ∀ p ∈ M, pairEnergy G p.1 p.2 + g p ≤
        ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d) :
    partitionEnergy G P + ∑ p ∈ M, g p ≤ partitionEnergy G (P.biUnion pieces) := by
  classical
  -- Nested-double-sum form of `partitionEnergy`, from the bridge lemma.
  have hdouble : ∀ parts : Finset (Finset V),
      partitionEnergy G parts = ∑ A ∈ parts, ∑ B ∈ parts, pairEnergy G A B := by
    intro parts
    rw [partitionEnergy_eq_sum_pairEnergy,
      show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  -- Coarse energy as a product-indexed sum.
  have hPcoarse : partitionEnergy G P = ∑ p ∈ P ×ˢ P, pairEnergy G p.1 p.2 := by
    rw [hdouble P]
    exact (Finset.sum_product' P P (fun A B => pairEnergy G A B)).symm
  -- Fine energy as a product-indexed sum of per-pair cell sums.
  have hPB : partitionEnergy G (P.biUnion pieces)
      = ∑ p ∈ P ×ˢ P, ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d := by
    have h1 : partitionEnergy G (P.biUnion pieces)
        = ∑ A ∈ P, ∑ c ∈ pieces A, ∑ B ∈ P, ∑ d ∈ pieces B, pairEnergy G c d := by
      rw [hdouble (P.biUnion pieces), Finset.sum_biUnion hdisjOut]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_biUnion hdisjOut]
    have h2 : ∑ p ∈ P ×ˢ P, (∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d)
        = ∑ A ∈ P, ∑ B ∈ P, ∑ c ∈ pieces A, ∑ d ∈ pieces B, pairEnergy G c d :=
      Finset.sum_product' P P
        (fun A B => ∑ c ∈ pieces A, ∑ d ∈ pieces B, pairEnergy G c d)
    calc partitionEnergy G (P.biUnion pieces)
        = ∑ A ∈ P, ∑ c ∈ pieces A, ∑ B ∈ P, ∑ d ∈ pieces B, pairEnergy G c d := h1
      _ = ∑ A ∈ P, ∑ B ∈ P, ∑ c ∈ pieces A, ∑ d ∈ pieces B, pairEnergy G c d :=
          Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
      _ = ∑ p ∈ P ×ˢ P, ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d :=
          h2.symm
  -- Unmarked pairs: plain two-sided refinement monotonicity.
  have key : ∀ p ∈ (P ×ˢ P) \ M,
      pairEnergy G p.1 p.2 ≤ ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_sdiff.mp hp).1
    have h := pairEnergy_biUnion_split_mono_prod G (pieces p.1) id (pieces p.2) id
      (hdisjIn p.1 hp1) (hdisjIn p.2 hp2)
    rw [hcover p.1 hp1, hcover p.2 hp2] at h
    simpa using h
  calc partitionEnergy G P + ∑ p ∈ M, g p
      = (∑ p ∈ (P ×ˢ P) \ M, pairEnergy G p.1 p.2
          + ∑ p ∈ M, pairEnergy G p.1 p.2) + ∑ p ∈ M, g p := by
        rw [hPcoarse, ← Finset.sum_sdiff hM]
    _ = ∑ p ∈ (P ×ˢ P) \ M, pairEnergy G p.1 p.2
          + ∑ p ∈ M, (pairEnergy G p.1 p.2 + g p) := by
        rw [Finset.sum_add_distrib]; ring
    _ ≤ ∑ p ∈ (P ×ˢ P) \ M, (∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d)
          + ∑ p ∈ M, (∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d) :=
        add_le_add (Finset.sum_le_sum key) (Finset.sum_le_sum hgain)
    _ = ∑ p ∈ P ×ˢ P, ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d :=
        Finset.sum_sdiff hM
    _ = partitionEnergy G (P.biUnion pieces) := hPB.symm

-- ═══════════════════════════════════════════════════════════════════
-- PART III: CAPSTONE — GRID-SPLITTING COMMON REFINEMENT GAINS THE SUM
-- ═══════════════════════════════════════════════════════════════════

/-- **Grid-splitting common refinement gains the sum of the grid gains.**
    Combine Parts I and II: refine every part of `P` into disjoint cells, and
    suppose that for each marked pair `p ∈ M` the cells of `p.1` split along a
    witness set `wA p ⊆ p.1` (each cell inside `wA p` or inside its
    complement), likewise for `p.2` along `wB p`, while the `2×2` witness grid
    of `p` carries an energy gain `g p` over `pairEnergy p.1 p.2`.  Then the
    refined partition gains the **sum** of all marked gains:

    `partitionEnergy G P + Σ_{p ∈ M} g p ≤ partitionEnergy G (P.biUnion pieces)`.

    This is the analytic half of the S28 amplification: it reduces the summed
    `ε⁵`-scale increment to *constructing* a per-part common refinement that
    splits along every chosen witness set simultaneously (the S28c atomiser). -/
theorem partitionEnergy_refine_gain_of_grid_splits (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (P : Finset (Finset V)) (pieces : Finset V → Finset (Finset V))
    (hcover : ∀ A ∈ P, (pieces A).biUnion id = A)
    (hdisjIn : ∀ A ∈ P, (↑(pieces A) : Set (Finset V)).PairwiseDisjoint id)
    (hdisjOut : (↑P : Set (Finset V)).PairwiseDisjoint pieces)
    (M : Finset (Finset V × Finset V)) (hM : M ⊆ P ×ˢ P)
    (wA wB : Finset V × Finset V → Finset V) (g : Finset V × Finset V → ℚ)
    (hwA : ∀ p ∈ M, wA p ⊆ p.1) (hwB : ∀ p ∈ M, wB p ⊆ p.2)
    (hsplitA : ∀ p ∈ M, ∀ c ∈ pieces p.1, c ⊆ wA p ∨ c ⊆ p.1 \ wA p)
    (hsplitB : ∀ p ∈ M, ∀ d ∈ pieces p.2, d ⊆ wB p ∨ d ⊆ p.2 \ wB p)
    (hgrid : ∀ p ∈ M,
        pairEnergy G p.1 p.2 + g p ≤
          pairEnergy G (wA p) (wB p) + pairEnergy G (wA p) (p.2 \ wB p) +
            pairEnergy G (p.1 \ wA p) (wB p) +
            pairEnergy G (p.1 \ wA p) (p.2 \ wB p)) :
    partitionEnergy G P + ∑ p ∈ M, g p ≤ partitionEnergy G (P.biUnion pieces) := by
  refine partitionEnergy_refine_gain_marked G P pieces hcover hdisjIn hdisjOut
    M hM g (fun p hp => ?_)
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (hM hp)
  have hcells := grid_le_cells_sum G p.1 p.2 (wA p) (wB p) (hwA p hp) (hwB p hp)
    (pieces p.1) (pieces p.2)
    (hcover p.1 hp1) (hdisjIn p.1 hp1) (hsplitA p hp)
    (hcover p.2 hp2) (hdisjIn p.2 hp2) (hsplitB p hp)
  linarith [hgrid p hp]

/-- **Uniform-floor numeric form.**  If every marked gain is at least `γ`, the
    refined partition gains at least `|M|·γ`.  With `M` the irregular pairs of
    a too-irregular equitable partition (`|M| > ε·k(k−1)`) and
    `γ = ε⁴m²/n²` from the mass floors, this is the `ε⁵`-scale amplified
    increment the S28d counting step feeds to the maintained oracle. -/
theorem partitionEnergy_refine_gain_marked_card (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (P : Finset (Finset V)) (pieces : Finset V → Finset (Finset V))
    (hcover : ∀ A ∈ P, (pieces A).biUnion id = A)
    (hdisjIn : ∀ A ∈ P, (↑(pieces A) : Set (Finset V)).PairwiseDisjoint id)
    (hdisjOut : (↑P : Set (Finset V)).PairwiseDisjoint pieces)
    (M : Finset (Finset V × Finset V)) (hM : M ⊆ P ×ˢ P)
    (g : Finset V × Finset V → ℚ)
    (hgain : ∀ p ∈ M, pairEnergy G p.1 p.2 + g p ≤
        ∑ c ∈ pieces p.1, ∑ d ∈ pieces p.2, pairEnergy G c d)
    (γ : ℚ) (hγ : ∀ p ∈ M, γ ≤ g p) :
    partitionEnergy G P + (M.card : ℚ) * γ ≤
      partitionEnergy G (P.biUnion pieces) := by
  have hsum : (M.card : ℚ) * γ ≤ ∑ p ∈ M, g p := by
    have h := Finset.card_nsmul_le_sum M g γ hγ
    simpa [nsmul_eq_mul] using h
  have hmain := partitionEnergy_refine_gain_marked G P pieces hcover hdisjIn
    hdisjOut M hM g hgain
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: WITNESS-FUNCTION PACKAGING FOR A MARKED IRREGULAR SET
-- ═══════════════════════════════════════════════════════════════════

/-- **Witness functions for a marked set of irregular pairs.**  Every pair in a
    marked set `M` of `ε`-irregular pairs admits witness sets realizing the
    sharp `ε⁴|A||B|/n²` grid gain (`pairEnergy_prod_gain_of_irregular_eps4`);
    packaging the choices as total functions `wA, wB` produces exactly the
    witness data `partitionEnergy_refine_gain_of_grid_splits` consumes.  The
    S28c atomiser must build its per-part common refinement *against these
    functions* — choice happens first, construction second. -/
theorem exists_grid_witnesses_of_irregular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 ≤ eps) (M : Finset (Finset V × Finset V))
    (hirr : ∀ p ∈ M, ¬ IsEpsilonRegular G eps p.1 p.2) :
    ∃ wA wB : Finset V × Finset V → Finset V,
      (∀ p ∈ M, wA p ⊆ p.1) ∧ (∀ p ∈ M, wB p ⊆ p.2) ∧
        ∀ p ∈ M,
          pairEnergy G p.1 p.2 +
              eps ^ 4 * (↑p.1.card * ↑p.2.card) / (Fintype.card V : ℚ) ^ 2 ≤
            pairEnergy G (wA p) (wB p) + pairEnergy G (wA p) (p.2 \ wB p) +
              pairEnergy G (p.1 \ wA p) (wB p) +
              pairEnergy G (p.1 \ wA p) (p.2 \ wB p) := by
  classical
  choose f₁ f₂ h₁ h₂ h₃ using fun (p : Finset V × Finset V) (hp : p ∈ M) =>
    pairEnergy_prod_gain_of_irregular_eps4 G eps heps p.1 p.2 (hirr p hp)
  refine ⟨fun p => if hp : p ∈ M then f₁ p hp else ∅,
          fun p => if hp : p ∈ M then f₂ p hp else ∅, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [dif_pos hp] using h₁ p hp
  · intro p hp
    simpa only [dif_pos hp] using h₂ p hp
  · intro p hp
    simp only [dif_pos hp]
    exact h₃ p hp

end Szemeredi.RegularityOQ04Amplify
