/-
  Szemerédi Regularity Lemma — OQ-04: the outer loop threaded with BOTH step
  shapes (S17 residual (b), the last layer).

  The item-1 dichotomy of the strong (AFKS) regularity lemma resolves a
  non-fine-regular partition into one of TWO honest refinement shapes
  (`StepThree.lean`, S16–S17):

  * the symmetric 4-piece step `IsWitnessedSharpStep` (`Outer.lean`) — both
    parents split, sharp `2×2` grid, `eps⁴` partition-energy gain
    (`partitionEnergy_prod_gain_eps4`, Assembly.lean); and
  * the asymmetric 3-piece step `IsWitnessedSharpStep3` (`StepThree.lean`) —
    only `B` splits, defect deviation against the parent, `eps³` PAIR-energy
    gain (`pairEnergy_gain_of_isWitnessedSharpStep3`, DefectGain.lean, S18).

  The outer-loop assembly `exists_afksTwoLevel_of_dichotomy` (`Outer.lean`)
  consumed only the 4-piece shape, so the degenerate branch of the dichotomy
  could not yet drive the loop.  This file closes that gap:

  * `partitionEnergy_step3_refinement_gain` — the S18 pair-level `eps³` gain
    lifted to the WHOLE partition: replacing `{A, B}` by `{A, B₁, B₂}` over the
    untouched residual `R` raises `partitionEnergy` by `eps³·|A||B|/n²`.  The
    block decomposition mirrors `partitionEnergy_prod_refinement_gain`
    (Assembly.lean): the `R×R` block and every `A`-row/column are unchanged,
    the `B`-rows/columns against `R`, the `(B,A)` cross and the `B²` diagonal
    split by pure `pairEnergy` monotonicity, and the single `(A,B)` cross
    carries the defect gain (`pairEnergy_step3_gain`).
  * `afks_sharp_energy_iteration_count_of_witness_both` — the mixed-chain
    iteration count: a chain in which EVERY step is witnessed by EITHER shape
    still gains `≥ eps⁴·m²/n²` per step (for `eps ≤ 1` the 3-piece `eps³` floor
    dominates the 4-piece `eps⁴` one), so `N ≤ n²/(eps⁴·m²)` — the SAME sharp
    budget as the pure 4-piece chain: the degenerate branch is not merely
    tolerated, it is cheaper.
  * `afks_regular_step_within_bound_both` — termination: past the sharp budget
    some step carries NEITHER witness shape.
  * `exists_afksTwoLevel_of_dichotomy_both` — **the reformulated outer loop**:
    the dichotomy hypothesis now concludes `IsWitnessedSharpStep ∨
    IsWitnessedSharpStep3`, exactly the disjunction
    `exists_proper_or_semitrivial_split_of_not_afksFineRegular` (S17) produces.
    A step below the horizon with neither witness must be AFKS-fine-regular,
    and packages with the coarse partition into `IsAFKSTwoLevel`.
  * `exists_afksTwoLevel_of_dichotomy_both_equipartition` — the tower-free
    `k²/E(k)⁴` horizon form of the same conclusion.

  Everything is a chaining of verified primitives: 0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Outer
import Proofs.SzemerediRegularityOQ04DefectGain

namespace Szemeredi.RegularityOQ04OuterBoth

open Classical
open Szemeredi.Core Szemeredi.EnergyIncrement Szemeredi.RegularityOQ04Energy
  Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04StepThree
  Szemeredi.RegularityOQ04DefectGain Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bridge in nested-double-sum form (local re-derivation of the Bridge
    file's `private` helper), convenient for block decompositions. -/
private theorem partitionEnergy_eq_double_sum (G : SimpleGraph V)
    [DecidableRel G.Adj] (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      parts.sum (fun P => parts.sum (fun Q => pairEnergy G P Q)) := by
  rw [partitionEnergy_eq_sum_pairEnergy,
    show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE 3-PIECE STEP GAIN, LIFTED TO THE WHOLE PARTITION
-- ═══════════════════════════════════════════════════════════════════

/-- **Whole-partition `eps³` gain of the asymmetric 3-piece refinement.**  Let
    `R` be the remaining parts and `A, B` two further distinct parts; split only
    `B = B₁ ∪ B₂` disjointly, with the deviating piece `B₁` carrying the
    `eps`-mass floor and the `eps`-defect deviation against the parent density
    `d(A,B)`.  Then replacing `{A, B}` by `{A, B₁, B₂}` raises
    `partitionEnergy` by at least `eps³·|A||B|/n²`:

    `partitionEnergy G (insert A (insert B R)) + eps³·|A||B|/n²
        ≤ partitionEnergy G (insert A (insert B₁ (insert B₂ R)))`.

    The ordered-pair double sum decomposes as in
    `partitionEnergy_prod_refinement_gain`: the `R×R` block, the `(A,A)` cell
    and the `A`-rows/columns against `R` coincide on both sides; the
    `B`-rows/columns against `R`, the `(B,A)` cross and the `B²` diagonal split
    by pure `pairEnergy` monotonicity; and the single `(A,B)` cross carries the
    one-sided defect gain `pairEnergy_step3_gain` (S18). -/
theorem partitionEnergy_step3_refinement_gain (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset (Finset V)) (A B B₁ B₂ : Finset V)
    (hBunion : B₁ ∪ B₂ = B) (hdisjB : Disjoint B₁ B₂)
    -- coarse-side freshness
    (hAins : A ∉ insert B R) (hBR : B ∉ R)
    -- fine-side freshness
    (hAins' : A ∉ insert B₁ (insert B₂ R))
    (hB₁ins : B₁ ∉ insert B₂ R) (hB₂R : B₂ ∉ R)
    (eps : ℚ) (heps : 0 < eps)
    (hApos : 0 < (A.card : ℚ)) (hBpos : 0 < (B.card : ℚ))
    (hfloor : eps * B.card ≤ (B₁.card : ℚ))
    (hdev : eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|) :
    partitionEnergy G (insert A (insert B R)) +
        eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 ≤
      partitionEnergy G (insert A (insert B₁ (insert B₂ R))) := by
  -- `(A,B)` cross block: carries the S18 defect gain.
  have hAB : pairEnergy G A B +
        eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 ≤
      pairEnergy G A B₁ + pairEnergy G A B₂ :=
    pairEnergy_step3_gain G A B B₁ B₂ hBunion hdisjB eps heps hApos hBpos
      hfloor hdev
  -- `(B,A)` cross block (pure monotonicity).
  have hBA : pairEnergy G B A ≤ pairEnergy G B₁ A + pairEnergy G B₂ A := by
    have h := pairEnergy_split_mono G B₁ B₂ A hdisjB
    rwa [hBunion] at h
  -- diagonal `B²` block (pure monotonicity, both coordinates).
  have hBB : pairEnergy G B B ≤
      pairEnergy G B₁ B₁ + pairEnergy G B₁ B₂ +
        pairEnergy G B₂ B₁ + pairEnergy G B₂ B₂ := by
    have a := pairEnergy_split_mono G B₁ B₂ (B₁ ∪ B₂) hdisjB
    have b := pairEnergy_split_mono_right G B₁ B₁ B₂ hdisjB
    have c := pairEnergy_split_mono_right G B₂ B₁ B₂ hdisjB
    rw [hBunion] at a b c; linarith
  -- `B`-column against `R` splits.
  have hcolB : R.sum (fun Q => pairEnergy G B Q) ≤
      R.sum (fun Q => pairEnergy G B₁ Q) +
        R.sum (fun Q => pairEnergy G B₂ Q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun Q _ => ?_
    have h := pairEnergy_split_mono G B₁ B₂ Q hdisjB
    rwa [hBunion] at h
  -- `B`-row against `R` splits.
  have hrowB : R.sum (fun P => pairEnergy G P B) ≤
      R.sum (fun P => pairEnergy G P B₁) +
        R.sum (fun P => pairEnergy G P B₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun P _ => ?_
    have h := pairEnergy_split_mono_right G P B₁ B₂ hdisjB
    rwa [hBunion] at h
  -- Expand both partition energies to their block decompositions.
  rw [partitionEnergy_eq_double_sum, partitionEnergy_eq_double_sum]
  simp only [Finset.sum_insert hAins, Finset.sum_insert hBR,
    Finset.sum_insert hAins', Finset.sum_insert hB₁ins,
    Finset.sum_insert hB₂R, Finset.sum_add_distrib]
  linarith [hAB, hBA, hBB, hcolB, hrowB]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE MIXED-CHAIN ITERATION COUNT (BOTH STEP SHAPES)
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp iteration count for a mixed chain of witnessed steps.**  If every
    step `n < N` of a refinement chain is witnessed by EITHER shape — the
    symmetric 4-piece `IsWitnessedSharpStep` or the asymmetric 3-piece
    `IsWitnessedSharpStep3`, both at tolerance `eps ≤ 1` and mass floor `m` —
    then each step raises `partitionEnergy` by at least the uniform floor
    `eps⁴·m²/n²` (the 4-piece step by `partitionEnergy_prod_gain_eps4`, the
    3-piece step by the stronger `eps³ ≥ eps⁴` defect gain of Part I), so the
    `[0,1]`-potential engine caps the chain length at the SAME sharp budget as
    the pure 4-piece chain:

    `N ≤ n² / (eps⁴·m²)`.

    The degenerate branch of the S17 dichotomy therefore costs the outer loop
    nothing: its per-step gain is `eps³·m²/n² ≥ eps⁴·m²/n²`. -/
theorem afks_sharp_energy_iteration_count_of_witness_both
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (eps m : ℚ)
    (hε : 0 < eps) (hε1 : eps ≤ 1) (hm : 0 < m)
    (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hwit : ∀ n, n < N → IsWitnessedSharpStep G parts n eps m ∨
      IsWitnessedSharpStep3 G parts n eps m) :
    (N : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 / (eps ^ 4 * m ^ 2) := by
  refine afks_sharp_energy_iteration_count G parts N eps (m ^ 2) hε
    (by positivity) hcard hcover hdisjoint ?_
  intro n hn
  rcases hwit n hn with hstep | hstep
  · -- symmetric 4-piece step: the sharp `eps⁴` product gain.
    obtain ⟨R, A, B, A₁, A₂, B₁, B₂, hpn, hpn1, hAu, hBu, hdA, hdB,
      hAins, hBR, hA1, hA2, hB1, hB2, hmA, hmB, hcA, hcB, hdev⟩ := hstep
    rw [hpn, hpn1]
    have hgain := partitionEnergy_prod_gain_eps4 G R A B A₁ A₂ B₁ B₂
      hAu hBu hdA hdB hAins hBR hA1 hA2 hB1 hB2 eps hε.le hcA hcB hdev
    have hmass : m ^ 2 ≤ (A.card : ℚ) * B.card := by
      nlinarith [hmA, hmB, hm.le]
    have hfloor : eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
        eps ^ 4 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 := by
      gcongr
    linarith [hgain, hfloor]
  · -- asymmetric 3-piece step: the `eps³` defect gain dominates `eps⁴`.
    obtain ⟨R, A, B, B₁, B₂, hpn, hpn1, hBu, hdB, hAins, hBR, hAins',
      hB₁ins, hB₂R, hmA, hmB, hfl, hdev⟩ := hstep
    rw [hpn, hpn1]
    have hApos : 0 < (A.card : ℚ) := lt_of_lt_of_le hm hmA
    have hBpos : 0 < (B.card : ℚ) := lt_of_lt_of_le hm hmB
    have hgain := partitionEnergy_step3_refinement_gain G R A B B₁ B₂
      hBu hdB hAins hBR hAins' hB₁ins hB₂R eps hε hApos hBpos hfl hdev
    -- `eps⁴·m² ≤ eps³·m² ≤ eps³·|A||B|` (one power of `eps ≤ 1` is dropped).
    have hmass : m ^ 2 ≤ (A.card : ℚ) * B.card := by
      nlinarith [hmA, hmB, hm.le]
    have heps3 : (0 : ℚ) ≤ eps ^ 3 := by positivity
    have h43 : eps ^ 4 ≤ eps ^ 3 := by
      nlinarith [mul_nonneg heps3 (sub_nonneg.mpr hε1)]
    have hnum : eps ^ 4 * m ^ 2 ≤ eps ^ 3 * ((A.card : ℚ) * B.card) :=
      mul_le_mul h43 hmass (sq_nonneg m) heps3
    have hfloor : eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
        eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    linarith [hgain, hfloor]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: TERMINATION AGAINST BOTH SHAPES
-- ═══════════════════════════════════════════════════════════════════

/-- **Termination for the two-shape loop.**  Past the sharp budget
    `n²/(eps⁴·m²)`, some step `n < N` carries NEITHER witness shape: it is not
    a symmetric 4-piece sharp step and not an asymmetric 3-piece defect step.
    This is the contrapositive of the mixed-chain iteration count, and the
    exact hook the two-shape dichotomy needs — at that step the S17 case split
    can produce no refinement, so the partition must already be fine-regular. -/
theorem afks_regular_step_within_bound_both
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (eps m : ℚ)
    (hε : 0 < eps) (hε1 : eps ≤ 1) (hm : 0 < m)
    (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Fintype.card V : ℚ) ^ 2 / (eps ^ 4 * m ^ 2) < N) :
    ∃ n < N, ¬ (IsWitnessedSharpStep G parts n eps m ∨
      IsWitnessedSharpStep3 G parts n eps m) := by
  by_contra hcon
  push_neg at hcon
  have hle := afks_sharp_energy_iteration_count_of_witness_both
    G parts N eps m hε hε1 hm hcard hcover hdisjoint hcon
  exact absurd hle (not_le.mpr hN)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE OUTER LOOP, RE-THREADED WITH BOTH STEP SHAPES
-- ═══════════════════════════════════════════════════════════════════

/-- **The outer AFKS loop with the two-shape dichotomy (S17 residual (b)).**
    Identical wiring to `exists_afksTwoLevel_of_dichotomy` (Outer.lean), but
    the regular-or-refine dichotomy hypothesis now concludes the DISJUNCTION of
    step shapes — a witnessed symmetric 4-piece sharp step OR a witnessed
    asymmetric 3-piece defect step — which is exactly what the S17 case split
    `exists_proper_or_semitrivial_split_of_not_afksFineRegular` yields for a
    non-fine-regular partition.

    Past the sharp budget the mixed-chain termination finds a step with
    NEITHER witness; by the dichotomy's contrapositive that partition is
    AFKS-fine-regular, and it packages with the coarse `ε`-regular `Vparts`
    into the two-level conclusion.  The extra hypothesis over the one-shape
    version is only `E(k) ≤ 1` (needed so the 3-piece `eps³` gain dominates the
    common `eps⁴` budget); every tolerance of interest satisfies it. -/
theorem exists_afksTwoLevel_of_dichotomy_both
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (Vparts : Finset (Finset V))
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (m : ℚ)
    (hEpos : 0 < E Vparts.card) (hE1 : E Vparts.card ≤ 1) (hm : 0 < m)
    (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Fintype.card V : ℚ) ^ 2 / (E Vparts.card ^ 4 * m ^ 2) < N)
    (hcoarse : IsRegularPartition G ε Vparts)
    (href : ∀ n, IsRefinement (parts n) Vparts)
    (hdich : ∀ n, n < N → ¬ IsAFKSFineRegular G ε (E Vparts.card) (parts n) →
      IsWitnessedSharpStep G parts n (E Vparts.card) m ∨
      IsWitnessedSharpStep3 G parts n (E Vparts.card) m) :
    ∃ n < N, IsAFKSTwoLevel G ε E Vparts (parts n) := by
  obtain ⟨n, hn, hno⟩ := afks_regular_step_within_bound_both
    G parts N (E Vparts.card) m hEpos hE1 hm hcard hcover hdisjoint hN
  refine ⟨n, hn, ?_⟩
  have hfine : IsAFKSFineRegular G ε (E Vparts.card) (parts n) := by
    by_contra hcon
    exact hno (hdich n hn hcon)
  exact
    { coarseRegular := hcoarse
      refines := href n
      fineRegular := hfine }

/-- **Vertex-count-free (tower-free) horizon form of the two-shape loop.**
    Identical conclusion to `exists_afksTwoLevel_of_dichotomy_both`, with the
    horizon stated in the dimension-free `k²/E(k)⁴` shape via the
    equipartition mass floor `m = n/k`, exactly as in
    `exists_afksTwoLevel_of_dichotomy_equipartition`. -/
theorem exists_afksTwoLevel_of_dichotomy_both_equipartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (Vparts : Finset (Finset V))
    (parts : ℕ → Finset (Finset V)) (N : ℕ)
    (hEpos : 0 < E Vparts.card) (hE1 : E Vparts.card ≤ 1)
    (hkpos : 0 < Vparts.card) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Vparts.card : ℚ) ^ 2 / E Vparts.card ^ 4 < N)
    (hcoarse : IsRegularPartition G ε Vparts)
    (href : ∀ n, IsRefinement (parts n) Vparts)
    (hdich : ∀ n, n < N → ¬ IsAFKSFineRegular G ε (E Vparts.card) (parts n) →
      IsWitnessedSharpStep G parts n (E Vparts.card)
        ((Fintype.card V : ℚ) / Vparts.card) ∨
      IsWitnessedSharpStep3 G parts n (E Vparts.card)
        ((Fintype.card V : ℚ) / Vparts.card)) :
    ∃ n < N, IsAFKSTwoLevel G ε E Vparts (parts n) := by
  set k : ℚ := (Vparts.card : ℚ) with hk
  set n : ℚ := (Fintype.card V : ℚ) with hnc
  have hkq : (0 : ℚ) < k := by rw [hk]; exact_mod_cast hkpos
  have hmpos : (0 : ℚ) < n / k := div_pos hcard hkq
  have hEne : E Vparts.card ≠ 0 := hEpos.ne'
  have hkne : k ≠ 0 := hkq.ne'
  have hnne : n ≠ 0 := hcard.ne'
  -- `n² / (E(k)⁴ · (n/k)²) = k² / E(k)⁴`.
  have heq : n ^ 2 / (E Vparts.card ^ 4 * (n / k) ^ 2) =
      k ^ 2 / E Vparts.card ^ 4 := by
    field_simp
  refine exists_afksTwoLevel_of_dichotomy_both G ε E Vparts parts N (n / k)
    hEpos hE1 hmpos hcard hcover hdisjoint ?_ hcoarse href hdich
  rw [heq]; exact hN

end Szemeredi.RegularityOQ04OuterBoth
