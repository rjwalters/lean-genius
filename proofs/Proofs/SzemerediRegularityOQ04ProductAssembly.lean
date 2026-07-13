/-
  Szemerédi Regularity Lemma — OQ-04: lifting the *sharp* m×k product energy
  increment to the whole partition.

  The companion file `SzemerediRegularityOQ04Product` proves the sharp per-pair
  m×k increment `pairEnergy_prod_family_refinement_gain`: refining a pair `(A, B)`
  simultaneously on *both* coordinates into an arbitrary disjoint product grid
  `{Aᵢ}_{i∈I} × {Bⱼ}_{j∈J}` (with `A = ⋃Aᵢ`, `B = ⋃Bⱼ`) raises the double-sum
  `pairEnergy` by at least `(|A_{i₀}||B_{j₀}|/n²)·d²` whenever a single witness
  sub-cell `(i₀,j₀)` deviates from `d(A,B)` by `≥ d`.  That statement lives only at
  the `pairEnergy` level.  Its 2×2 special case was lifted to `partitionEnergy` in
  `SzemerediRegularityOQ04Assembly` (`partitionEnergy_prod_refinement_gain`); this
  file discharges the documented next step by lifting the **arbitrary m×k** gain to
  the whole partition.

  The structural monotonicity toolkit — the m-fold `pairEnergy` split lemmas
  `pairEnergy_biUnion_split_mono` / `_right` — comes from
  `SzemerediRegularityOQ04FamilySplit`.

  ## What this file proves (0 axioms, 0 sorries)

  * `partitionEnergy_prod_family_refinement_gain` — **the m×k whole-partition
    refinement gain.**  Replacing two distinct parts `A = ⋃Aᵢ`, `B = ⋃Bⱼ` of a
    partition by the product grid `{Aᵢ} × {Bⱼ}` raises `partitionEnergy` by the sharp
    increment `(|A_{i₀}||B_{j₀}|/n²)·d²`.  The ordered-pair double sum decomposes
    into: the untouched `R×R` block; the `A,B` rows/columns against the remaining
    parts `R` (each splits by the m-fold `pairEnergy` monotonicity of PART I of
    FamilySplit); the diagonal `A²`, `B²` blocks and the `(B,A)` cross (pure
    monotonicity on both coordinates); and the single `(A,B)` cross, which carries the
    variance-atom gain via `pairEnergy_prod_family_refinement_gain`.

  * `partitionEnergy_prod_family_gain_eps` — the AFKS-consumable `ε⁴` floor of the
    same lift: with the witness thresholds `|A_{i₀}| ≥ ε|A|`, `|B_{j₀}| ≥ ε|B|`,
    `d(A_{i₀},B_{j₀})` deviating from `d(A,B)` by `≥ ε`, the whole-partition energy
    jump is at least `ε⁴·|A||B|/n²`, depending only on `ε` and the *original* part
    sizes, not on the witness sub-cell.

  This is the full-generality partition-level energy increment — the arbitrary-family
  generalization of the 2×2 `partitionEnergy_prod_refinement_gain` — and the sharp
  per-step jump the AFKS finiteness engine (`afks_sharp_energy_iteration_count`)
  consumes.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FamilySplit
import Proofs.SzemerediRegularityOQ04Product

namespace Szemeredi.RegularityOQ04ProductAssembly

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge
open Szemeredi.RegularityOQ04FamilySplit

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- THE SHARP m×k PRODUCT ENERGY INCREMENT, LIFTED TO THE WHOLE PARTITION
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp whole-partition m×k product-refinement gain.**  Let `R` be the remaining
    parts of a partition and `A = ⋃_{i∈I} Aᵢ`, `B = ⋃_{j∈J} Bⱼ` two further distinct
    parts, refined disjointly into the arbitrary product grid `{Aᵢ}_{i∈I} × {Bⱼ}_{j∈J}`.
    If a single witness cell `(i₀, j₀)` has density `d(A_{i₀}, B_{j₀})` deviating from
    the coarse density `d(A, B)` by at least `d`, then refining the partition by the
    product grid raises `partitionEnergy` by the sharp increment `(|A_{i₀}||B_{j₀}|/n²)·d²`:

    `partitionEnergy G (insert A (insert B R)) + (|A_{i₀}||B_{j₀}|/n²)·d²
        ≤ partitionEnergy G (I.image As ∪ (J.image Bs ∪ R))`.

    This is the arbitrary-family generalization of `partitionEnergy_prod_refinement_gain`
    (the 2×2 case).  The ordered-pair double sum decomposes into: the `R×R` block
    (identical on both partitions); the `A,B` rows/columns against `R` (each splits by
    the m-fold `pairEnergy_biUnion_split_mono` / `_right`); and the `{A,B}²` block, whose
    four coarse terms refine into `m·k` sub-cells — the diagonal `A²`, `B²` and the
    `(B,A)` cross by monotonicity, and the single `(A,B)` cross carrying the
    variance-atom gain (`pairEnergy_prod_family_refinement_gain`). -/
theorem partitionEnergy_prod_family_refinement_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (R : Finset (Finset V)) (I : Finset ι) (J : Finset κ)
    (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs)
    (hinjA : Set.InjOn As ↑I) (hinjB : Set.InjOn Bs ↑J)
    -- freshness of the fine cells
    (hAR : ∀ i ∈ I, As i ∉ R) (hBR : ∀ j ∈ J, Bs j ∉ R)
    (hAB : ∀ i ∈ I, ∀ j ∈ J, As i ≠ Bs j)
    -- freshness of the coarse parts
    (hAfresh : I.biUnion As ∉ insert (J.biUnion Bs) R) (hBfresh : J.biUnion Bs ∉ R)
    (i₀ : ι) (j₀ : κ) (hi₀ : i₀ ∈ I) (hj₀ : j₀ ∈ J)
    (d : ℚ) (hd : 0 ≤ d)
    (hdev : d ≤ |edgeDensity G (As i₀) (Bs j₀) -
                  edgeDensity G (I.biUnion As) (J.biUnion Bs)|) :
    partitionEnergy G (insert (I.biUnion As) (insert (J.biUnion Bs) R)) +
        (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      partitionEnergy G (I.image As ∪ (J.image Bs ∪ R)) := by
  classical
  -- Image-sum reindexing via injectivity.
  have himgA : ∀ F : Finset V → ℚ, ∑ P ∈ I.image As, F P = ∑ i ∈ I, F (As i) := by
    intro F; rw [Finset.sum_image]
    intro x hx y hy h; exact hinjA (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
  have himgB : ∀ F : Finset V → ℚ, ∑ P ∈ J.image Bs, F P = ∑ j ∈ J, F (Bs j) := by
    intro F; rw [Finset.sum_image]
    intro x hx y hy h; exact hinjB (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
  -- Disjointness of the three fine blocks.
  have hdisjSB_R : Disjoint (J.image Bs) R := by
    rw [Finset.disjoint_left]; intro x hx hxR
    rw [Finset.mem_image] at hx; obtain ⟨j, hj, rfl⟩ := hx; exact hBR j hj hxR
  have hdisjSA_rest : Disjoint (I.image As) (J.image Bs ∪ R) := by
    rw [Finset.disjoint_left]; intro x hx hxU
    rw [Finset.mem_image] at hx; obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_union] at hxU
    rcases hxU with h | h
    · rw [Finset.mem_image] at h; obtain ⟨j, hj, hji⟩ := h
      exact hAB i hi j hj hji.symm
    · exact hAR i hi h
  -- Nested-double-sum form of `partitionEnergy`.
  have hdouble : ∀ parts : Finset (Finset V),
      partitionEnergy G parts = ∑ P ∈ parts, ∑ Q ∈ parts, pairEnergy G P Q := by
    intro parts
    rw [partitionEnergy_eq_sum_pairEnergy,
      show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  -- LHS (coarse) block decomposition.
  have hL : partitionEnergy G (insert (I.biUnion As) (insert (J.biUnion Bs) R))
      = pairEnergy G (I.biUnion As) (I.biUnion As)
        + pairEnergy G (I.biUnion As) (J.biUnion Bs)
        + (∑ Q ∈ R, pairEnergy G (I.biUnion As) Q)
        + pairEnergy G (J.biUnion Bs) (I.biUnion As)
        + pairEnergy G (J.biUnion Bs) (J.biUnion Bs)
        + (∑ Q ∈ R, pairEnergy G (J.biUnion Bs) Q)
        + (∑ P ∈ R, pairEnergy G P (I.biUnion As))
        + (∑ P ∈ R, pairEnergy G P (J.biUnion Bs))
        + (∑ P ∈ R, ∑ Q ∈ R, pairEnergy G P Q) := by
    rw [hdouble]
    simp only [Finset.sum_insert hAfresh, Finset.sum_insert hBfresh,
      Finset.sum_add_distrib]
    ring
  -- RHS (fine) block decomposition.
  have hR : partitionEnergy G (I.image As ∪ (J.image Bs ∪ R))
      = (∑ i ∈ I, ∑ i' ∈ I, pairEnergy G (As i) (As i'))
        + (∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j))
        + (∑ i ∈ I, ∑ Q ∈ R, pairEnergy G (As i) Q)
        + (∑ j ∈ J, ∑ i ∈ I, pairEnergy G (Bs j) (As i))
        + (∑ j ∈ J, ∑ j' ∈ J, pairEnergy G (Bs j) (Bs j'))
        + (∑ j ∈ J, ∑ Q ∈ R, pairEnergy G (Bs j) Q)
        + (∑ P ∈ R, ∑ i ∈ I, pairEnergy G P (As i))
        + (∑ P ∈ R, ∑ j ∈ J, pairEnergy G P (Bs j))
        + (∑ P ∈ R, ∑ Q ∈ R, pairEnergy G P Q) := by
    rw [hdouble]
    simp only [Finset.sum_union hdisjSA_rest, Finset.sum_union hdisjSB_R,
      Finset.sum_add_distrib, himgA, himgB]
    ring
  -- Diagonal `A²` block (pure two-coordinate monotonicity).
  have hAA : pairEnergy G (I.biUnion As) (I.biUnion As)
      ≤ ∑ i ∈ I, ∑ i' ∈ I, pairEnergy G (As i) (As i') := by
    refine (pairEnergy_biUnion_split_mono G I As (I.biUnion As) hA).trans ?_
    exact Finset.sum_le_sum
      (fun i _ => pairEnergy_biUnion_split_mono_right G (As i) I As hA)
  -- Diagonal `B²` block.
  have hBB : pairEnergy G (J.biUnion Bs) (J.biUnion Bs)
      ≤ ∑ j ∈ J, ∑ j' ∈ J, pairEnergy G (Bs j) (Bs j') := by
    refine (pairEnergy_biUnion_split_mono G J Bs (J.biUnion Bs) hB).trans ?_
    exact Finset.sum_le_sum
      (fun j _ => pairEnergy_biUnion_split_mono_right G (Bs j) J Bs hB)
  -- `(A,B)` cross block: carries the variance-atom gain.
  have hABgain : pairEnergy G (I.biUnion As) (J.biUnion Bs) +
        (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) :=
    pairEnergy_prod_family_refinement_gain G I J As Bs hA hB i₀ j₀ hi₀ hj₀ d hd hdev
  -- `(B,A)` cross block (pure monotonicity).
  have hBA : pairEnergy G (J.biUnion Bs) (I.biUnion As)
      ≤ ∑ j ∈ J, ∑ i ∈ I, pairEnergy G (Bs j) (As i) := by
    refine (pairEnergy_biUnion_split_mono G J Bs (I.biUnion As) hB).trans ?_
    exact Finset.sum_le_sum
      (fun j _ => pairEnergy_biUnion_split_mono_right G (Bs j) I As hA)
  -- Column sums against `R`: `d(A,·)` splits, `d(B,·)` splits.
  have hrowA : ∑ Q ∈ R, pairEnergy G (I.biUnion As) Q
      ≤ ∑ i ∈ I, ∑ Q ∈ R, pairEnergy G (As i) Q := by
    have step : ∑ Q ∈ R, pairEnergy G (I.biUnion As) Q
        ≤ ∑ Q ∈ R, ∑ i ∈ I, pairEnergy G (As i) Q :=
      Finset.sum_le_sum (fun Q _ => pairEnergy_biUnion_split_mono G I As Q hA)
    rwa [Finset.sum_comm] at step
  have hrowB : ∑ Q ∈ R, pairEnergy G (J.biUnion Bs) Q
      ≤ ∑ j ∈ J, ∑ Q ∈ R, pairEnergy G (Bs j) Q := by
    have step : ∑ Q ∈ R, pairEnergy G (J.biUnion Bs) Q
        ≤ ∑ Q ∈ R, ∑ j ∈ J, pairEnergy G (Bs j) Q :=
      Finset.sum_le_sum (fun Q _ => pairEnergy_biUnion_split_mono G J Bs Q hB)
    rwa [Finset.sum_comm] at step
  -- Row sums against `R`: `d(·,A)` splits, `d(·,B)` splits.
  have hcolA : ∑ P ∈ R, pairEnergy G P (I.biUnion As)
      ≤ ∑ P ∈ R, ∑ i ∈ I, pairEnergy G P (As i) :=
    Finset.sum_le_sum (fun P _ => pairEnergy_biUnion_split_mono_right G P I As hA)
  have hcolB : ∑ P ∈ R, pairEnergy G P (J.biUnion Bs)
      ≤ ∑ P ∈ R, ∑ j ∈ J, pairEnergy G P (Bs j) :=
    Finset.sum_le_sum (fun P _ => pairEnergy_biUnion_split_mono_right G P J Bs hB)
  rw [hL, hR]
  linarith [hAA, hBB, hABgain, hBA, hrowA, hrowB, hcolA, hcolB]

/-- **AFKS-consumable `ε⁴` floor of the sharp whole-partition m×k gain.**  Flooring the
    size-dependent increment `(|A_{i₀}||B_{j₀}|/n²)·ε²` by the witness thresholds
    `|A_{i₀}| ≥ ε|A|`, `|B_{j₀}| ≥ ε|B|`, an ε-irregular pair refined simultaneously into
    an arbitrary product grid raises the whole-partition energy by at least
    `ε⁴·|A||B|/n²` — the sharp partition-level jump, depending only on `ε` and the
    original part sizes `|A|, |B|`. -/
theorem partitionEnergy_prod_family_gain_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (R : Finset (Finset V)) (I : Finset ι) (J : Finset κ)
    (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs)
    (hinjA : Set.InjOn As ↑I) (hinjB : Set.InjOn Bs ↑J)
    (hAR : ∀ i ∈ I, As i ∉ R) (hBR : ∀ j ∈ J, Bs j ∉ R)
    (hAB : ∀ i ∈ I, ∀ j ∈ J, As i ≠ Bs j)
    (hAfresh : I.biUnion As ∉ insert (J.biUnion Bs) R) (hBfresh : J.biUnion Bs ∉ R)
    (i₀ : ι) (j₀ : κ) (hi₀ : i₀ ∈ I) (hj₀ : j₀ ∈ J)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hAcard : ε * ↑(I.biUnion As).card ≤ (↑(As i₀).card : ℚ))
    (hBcard : ε * ↑(J.biUnion Bs).card ≤ (↑(Bs j₀).card : ℚ))
    (hdev : ε ≤ |edgeDensity G (As i₀) (Bs j₀) -
                  edgeDensity G (I.biUnion As) (J.biUnion Bs)|) :
    partitionEnergy G (insert (I.biUnion As) (insert (J.biUnion Bs) R)) +
        ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2 ≤
      partitionEnergy G (I.image As ∪ (J.image Bs ∪ R)) := by
  have hgain := partitionEnergy_prod_family_refinement_gain G R I J As Bs hA hB
    hinjA hinjB hAR hBR hAB hAfresh hBfresh i₀ j₀ hi₀ hj₀ ε hε hdev
  -- Replace the witness-cell gain by the uniform `ε⁴|A||B|` lower bound.
  have hcore : ε * ↑(I.biUnion As).card * (ε * ↑(J.biUnion Bs).card)
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card :=
    mul_le_mul hAcard hBcard (mul_nonneg hε (by positivity)) (by positivity)
  have key : ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card * ε ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcore (sq_nonneg ε)]
  have hinv : (0 : ℚ) ≤ 1 / (Fintype.card V : ℚ) ^ 2 := by positivity
  have hstep : ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * ε ^ 2 :=
    calc ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2
        = (ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card)
            * (1 / (Fintype.card V : ℚ) ^ 2) := by ring
      _ ≤ ((↑(As i₀).card : ℚ) * ↑(Bs j₀).card * ε ^ 2)
            * (1 / (Fintype.card V : ℚ) ^ 2) := mul_le_mul_of_nonneg_right key hinv
      _ = (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * ε ^ 2 := by ring
  linarith [hgain, hstep]

end Szemeredi.RegularityOQ04ProductAssembly
