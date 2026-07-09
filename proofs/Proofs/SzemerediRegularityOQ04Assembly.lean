/-
  Szemerédi Regularity Lemma — OQ-04: lifting the *sharp* direct 2×2 energy
  increment to the whole partition.

  The companion file `SzemerediRegularityOQ04Bridge` proves the sharp per-pair
  increment `pairEnergy_prod_gain_of_irregular_eps4`: refining an ε-irregular pair
  `(A, B)` simultaneously on *both* coordinates into the 2×2 grid
  `{A′, A∖A′} × {B′, B∖B′}` raises the four-cell `pairEnergy` sum by at least
  `ε⁴·|A||B|/n²` — with **no factor-¼ loss**.  That statement, however, lives only
  at the `pairEnergy` level.  The whole-partition capstone that actually feeds the
  AFKS finiteness engine (`partitionEnergy_gain_of_irregular_pair`) still routes
  through the *one-sided* branches and therefore only realizes the lossy floor
  `(ε/2)²/(2n²) = ε²/(8n²)`.

  This file closes that gap: it lifts the **sharp** 2×2 gain to `partitionEnergy`.

  * `partitionEnergy_prod_refinement_gain` — replacing two distinct parts `A, B`
    of a partition by the 2×2 grid `{A′, A∖A′} × {B′, B∖B′}` raises
    `partitionEnergy` by the sharp size-dependent increment `(|A′||B′|/n²)·d²`,
    where `d = |d(A′,B′) − d(A,B)|` is the witness deviation.  The proof is the
    two-coordinate analogue of `partitionEnergy_single_split_gain`: expand the
    ordered-pair sum into blocks; the `R×R` block is untouched, every row/column
    against the remaining parts `R` splits by pure `pairEnergy` monotonicity, and
    the `{A,B}²` block refines into its sixteen sub-cells with the single `(A,B)`
    cross-block carrying the variance-atom gain (`pairEnergy_prod_refinement_gain`).

  * `partitionEnergy_prod_gain_eps4` — the AFKS-consumable `ε⁴` floor of the same
    lift: with the witness size thresholds `|A′| ≥ ε|A|`, `|B′| ≥ ε|B|`, the
    increment is at least `ε⁴·|A||B|/n²`, the sharp partition-level energy jump
    free of the one-sided factor-¼ loss.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Bridge

namespace Szemeredi.RegularityOQ04Bridge

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bridge in nested-double-sum form (local re-derivation of the Bridge file's
    `private` helper), convenient for block decompositions. -/
private theorem partitionEnergy_eq_double_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      parts.sum (fun P => parts.sum (fun Q => pairEnergy G P Q)) := by
  rw [partitionEnergy_eq_sum_pairEnergy,
    show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]

-- ═══════════════════════════════════════════════════════════════════
-- THE SHARP DIRECT 2×2 ENERGY INCREMENT, LIFTED TO THE WHOLE PARTITION
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp whole-partition 2×2 refinement gain.**  Let `R` be the remaining parts
    of a partition and `A, B` two further distinct parts, split disjointly as
    `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` (the witness cell being `A₁ × B₁`).  If the witness
    density `d(A₁, B₁)` deviates from the coarse density `d(A, B)` by at least `d`,
    then refining the partition by the 2×2 grid `{A₁, A₂} × {B₁, B₂}` raises
    `partitionEnergy` by the sharp increment `(|A₁||B₁|/n²)·d²`:

    `partitionEnergy G (insert A (insert B R)) + (|A₁||B₁|/n²)·d²
        ≤ partitionEnergy G (insert A₁ (insert A₂ (insert B₁ (insert B₂ R))))`.

    Unlike the one-sided routes (`partitionEnergy_Aside_gain_of_irregular`), which
    keep one coordinate whole and pay a factor-¼ tolerance loss through a triangle
    detour, the deviation here is measured *directly* against `d(A,B)` and consumed
    by the 2×2 variance-atom gain `pairEnergy_prod_refinement_gain` with no loss.

    The ordered-pair double sum decomposes into: the `R×R` block (identical on both
    partitions); the `A,B` rows/columns against `R` (each splits by pure
    `pairEnergy_split_mono` / `_mono_right`); and the `{A,B}²` block, whose four
    coarse terms refine into sixteen sub-cells — the diagonal `A²`, `B²` blocks and
    the `(B,A)` cross by monotonicity, and the single `(A,B)` cross carrying the
    variance-atom gain. -/
theorem partitionEnergy_prod_refinement_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hAunion : A₁ ∪ A₂ = A) (hBunion : B₁ ∪ B₂ = B)
    (hdisjA : Disjoint A₁ A₂) (hdisjB : Disjoint B₁ B₂)
    -- coarse-side freshness
    (hAins : A ∉ insert B R) (hBR : B ∉ R)
    -- fine-side freshness
    (hA₁ins : A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)))
    (hA₂ins : A₂ ∉ insert B₁ (insert B₂ R))
    (hB₁ins : B₁ ∉ insert B₂ R) (hB₂R : B₂ ∉ R)
    (d : ℚ) (hd : 0 ≤ d)
    (hdev : d ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    partitionEnergy G (insert A (insert B R)) +
        (↑A₁.card : ℚ) * ↑B₁.card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      partitionEnergy G
        (insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))) := by
  -- Block inequalities.  Diagonal `A²` block (pure monotonicity).
  have hAA : pairEnergy G A A ≤
      pairEnergy G A₁ A₁ + pairEnergy G A₁ A₂ +
        pairEnergy G A₂ A₁ + pairEnergy G A₂ A₂ := by
    have a := pairEnergy_split_mono G A₁ A₂ (A₁ ∪ A₂) hdisjA
    have b := pairEnergy_split_mono_right G A₁ A₁ A₂ hdisjA
    have c := pairEnergy_split_mono_right G A₂ A₁ A₂ hdisjA
    rw [hAunion] at a b c; linarith
  -- Diagonal `B²` block (pure monotonicity).
  have hBB : pairEnergy G B B ≤
      pairEnergy G B₁ B₁ + pairEnergy G B₁ B₂ +
        pairEnergy G B₂ B₁ + pairEnergy G B₂ B₂ := by
    have a := pairEnergy_split_mono G B₁ B₂ (B₁ ∪ B₂) hdisjB
    have b := pairEnergy_split_mono_right G B₁ B₁ B₂ hdisjB
    have c := pairEnergy_split_mono_right G B₂ B₁ B₂ hdisjB
    rw [hBunion] at a b c; linarith
  -- `(A,B)` cross block: carries the variance-atom gain.
  have hAB : pairEnergy G A B +
        (↑A₁.card : ℚ) * ↑B₁.card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      pairEnergy G A₁ B₁ + pairEnergy G A₁ B₂ +
        pairEnergy G A₂ B₁ + pairEnergy G A₂ B₂ := by
    have hdev' : d ≤
        |edgeDensity G A₁ B₁ - edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)| := by
      rw [hAunion, hBunion]; exact hdev
    have g := pairEnergy_prod_refinement_gain G A₁ A₂ B₁ B₂ hdisjA hdisjB d hd hdev'
    rw [hAunion, hBunion] at g; exact g
  -- `(B,A)` cross block (pure monotonicity).
  have hBA : pairEnergy G B A ≤
      pairEnergy G B₁ A₁ + pairEnergy G B₁ A₂ +
        pairEnergy G B₂ A₁ + pairEnergy G B₂ A₂ := by
    have a := pairEnergy_split_mono G B₁ B₂ (A₁ ∪ A₂) hdisjB
    have b := pairEnergy_split_mono_right G B₁ A₁ A₂ hdisjA
    have c := pairEnergy_split_mono_right G B₂ A₁ A₂ hdisjA
    rw [hAunion, hBunion] at a b c; linarith
  -- Column sums against `R`: `d(A,·)` splits, `d(B,·)` splits.
  have hcolA : R.sum (fun Q => pairEnergy G A Q) ≤
      R.sum (fun Q => pairEnergy G A₁ Q) + R.sum (fun Q => pairEnergy G A₂ Q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun Q _ => ?_
    have := pairEnergy_split_mono G A₁ A₂ Q hdisjA; rwa [hAunion] at this
  have hcolB : R.sum (fun Q => pairEnergy G B Q) ≤
      R.sum (fun Q => pairEnergy G B₁ Q) + R.sum (fun Q => pairEnergy G B₂ Q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun Q _ => ?_
    have := pairEnergy_split_mono G B₁ B₂ Q hdisjB; rwa [hBunion] at this
  -- Row sums against `R`: `d(·,A)` splits, `d(·,B)` splits.
  have hrowA : R.sum (fun P => pairEnergy G P A) ≤
      R.sum (fun P => pairEnergy G P A₁) + R.sum (fun P => pairEnergy G P A₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun P _ => ?_
    have := pairEnergy_split_mono_right G P A₁ A₂ hdisjA; rwa [hAunion] at this
  have hrowB : R.sum (fun P => pairEnergy G P B) ≤
      R.sum (fun P => pairEnergy G P B₁) + R.sum (fun P => pairEnergy G P B₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun P _ => ?_
    have := pairEnergy_split_mono_right G P B₁ B₂ hdisjB; rwa [hBunion] at this
  -- Expand both partition energies to their block decompositions.
  rw [partitionEnergy_eq_double_sum, partitionEnergy_eq_double_sum]
  simp only [Finset.sum_insert hAins, Finset.sum_insert hBR,
    Finset.sum_insert hA₁ins, Finset.sum_insert hA₂ins,
    Finset.sum_insert hB₁ins, Finset.sum_insert hB₂R,
    Finset.sum_add_distrib]
  linarith [hAA, hBB, hAB, hBA, hcolA, hcolB, hrowA, hrowB]

/-- **AFKS-consumable `ε⁴` floor of the sharp whole-partition 2×2 gain.**  Flooring
    the size-dependent increment `(|A₁||B₁|/n²)·d²` by the size thresholds
    `|A₁| ≥ ε|A|`, `|B₁| ≥ ε|B|`, `d ≥ ε`, an ε-irregular pair refined
    simultaneously on both coordinates raises the whole-partition energy by at least
    `ε⁴·|A||B|/n²` — the sharp partition-level jump, free of the factor-¼ loss the
    one-sided branches (`partitionEnergy_gain_of_irregular_pair`) incur. -/
theorem partitionEnergy_prod_gain_eps4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hAunion : A₁ ∪ A₂ = A) (hBunion : B₁ ∪ B₂ = B)
    (hdisjA : Disjoint A₁ A₂) (hdisjB : Disjoint B₁ B₂)
    (hAins : A ∉ insert B R) (hBR : B ∉ R)
    (hA₁ins : A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)))
    (hA₂ins : A₂ ∉ insert B₁ (insert B₂ R))
    (hB₁ins : B₁ ∉ insert B₂ R) (hB₂R : B₂ ∉ R)
    (eps : ℚ) (hε : 0 ≤ eps)
    (hcardA : eps * A.card ≤ (A₁.card : ℚ)) (hcardB : eps * B.card ≤ (B₁.card : ℚ))
    (hdev : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    partitionEnergy G (insert A (insert B R)) +
        eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2 ≤
      partitionEnergy G
        (insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))) := by
  have hgain := partitionEnergy_prod_refinement_gain G R A B A₁ A₂ B₁ B₂
    hAunion hBunion hdisjA hdisjB hAins hBR hA₁ins hA₂ins hB₁ins hB₂R eps hε hdev
  -- Floor the exact cell increment `(|A₁||B₁|/n²)·ε²` by `ε⁴·|A||B|/n²`.
  have hcard : (eps * A.card) * (eps * B.card) ≤ (↑A₁.card : ℚ) * ↑B₁.card :=
    mul_le_mul hcardA hcardB (by positivity) (by positivity)
  have he2 : (0 : ℚ) ≤ eps ^ 2 / (Fintype.card V : ℚ) ^ 2 := by positivity
  have hfloor : eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2
      ≤ (↑A₁.card : ℚ) * ↑B₁.card / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 :=
    calc eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2
        = (eps * A.card) * (eps * B.card) * (eps ^ 2 / (Fintype.card V : ℚ) ^ 2) := by
          ring
      _ ≤ (↑A₁.card : ℚ) * ↑B₁.card * (eps ^ 2 / (Fintype.card V : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard he2
      _ = (↑A₁.card : ℚ) * ↑B₁.card / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 := by ring
  linarith [hgain, hfloor]

end Szemeredi.RegularityOQ04Bridge
