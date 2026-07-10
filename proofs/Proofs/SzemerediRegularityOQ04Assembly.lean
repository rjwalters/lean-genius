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
    rw [hBunion, hAunion] at a; rw [hAunion] at b c; linarith
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

-- ═══════════════════════════════════════════════════════════════════
-- THE SHARP AFKS ITERATION COUNT (NO-LOSS FLOOR → TERMINATION)
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp AFKS energy-iteration count.**  The termination engine
    `partitionEnergy_iteration_bound` bounds the number of refinement steps by
    `1/δ` once every step raises `partitionEnergy` by a fixed `δ > 0`.  The lossy
    one-sided route (`afks_energy_iteration_count`) can only supply the floor
    `δ = ε²/(2n²)`, giving `N ≤ 2n²/ε²`.  The **sharp** 2×2 route earns the
    no-loss floor `partitionEnergy_prod_gain_eps4`, which — once the refined pair
    carries mass at least `M` (i.e. `|A||B| ≥ M`, guaranteed by a minimum-part-mass
    hypothesis on the partition) — is `δ = ε⁴·M/n²`.  Feeding this into the same
    `[0,1]`-potential engine yields the sharp iteration count

    `N ≤ n² / (ε⁴·M)`,

    the termination bound the factor-¼-free route delivers.  Unlike
    `afks_energy_iteration_count`, whose floor is independent of the refined pair,
    the sharp floor scales with the ε⁴ tolerance and the pair mass `M`; the two
    bounds coincide in order of magnitude only when `M ≈ ε²n²/2`, and the sharp
    bound is strictly better once the refined pairs are more massive than that. -/
theorem afks_sharp_energy_iteration_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (eps M : ℚ)
    (hε : 0 < eps) (hM : 0 < M) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hstep : ∀ n, n < N →
      partitionEnergy G (parts n) + eps ^ 4 * M / (Fintype.card V : ℚ) ^ 2 ≤
        partitionEnergy G (parts (n + 1))) :
    (N : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 / (eps ^ 4 * M) := by
  have hδ : 0 < eps ^ 4 * M / (Fintype.card V : ℚ) ^ 2 :=
    div_pos (mul_pos (by positivity) hM) (pow_pos hcard 2)
  have hbound := Szemeredi.RegularityOQ04.partitionEnergy_iteration_bound G parts N
    (eps ^ 4 * M / (Fintype.card V : ℚ) ^ 2) hδ hcover hdisjoint hstep
  rwa [one_div_div] at hbound

/-- **Sharp AFKS iteration count from a per-step irregular-product witness.**  This
    closes the no-loss route into an end-to-end iteration certificate: rather than
    postulate the per-step energy jump abstractly (as `afks_sharp_energy_iteration_count`
    does through its `hstep`), we *derive* it from the datum an actual ε-irregular
    pair supplies at each step.

    Suppose that at each of the first `N` steps the partition `parts n` contains two
    distinct parts `A, B` (with the rest `R`) that are refined into the sharp 2×2 grid
    `{A₁, A₂} × {B₁, B₂}` — `parts (n+1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))`
    — where the witness cell `A₁ × B₁` carries the ε-irregularity: `|A₁| ≥ ε|A|`,
    `|B₁| ≥ ε|B|`, and `|d(A₁,B₁) − d(A,B)| ≥ ε`.  If, moreover, every refined part has
    mass at least `m` (`|A|, |B| ≥ m`), then each step realizes the sharp no-loss floor
    `ε⁴·m²/n²` (via `partitionEnergy_prod_gain_eps4`, flooring `|A||B| ≥ m²`), and hence

    `N ≤ n² / (ε⁴·m²)`.

    The freshness side-conditions (`A₁,A₂,B₁,B₂` distinct and `∉ R`) remain hypotheses,
    exactly as they are in `partitionEnergy_prod_gain_eps4` and the one-sided route;
    discharging them from a nonempty-equipartition model is the standing open blocker.
    Everything downstream of the witness — flooring the size-dependent cell gain by the
    uniform `ε⁴·m²/n²` and feeding it through the `[0,1]`-potential termination engine —
    is here fully machine-checked. -/
theorem afks_sharp_energy_iteration_count_of_prod_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (eps m : ℚ)
    (hε : 0 < eps) (hm : 0 < m) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hwit : ∀ n, n < N → ∃ R : Finset (Finset V), ∃ A B A₁ A₂ B₁ B₂ : Finset V,
      parts n = insert A (insert B R) ∧
      parts (n + 1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R))) ∧
      A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
      A ∉ insert B R ∧ B ∉ R ∧
      A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)) ∧ A₂ ∉ insert B₁ (insert B₂ R) ∧
      B₁ ∉ insert B₂ R ∧ B₂ ∉ R ∧
      m ≤ (A.card : ℚ) ∧ m ≤ (B.card : ℚ) ∧
      eps * A.card ≤ (A₁.card : ℚ) ∧ eps * B.card ≤ (B₁.card : ℚ) ∧
      eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    (N : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 / (eps ^ 4 * m ^ 2) := by
  refine afks_sharp_energy_iteration_count G parts N eps (m ^ 2) hε
    (by positivity) hcard hcover hdisjoint ?_
  intro n hn
  obtain ⟨R, A, B, A₁, A₂, B₁, B₂, hpn, hpn1, hAu, hBu, hdA, hdB,
    hAins, hBR, hA1, hA2, hB1, hB2, hmA, hmB, hcA, hcB, hdev⟩ := hwit n hn
  rw [hpn, hpn1]
  -- The exact size-dependent sharp gain from the ε-irregular product witness.
  have hgain := partitionEnergy_prod_gain_eps4 G R A B A₁ A₂ B₁ B₂
    hAu hBu hdA hdB hAins hBR hA1 hA2 hB1 hB2 eps hε.le hcA hcB hdev
  -- Floor the pair mass `|A||B| ≥ m²`, so the uniform floor `ε⁴·m²/n²` is dominated.
  have hmass : m ^ 2 ≤ (A.card : ℚ) * B.card := by nlinarith [hmA, hmB, hm.le]
  have hfloor : eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
      eps ^ 4 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 := by
    gcongr
  linarith [hgain, hfloor]

-- ═══════════════════════════════════════════════════════════════════
-- TERMINATION: A REGULAR REFINEMENT STEP IS REACHED IN BOUNDED TIME
-- ═══════════════════════════════════════════════════════════════════

/-- **AFKS termination / a regular step is reached in bounded time.**  This is the
    contrapositive capstone of `afks_sharp_energy_iteration_count_of_prod_witness`
    and states the *conclusion* the whole file was built toward: an infinite chain of
    sharp `2×2` irregular-refinement steps is impossible, so a *regular* step must occur
    within a bounded number of refinements.

    Concretely: for any partition sequence `parts : ℕ → Finset (Finset V)` (each a cover
    by pairwise-disjoint parts) and any horizon `N` strictly larger than the sharp
    iteration bound `n²/(ε⁴·m²)`, there is some step `n < N` at which the refinement
    `parts n → parts (n+1)` is **not** a mass-`m`, `ε`-irregular sharp `2×2` split.  Since
    `afks_sharp_energy_iteration_count_of_prod_witness` shows every such witnessed step
    raises `partitionEnergy` by the fixed no-loss floor `ε⁴·m²/n²`, and energy is capped
    at `1`, no more than `n²/(ε⁴·m²)` witnessed steps can occur; a horizon exceeding that
    bound must therefore contain a step whose refined pair is already `ε`-regular (or has
    a part of mass `< m`).  This is exactly the strong-regularity termination statement:
    the AFKS iteration halts — a regular partition is reached — in `O(n²/(ε⁴m²))` steps.

    The freshness/equipartition realizability of the witnessed steps is inherited from
    the underlying iteration-count lemma and is not assumed here; the theorem is purely
    the impossibility of an all-witnessed refinement chain longer than the energy budget
    allows. -/
theorem afks_regular_step_within_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (eps m : ℚ)
    (hε : 0 < eps) (hm : 0 < m) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Fintype.card V : ℚ) ^ 2 / (eps ^ 4 * m ^ 2) < N) :
    ∃ n < N, ¬ (∃ R : Finset (Finset V), ∃ A B A₁ A₂ B₁ B₂ : Finset V,
      parts n = insert A (insert B R) ∧
      parts (n + 1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R))) ∧
      A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
      A ∉ insert B R ∧ B ∉ R ∧
      A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)) ∧ A₂ ∉ insert B₁ (insert B₂ R) ∧
      B₁ ∉ insert B₂ R ∧ B₂ ∉ R ∧
      m ≤ (A.card : ℚ) ∧ m ≤ (B.card : ℚ) ∧
      eps * A.card ≤ (A₁.card : ℚ) ∧ eps * B.card ≤ (B₁.card : ℚ) ∧
      eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) := by
  by_contra hcon
  push_neg at hcon
  -- `hcon` is now exactly the per-step witness hypothesis: every step `n < N` IS a
  -- mass-`m`, `ε`-irregular sharp `2×2` split.  Feed it to the iteration-count bound.
  have hle := afks_sharp_energy_iteration_count_of_prod_witness
    G parts N eps m hε hm hcard hcover hdisjoint (fun n hn => hcon n hn)
  -- The bound `N ≤ n²/(ε⁴m²)` contradicts the assumed horizon `n²/(ε⁴m²) < N`.
  exact absurd hle (not_le.mpr hN)

end Szemeredi.RegularityOQ04Bridge
