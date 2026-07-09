/-
  Szemerédi Regularity Lemma — OQ-04: connecting the `pairEnergy` refinement
  machinery to the gallery's `partitionEnergy`.

  The companion file `SzemerediRegularityOQ04Energy` builds a normalized
  per-ordered-pair energy `pairEnergy G A B = (|A||B|/n²)·d(A,B)²` and proves its
  refinement behaviour (`pairEnergy_split_mono`, `pairEnergy_split_gain`,
  `pairEnergy_row_split_mono`).  Its docstring asserts — but never proves — that
  *summing* `pairEnergy` over all ordered pairs of parts reproduces
  `partitionEnergy`.  Without that bridge the whole `pairEnergy` layer is
  disconnected from the actual gallery energy, so none of its monotonicity
  content transfers.

  This file supplies the missing bridge and cashes it out, fully machine-checked:

  * `partitionEnergy_eq_sum_pairEnergy` — the bridge: `partitionEnergy G parts`
    is exactly `Σ_{(P,Q) ∈ parts ×ˢ parts} pairEnergy G P Q`, unconditionally
    (the `n = 0` degenerate case is handled because every `pairEnergy` term
    carries the same vanishing `1/n²` weight).
  * `pairEnergy_comm` — symmetry `pairEnergy G A B = pairEnergy G B A`, via the
    gallery's `edgeDensity_symm`.
  * `pairEnergy_split_mono_right` — the second-argument (B-side) form of
    `pairEnergy_split_mono`.
  * `partitionEnergy_single_split_mono` — **genuine refinement monotonicity of
    the gallery energy**: replacing a part `A₁ ∪ A₂` by its two disjoint pieces
    never decreases `partitionEnergy`.  This is the "splitting a part never
    decreases energy" fact stated in the `partitionEnergy` docstring but not
    previously proved for the actual refinement operation (the existing
    `partitionEnergy_mono` is only monotone under *set inclusion* of the family,
    which does not model a refinement — a refinement removes `A₁ ∪ A₂` and adds
    `A₁, A₂`).  The proof decomposes the ordered-pair sum into the diagonal, row,
    and column blocks and applies the `pairEnergy` split lemmas to each.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Energy
import Proofs.SzemerediRegularityOQ01

namespace Szemeredi.RegularityOQ04Bridge

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE BRIDGE — partitionEnergy IS THE SUM OF pairEnergy
-- ═══════════════════════════════════════════════════════════════════

/-- **Bridge lemma.**  The gallery's `partitionEnergy G parts` is exactly the sum
    of the normalized `pairEnergy` contributions over all ordered pairs of parts.
    This holds unconditionally: in the degenerate `n = |V| = 0` case both sides
    vanish, since every `pairEnergy` term carries the common `1/n²` factor. -/
theorem partitionEnergy_eq_sum_pairEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      (parts.product parts).sum (fun pq => pairEnergy G pq.1 pq.2) := by
  unfold partitionEnergy pairEnergy
  by_cases hn : (Fintype.card V : ℚ) = 0
  · simp only [if_pos hn]
    symm
    apply Finset.sum_eq_zero
    intro pq _
    simp [hn]
  · simp only [if_neg hn]

/-- The bridge in nested-double-sum form, convenient for block decompositions. -/
private theorem partitionEnergy_eq_double_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      parts.sum (fun P => parts.sum (fun Q => pairEnergy G P Q)) := by
  rw [partitionEnergy_eq_sum_pairEnergy,
    show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: SYMMETRY AND THE SECOND-ARGUMENT SPLIT
-- ═══════════════════════════════════════════════════════════════════

/-- **Symmetry of pair energy.**  `pairEnergy G A B = pairEnergy G B A`, an
    immediate consequence of `edgeDensity_comm` and `|A||B| = |B||A|`. -/
theorem pairEnergy_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    pairEnergy G A B = pairEnergy G B A := by
  unfold pairEnergy
  rw [Szemeredi.Regularity.OQ01.edgeDensity_comm G A B]
  ring

/-- **Second-argument refinement monotonicity.**  Splitting the `B`-side of a pair
    into disjoint `B₁, B₂` never decreases its normalized energy contribution.
    This is `pairEnergy_split_mono` transported through `pairEnergy_comm`. -/
theorem pairEnergy_split_mono_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hB : Disjoint B₁ B₂) :
    pairEnergy G A (B₁ ∪ B₂) ≤ pairEnergy G A B₁ + pairEnergy G A B₂ := by
  rw [pairEnergy_comm G A (B₁ ∪ B₂), pairEnergy_comm G A B₁, pairEnergy_comm G A B₂]
  exact pairEnergy_split_mono G B₁ B₂ A hB

-- ═══════════════════════════════════════════════════════════════════
-- PART III: REFINEMENT MONOTONICITY OF partitionEnergy
-- ═══════════════════════════════════════════════════════════════════

/-- **Refinement monotonicity of the gallery energy.**  Let `R` be a family of
    parts and let `A₁, A₂` be two disjoint sets, neither in `R`, whose union is
    also not in `R`.  Then refining the partition by replacing the single part
    `A₁ ∪ A₂` with its two pieces `A₁, A₂` never decreases `partitionEnergy`:

    `partitionEnergy G (insert (A₁ ∪ A₂) R) ≤ partitionEnergy G (insert A₁ (insert A₂ R))`.

    This is the exact "splitting a part never decreases energy" statement from the
    `partitionEnergy` docstring, realized for the genuine refinement operation.
    The ordered-pair sum splits into a diagonal block `(A,A)`, a row block
    `(A, R)`, a column block `(R, A)`, and the untouched `R × R` block; the three
    affected blocks are each controlled by the `pairEnergy` split lemmas. -/
theorem partitionEnergy_single_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A₁ A₂ : Finset V) (hdisj : Disjoint A₁ A₂)
    (hA₁R : A₁ ∉ R) (hA₂R : A₂ ∉ R) (hne : A₁ ≠ A₂) (hAR : A₁ ∪ A₂ ∉ R) :
    partitionEnergy G (insert (A₁ ∪ A₂) R) ≤
      partitionEnergy G (insert A₁ (insert A₂ R)) := by
  -- A₁ is not in the smaller inserted family either.
  have hA₁ : A₁ ∉ insert A₂ R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hA₁R⟩
  -- Diagonal block: (A₁∪A₂,A₁∪A₂) ≤ the four sub-pairs.
  have h1 : pairEnergy G (A₁ ∪ A₂) (A₁ ∪ A₂) ≤
      pairEnergy G A₁ A₁ + pairEnergy G A₁ A₂ +
        pairEnergy G A₂ A₁ + pairEnergy G A₂ A₂ := by
    have a := pairEnergy_split_mono G A₁ A₂ (A₁ ∪ A₂) hdisj
    have b := pairEnergy_split_mono_right G A₁ A₁ A₂ hdisj
    have c := pairEnergy_split_mono_right G A₂ A₁ A₂ hdisj
    linarith
  -- Row block: Σ_{Q∈R} pairEnergy (A₁∪A₂) Q ≤ Σ pairEnergy A₁ Q + Σ pairEnergy A₂ Q.
  have h2 := pairEnergy_row_split_mono G A₁ A₂ hdisj R
  rw [Finset.sum_add_distrib] at h2
  -- Column block: Σ_{P∈R} pairEnergy P (A₁∪A₂) ≤ Σ pairEnergy P A₁ + Σ pairEnergy P A₂.
  have h3 : R.sum (fun P => pairEnergy G P (A₁ ∪ A₂)) ≤
      R.sum (fun P => pairEnergy G P A₁) + R.sum (fun P => pairEnergy G P A₂) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro P _
    exact pairEnergy_split_mono_right G P A₁ A₂ hdisj
  -- Expand both energies to their block decompositions and combine.
  rw [partitionEnergy_eq_double_sum, partitionEnergy_eq_double_sum]
  simp only [Finset.sum_insert hAR, Finset.sum_insert hA₁, Finset.sum_insert hA₂R,
    Finset.sum_add_distrib]
  linarith [h1, h2, h3]

end Szemeredi.RegularityOQ04Bridge
