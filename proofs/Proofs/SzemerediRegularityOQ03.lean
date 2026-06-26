/-
# Szemerédi Regularity OQ-03: Algorithmic Regularity & Polynomial-Time Backbone

OQ-03 follow-up to `szemeredi-regularity`. Addresses the open question:

  "Can the partition refinement be made algorithmic with polynomial-time
   guarantees (Alon–Duke–Lefmann–Rödl–Yuster)?"

## Background

Szemerédi's original proof is *effective* but its naive reading is not
polynomial: the energy-increment step asks, for each irregular pair (Pᵢ,Pⱼ),
for witness subsets demonstrating irregularity, and finding the *maximal*
such witnesses is co-NP-hard. Alon–Duke–Lefmann–Rödl–Yuster (1994) made the
lemma algorithmic by replacing exact regularity testing with a polynomial-time
**"regular-or-witness"** subroutine: for a parameter ε and a slightly weaker
ε', in time poly(n) it either certifies a pair is ε-regular or produces an
explicit witness proving it is not ε'-regular (via a Cauchy–Schwarz / singular
value analysis of the bipartite adjacency matrix).

The reason the overall algorithm is polynomial — and the part that is purely
combinatorial, hence formalizable here — is the **iteration bound**:

  * each refinement round increases the partition energy `q ∈ [0,1]` by a fixed
    amount `δ = δ(ε) > 0` (the Komlós–Simonovits energy increment, `δ ≍ ε⁵`), and
  * energy never exceeds `1`,

so the number of rounds is at most `1/δ`, a *constant independent of n*. Each
round does poly(n) work, so the total running time is poly(n).

## What this file proves

1. `energy_telescope` — a per-step energy increment telescopes:
   `q m ≥ q 0 + m·δ`.
2. `energy_increment_iteration_bound` / `roundCount_le` — a refinement sequence
   whose energy starts ≥ 0, stays ≤ 1, and increases by ≥ δ each round has at
   most `1/δ` rounds. This is the finiteness/complexity heart of ADLRY, and is
   *sharper* than the parent's `max_iterations` (an existential `∃ N`): it bounds
   the round count of an actual energy sequence by the explicit constant `1/δ`.
3. `partition_refinement_rounds_bounded` — the same bound stated directly on the
   real `partitionEnergy` of a sequence of genuine partitions, using
   `partitionEnergy_nonneg` and `partitionEnergy_le_one`.
4. `IrregularityWitness` / `RegularOrWitness` / `regular_no_witness` — the
   algorithmic dichotomy the ADLRY subroutine realises, packaged as a structure,
   with soundness of the witness branch.
5. `polytime_total_cost` — the cost-accounting skeleton: constant rounds × poly
   per-round work = poly(n).

## What this file does NOT prove (genuinely open / hard)

The verified poly-time *implementation* of the regular-or-witness subroutine
(its SVD / Cauchy–Schwarz analysis and the concrete cost model) is not
formalized. This file isolates the combinatorial backbone explaining *why* the
algorithm is polynomial, not a machine-checked algorithm.

## Tags
graph-theory, combinatorics, szemeredi, regularity, algorithmic, complexity
-/

import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace SzemerediAlgorithmic

open Szemeredi.Core Szemeredi.Regularity Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: The iteration bound (why ADLRY is polynomial)
-- ═══════════════════════════════════════════════════════════════════

/-- **Telescoping.** If energy increases by at least `δ` each round
    (`q (i+1) ≥ q i + δ`), then after `m` rounds it has grown by at least
    `m·δ`: `q m ≥ q 0 + m·δ`. -/
theorem energy_telescope (q : ℕ → ℚ) (δ : ℚ)
    (hstep : ∀ i, q i + δ ≤ q (i + 1)) :
    ∀ m, q 0 + m * δ ≤ q m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      have hk := hstep k
      have hcast : q 0 + (↑(k + 1) : ℚ) * δ = (q 0 + (k : ℚ) * δ) + δ := by
        push_cast; ring
      rw [hcast]
      linarith [ih, hk]

/-- **Iteration bound.** A refinement sequence whose energy starts ≥ 0, stays
    ≤ 1, and increases by at least `δ` each round satisfies `m·δ ≤ 1` for every
    round count `m`. With `δ ≍ ε⁵` this is the `O(ε⁻⁵)` round bound that makes
    the Alon–Duke–Lefmann–Rödl–Yuster algorithm run in poly(n). -/
theorem energy_increment_iteration_bound (q : ℕ → ℚ) (δ : ℚ)
    (hstart : 0 ≤ q 0) (hbound : ∀ i, q i ≤ 1)
    (hstep : ∀ i, q i + δ ≤ q (i + 1)) (m : ℕ) :
    (m : ℚ) * δ ≤ 1 := by
  have h1 : q 0 + (m : ℚ) * δ ≤ q m := energy_telescope q δ hstep m
  have h2 : q m ≤ 1 := hbound m
  linarith

/-- Explicit constant round bound: `m ≤ 1/δ`, a constant independent of the
    number of vertices `n`. (The number of refinement rounds is bounded purely
    by the regularity parameter, not the input size — the crux of ADLRY.) -/
theorem roundCount_le (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hstart : 0 ≤ q 0) (hbound : ∀ i, q i ≤ 1)
    (hstep : ∀ i, q i + δ ≤ q (i + 1)) (m : ℕ) :
    (m : ℚ) ≤ 1 / δ := by
  rw [le_div_iff₀ hδ]
  exact energy_increment_iteration_bound q δ hstart hbound hstep m

/-- **Round bound for genuine partition refinement.** Specialising the abstract
    iteration bound to the real `partitionEnergy`: given a sequence of valid
    partitions `P : ℕ → ...` (each covering `V` with pairwise-disjoint parts)
    whose energy increases by at least `δ > 0` per round, the number of rounds
    is at most `1/δ` — independent of `|V|`. -/
theorem partition_refinement_rounds_bounded
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : ℕ → Finset (Finset V)) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ i, ∀ v : V, ∃ Q ∈ P i, v ∈ Q)
    (hdisj : ∀ i, ∀ Q R : Finset V, Q ∈ P i → R ∈ P i → Q ≠ R → Disjoint Q R)
    (hincr : ∀ i, partitionEnergy G (P i) + δ ≤ partitionEnergy G (P (i + 1)))
    (m : ℕ) :
    (m : ℚ) ≤ 1 / δ := by
  refine roundCount_le (fun i => partitionEnergy G (P i)) δ hδ ?_ ?_ hincr m
  · exact partitionEnergy_nonneg G (P 0)
  · exact fun i => partitionEnergy_le_one G (P i) (hcover i) (hdisj i)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: The "regular-or-witness" algorithmic dichotomy
-- ═══════════════════════════════════════════════════════════════════

/-- A **witness of irregularity** at level `ε` for a pair `(A, B)`: subsets
    `A' ⊆ A`, `B' ⊆ B`, each occupying at least an `ε`-fraction, whose edge
    density deviates from `d(A, B)` by more than `ε`. The Alon–Duke–Lefmann–
    Rödl–Yuster subroutine produces such an explicit witness in poly(n) time
    whenever it fails to certify regularity. -/
structure IrregularityWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) where
  A' : Finset V
  B' : Finset V
  hA : A' ⊆ A
  hB : B' ⊆ B
  hA_large : (A'.card : ℚ) ≥ eps * A.card
  hB_large : (B'.card : ℚ) ≥ eps * B.card
  hdev : |edgeDensity G A' B' - edgeDensity G A B| > eps

/-- **Soundness of the witness branch.** If a pair is `ε`-regular then it admits
    no `ε`-irregularity witness. Contrapositive: producing a witness *proves*
    irregularity — exactly the guarantee the ADLRY subroutine relies on so that
    "found a witness" is never a false alarm. -/
theorem regular_no_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (h : IsEpsilonRegular G eps A B) :
    IsEmpty (IrregularityWitness G eps A B) := by
  constructor
  intro w
  have hle := h w.A' w.B' w.hA w.hB w.hA_large w.hB_large
  exact absurd hle (not_le.mpr w.hdev)

/-- An `ε`-regular pair has an empty witness type, so any element of that type is
    impossible. (Convenience eliminator used by the chooser below.) -/
theorem no_witness_of_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (h : IsEpsilonRegular G eps A B)
    (w : IrregularityWitness G eps A B) : False := by
  have hle := h w.A' w.B' w.hA w.hB w.hA_large w.hB_large
  exact absurd hle (not_le.mpr w.hdev)

/-- The algorithmic **dichotomy** the ADLRY subroutine realises: for every pair
    it *either* certifies `ε`-regularity *or* returns an `ε'`-irregularity
    witness. (Stated as a `Prop`; the open content is implementing the chooser
    in poly(n), not the dichotomy itself.) -/
def RegularOrWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps eps' : ℚ) (A B : Finset V) : Prop :=
  IsEpsilonRegular G eps A B ∨ Nonempty (IrregularityWitness G eps' A B)

/-- The dichotomy always holds *classically* with `eps' = eps`: a pair is either
    `ε`-regular, or (`exists_irregular_witness`) carries an `ε`-witness. This
    records that the ADLRY guarantee is *information-theoretically* free — the
    only content is making the choice *constructive and polynomial-time*. -/
theorem regularOrWitness_holds (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    RegularOrWitness G eps eps A B := by
  unfold RegularOrWitness
  by_cases h : IsEpsilonRegular G eps A B
  · exact Or.inl h
  · obtain ⟨A', B', hA, hB, hcA, hcB, hd⟩ := exists_irregular_witness G eps A B h
    exact Or.inr ⟨⟨A', B', hA, hB, hcA, hcB, hd⟩⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Polynomial-time cost accounting
-- ═══════════════════════════════════════════════════════════════════

/-- **Polynomial-time skeleton.** If the number of refinement rounds is at most a
    constant `R` (independent of `n`, by `partition_refinement_rounds_bounded`)
    and each round costs at most `C·nᵏ` steps, then the total running time is at
    most `R·(C·nᵏ)` — still `poly(n)`. This is the cost accounting behind the
    ADLRY polynomial-time guarantee: a *constant* number of *polynomial* rounds. -/
theorem polytime_total_cost
    (rounds R C k n perRound : ℕ)
    (hrounds : rounds ≤ R)
    (hperRound : perRound ≤ C * n ^ k) :
    rounds * perRound ≤ R * (C * n ^ k) :=
  Nat.mul_le_mul hrounds hperRound

/-- The total cost `R·(C·nᵏ)` is itself a polynomial in `n` of degree `k` with
    leading coefficient `R·C`: `R·(C·nᵏ) = (R·C)·nᵏ`. Confirms the bound from
    `polytime_total_cost` has the shape "constant · nᵏ". -/
theorem total_cost_is_poly (R C k n : ℕ) :
    R * (C * n ^ k) = (R * C) * n ^ k := by ring

end SzemerediAlgorithmic
