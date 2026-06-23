/-
  Aristotle targets for BallotProblemOQ01OQ02OQ01 (Uniform Fiber Transfer)
  Routine lemmas for automated proof search.
  See BallotProblemOQ01OQ02OQ01.lean for the main formalization.

  The 3 sorries in the main file are Mathlib API navigation (0 axioms):
  1. `ncard_biUnion_eq_of_uniform` (2 sub-sorries): rewrite each ncard to k,
     then sum k over I.toFinset = k * I.ncard
  2. `uniformOn_fiber_transfer'` (1 sorry): assemble ENNReal ratio from the
     ncard counts using condCount definition of uniformOn

  ## Proof Strategies

  TARGET 1 (`ncard_sum_eq`):
    Goal: ∑ i ∈ hI.toFinset, (S i).ncard = k * I.ncard
    Strategy:
      have hmem : ∀ i ∈ hI.toFinset, (S i).ncard = k :=
        fun i hi => hk i (hI.mem_toFinset.mp hi)
      rw [Finset.sum_congr rfl hmem, Finset.sum_const, Set.ncard_eq_toFinset_card']
      simp [smul_eq_mul, Finset.card_eq_of_equiv]

  TARGET 2 (`ncard_biUnion_eq_of_uniform`):
    Strategy:
      rw [Set.ncard_biUnion hI hdisj (fun i hi => hfin i hi)]
      exact ncard_sum_eq S I hI k hk

  TARGET 3 (`uniformOn_fiber_transfer'`):
    Unfold uniformOn to condCount (ratio of ncard values in ENNReal).
    Apply ncard_biUnion_eq_of_uniform to get:
      ncard(multiCountedSequence) = k * ncard(countedSequence a b)
      ncard(multiCountedSequence ∩ multiStaysPositive) = k * ncard(C ∩ staysPositive)
    where k = ncard(fiber(any target)) from fiber_card_uniform.
    Then the ENNReal.div_eq_div_of_mul_eq from the main file cancels the k.
-/
import Mathlib
import Proofs.BallotProblemOQ01OQ02OQ01

open Ballot ProbabilityTheory Set MultiBallot BallotFiberTransfer

namespace BallotProblemOQ01OQ02OQ01Aristotle

/-
TARGET 1 (pure Finset API: sum of a constant over a finite index set)

After `Set.ncard_biUnion` reduces the goal to a sum, this lemma handles
the key step: ∑ i ∈ hI.toFinset, (S i).ncard = k * I.ncard.

Strategy:
  have hmem : ∀ i ∈ hI.toFinset, (S i).ncard = k :=
    fun i hi => hk i (hI.mem_toFinset.mp hi)
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, Set.ncard_eq_toFinset_card']
  simp [smul_eq_mul]
-/
theorem ncard_sum_eq {α ι : Type*}
    (S : ι → Set α)
    (I : Set ι) (hI : I.Finite)
    (k : ℕ) (hk : ∀ i ∈ I, (S i).ncard = k) :
    ∑ i ∈ hI.toFinset, (S i).ncard = k * I.ncard := by
  have hmem : ∀ i ∈ hI.toFinset, (S i).ncard = k :=
    fun i hi => hk i (hI.mem_toFinset.mp hi)
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, smul_eq_mul,
      mul_comm, hI.toFinset_card]

/-
TARGET 2 (Mathlib API: Set.ncard_biUnion + uniform sum)

General lemma: pairwise-disjoint finite sets with uniform ncard k have
total ncard equal to k × number of sets.

Strategy:
  rw [Set.ncard_biUnion hI hdisj (fun i hi => hfin i hi)]
  exact ncard_sum_eq S I hI k hk
-/
theorem ncard_biUnion_eq_of_uniform {α ι : Type*}
    (S : ι → Set α)
    (I : Set ι) (hI : I.Finite)
    (hfin : ∀ i ∈ I, (S i).Finite)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (k : ℕ) (hk : ∀ i ∈ I, (S i).ncard = k) :
    (⋃ i ∈ I, S i).ncard = k * I.ncard := by
  rw [Set.ncard_biUnion hI hdisj (fun i hi => hfin i hi)]
  exact ncard_sum_eq S I hI k hk

/-
TARGET 3 (ENNReal assembly: uniformOn = condCount = ncard ratio)

Uniform fibers preserve the uniformOn probability.

Key intermediate facts (all proved in the main file):
  - multiCountedSequence_eq_biUnion: multiCountedSequence = ⋃ t ∈ countedSequence, fiber(t)
  - multiProjectionFiber_pairwise_disjoint: fibers over distinct targets are disjoint
  - multiStaysPositive_eq_biUnion: the "stays positive" decomposition
  - fiber_card_uniform (in parent): all fibers have equal ncard (via fiberSwap bijection)
  - ENNReal.div_eq_div_of_mul_eq (in main file): cancels the fiber size k

Strategy:
  simp only [ProbabilityTheory.uniformOn, MeasureTheory.condCount]
  -- condCount S P = (S ∩ P).ncard / S.ncard as ENNReal
  obtain ⟨k, hk_pos, hk⟩ := ... -- fiber_card_uniform gives fiber size k
  rw [multiCountedSequence_eq_biUnion, multiStaysPositive_eq_biUnion]
  rw [ncard_biUnion_eq_of_uniform, ncard_biUnion_eq_of_uniform]
  exact ENNReal.div_eq_div_of_mul_eq hk_pos rfl rfl (...)
-/
theorem uniformOn_fiber_transfer' (m : ℕ) (hm : 2 ≤ m) (a b : ℕ)
    (hab : b < a) :
    ProbabilityTheory.uniformOn (multiCountedSequence m (by omega) a b)
      (multiStaysPositive m (by omega)) =
    ProbabilityTheory.uniformOn (Ballot.countedSequence a b)
      Ballot.staysPositive := by
  sorry

end BallotProblemOQ01OQ02OQ01Aristotle
