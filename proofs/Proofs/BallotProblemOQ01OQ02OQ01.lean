/-
  Ballot Problem OQ-01-OQ-02-OQ-01: Uniform Fiber Transfer

  Proves `uniformOn_fiber_transfer`: when a surjection has uniform fiber sizes,
  it preserves the `uniformOn` probability. This eliminates the axiom in
  BallotProblemOQ01OQ02.lean, completing the multi-candidate ballot theorem.

  ## The Key Idea

  The projection `project leader` maps multi-candidate sequences to ±1 sequences.
  Every ±1 target in `countedSequence a b` has the same number of multi-candidate
  preimages in `multiCountedSequence m a b` (proved by `fiber_card_uniform`
  via the fiberSwap bijection).

  For `uniformOn S P = ncard(S ∩ P) / ncard(S)` (in ENNReal):
  - S = multiCountedSequence is the disjoint union of fibers over countedSequence
  - P = multiStaysPositive = project⁻¹(staysPositive)
  - Since all fibers have equal ncard k:
    ncard(S ∩ P) = k · ncard(countedSequence ∩ staysPositive)
    ncard(S) = k · ncard(countedSequence)
  - The ratio simplifies to ncard(C ∩ staysPositive) / ncard(C)

  References:
  - Parent: Proofs.BallotProblemOQ01OQ02 (multiCountedSequence, fiber_card_uniform)
  - Mathlib: Archive.Wiedijk100Theorems.BallotProblem (countedSequence, staysPositive)
-/

import Proofs.BallotProblemOQ01OQ02

open Ballot ProbabilityTheory Set

namespace BallotFiberTransfer

-- Re-export key definitions and theorems from the parent
-- (All imported via Proofs.BallotProblemOQ01OQ02)

-- ═══════════════════════════════════════════════════════════════
-- PART I: ABSTRACT UNIFORM FIBER COUNTING LEMMA
-- ═══════════════════════════════════════════════════════════════

/-- General lemma: if a collection of pairwise disjoint finite sets all have
    the same ncard k, then the ncard of their union equals k times the
    number of sets.

    This is the abstract version of the fiber-counting argument. -/
theorem ncard_biUnion_eq_of_uniform {α ι : Type*}
    (S : ι → Set α)
    (I : Set ι) (hI : I.Finite)
    (hfin : ∀ i ∈ I, (S i).Finite)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (k : ℕ) (hk : ∀ i ∈ I, (S i).ncard = k) :
    (⋃ i ∈ I, S i).ncard = k * I.ncard := by
  rw [Set.ncard_biUnion hI hdisj (fun i hi => hfin i hi)]
  -- Goal: ∑ i ∈ hI.toFinset, (S i).ncard = k * I.ncard
  have hmem : ∀ i ∈ hI.toFinset, (S i).ncard = k :=
    fun i hi => hk i (hI.mem_toFinset.mp hi)
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, smul_eq_mul,
      mul_comm, hI.toFinset_card]

-- ═══════════════════════════════════════════════════════════════
-- PART II: FIBER PARTITION PROPERTIES
-- ═══════════════════════════════════════════════════════════════

-- These establish that multiCountedSequence decomposes into fibers

section FiberPartition

variable {m : ℕ} (hm1 : m ≥ 1) (hm : 2 ≤ m) (a b : ℕ) (hab : b < a)

/-- The multiCountedSequence is the union of fibers over countedSequence targets. -/
theorem multiCountedSequence_eq_biUnion :
    multiCountedSequence m hm1 a b =
    ⋃ t ∈ Ballot.countedSequence a b, multiProjectionFiber m hm1 a b t := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_sep_iff, multiProjectionFiber, Set.mem_inter_iff,
             projectionFiber, Set.mem_setOf_eq]
  constructor
  · intro hs
    exact ⟨project (leader m hm1) s, project_multi_to_counted hm1 hs, hs, rfl⟩
  · rintro ⟨t, _, hs, _⟩
    exact hs

/-- Fibers over different targets are disjoint. -/
theorem multiProjectionFiber_pairwise_disjoint :
    ∀ t1 ∈ Ballot.countedSequence a b,
    ∀ t2 ∈ Ballot.countedSequence a b,
    t1 ≠ t2 → Disjoint (multiProjectionFiber m hm1 a b t1)
                        (multiProjectionFiber m hm1 a b t2) := by
  intro t1 _ t2 _ hne
  rw [Set.disjoint_iff]
  intro s ⟨⟨_, hs1⟩, ⟨_, hs2⟩⟩
  exact hne (hs1.symm.trans hs2)

/-- The "stays positive" intersection with multiCountedSequence is the union
    of fibers over targets in countedSequence ∩ staysPositive. -/
theorem multiStaysPositive_eq_biUnion :
    multiCountedSequence m hm1 a b ∩ multiStaysPositive m hm1 =
    ⋃ t ∈ (Ballot.countedSequence a b ∩ Ballot.staysPositive),
      multiProjectionFiber m hm1 a b t := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_iUnion, multiStaysPositive, Set.mem_setOf_eq,
             multiProjectionFiber, projectionFiber]
  constructor
  · rintro ⟨hs, hsp⟩
    exact ⟨project (leader m hm1) s,
           ⟨project_multi_to_counted hm1 hs, hsp⟩,
           hs, rfl⟩
  · rintro ⟨t, ⟨ht, htp⟩, hs, heq⟩
    exact ⟨hs, heq ▸ htp⟩

end FiberPartition

-- ═══════════════════════════════════════════════════════════════
-- PART III: THE ENNReal RATIO CANCELLATION
-- ═══════════════════════════════════════════════════════════════

/-- If both numerator and denominator are k times the respective values,
    the ratio is the same (for k > 0 and finite values). -/
theorem ENNReal.div_eq_div_of_mul_eq {a b c d : ℕ} {k : ℕ} (hk : 0 < k)
    (ha : a = k * c) (hb : b = k * d) (hd : 0 < d) :
    (a : ENNReal) / b = (c : ENNReal) / d := by
  rw [ha, hb]
  simp only [Nat.cast_mul]
  rw [ENNReal.mul_div_mul_left]
  · exact ENNReal.natCast_ne_top
  · exact Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (by omega))

-- ═══════════════════════════════════════════════════════════════
-- PART IV: MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════

/-- **Uniform Fiber Transfer Theorem**.

    When a surjection has uniform fiber sizes, the `uniformOn` probability
    of a pullback event equals the `uniformOn` probability of the event itself.

    This is the missing step that completes the Multi-Candidate Ballot Theorem
    (replacing the axiom `uniformOn_fiber_transfer` in BallotProblemOQ01OQ02.lean).

    **Strategy**: Proven via fiber-counting assembly. All fibers over CS
    have equal ncard k (fiber_card_uniform via fiberSwap). The disjoint union
    decompositions give ncard(MCS) = k·ncard(CS) and ncard(MCS∩MSP) = k·ncard(CS∩SP),
    so the ratio k cancels.

    `ProbabilityTheory.uniformOn` unfolds (via `simp only [ProbabilityTheory.uniformOn]`)
    to `↑(S ∩ P).ncard / ↑S.ncard` in ENNReal, consistent with condCount.
    ENNReal.div_eq_div_iff reduces the equality to cross-multiplication in ℕ. -/
theorem uniformOn_fiber_transfer' (m : ℕ) (hm : 2 ≤ m) (a b : ℕ)
    (hab : b < a) :
    ProbabilityTheory.uniformOn (multiCountedSequence m (by omega) a b)
      (multiStaysPositive m (by omega)) =
    ProbabilityTheory.uniformOn (Ballot.countedSequence a b)
      Ballot.staysPositive := by
  set hm1 : m ≥ 1 := by omega
  -- Finiteness (inline the private proofs from parent)
  have hMCS_fin : (multiCountedSequence m hm1 a b).Finite :=
    Set.Finite.subset (Set.finite_range (List.ofFn : (Fin (a + b) → Fin m) → _))
      fun s ⟨_, hlen⟩ => ⟨fun i => s.get ⟨i.val, by omega⟩,
        List.ext_get (by simp [hlen]) (fun i _ _ => by simp)⟩
  have hCS_fin := Ballot.countedSequence_finite a b
  -- Nonemptiness
  have hCS_ne := Ballot.countedSequence_nonempty a b
  have hMCS_ne : (multiCountedSequence m hm1 a b).Nonempty := by
    refine ⟨List.replicate a (leader m hm1) ++ List.replicate b ⟨1, by omega⟩, ?_, ?_⟩
    · simp only [List.count_append, List.count_replicate, leader]
      have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
        intro h; exact absurd (Fin.val_eq_of_eq h) (by omega)
      simp [hne]
    · simp
  -- Positive ncard
  have hMCS_pos : 0 < (multiCountedSequence m hm1 a b).ncard :=
    Set.ncard_pos hMCS_fin ⟨_, hMCS_ne.choose_spec⟩
  have hCS_pos : 0 < (Ballot.countedSequence a b).ncard :=
    Set.ncard_pos hCS_fin ⟨_, hCS_ne.choose_spec⟩
  -- Reference target and fiber witness
  obtain ⟨t0, ht0⟩ := hCS_ne
  obtain ⟨s0, hs0⟩ := hMCS_ne
  have ht1 : project (leader m hm1) s0 ∈ Ballot.countedSequence a b :=
    project_multi_to_counted hm1 hs0
  -- All fibers have equal ncard (fiber_card_uniform)
  have hk_uniform : ∀ t ∈ Ballot.countedSequence a b,
      (multiProjectionFiber m hm1 a b t).ncard =
      (multiProjectionFiber m hm1 a b t0).ncard := fun t ht =>
    fiber_card_uniform m hm a b t t0 ht ht0
  -- Fiber over t0 is nonempty (since fiber over project(s0) is nonempty)
  set k := (multiProjectionFiber m hm1 a b t0).ncard with hk_def
  have hk_pos : 0 < k := by
    rw [hk_def, ← fiber_card_uniform m hm a b t0 (project (leader m hm1) s0) ht0 ht1]
    exact Set.ncard_pos (multiProjectionFiber_finite m hm1 a b _)
      ⟨s0, hs0, rfl⟩
  -- ncard(MCS) = k * ncard(CS)
  have hMCS_ncard : (multiCountedSequence m hm1 a b).ncard =
      k * (Ballot.countedSequence a b).ncard := by
    rw [multiCountedSequence_eq_biUnion hm1 a b]
    exact ncard_biUnion_eq_of_uniform
      (multiProjectionFiber m hm1 a b) (Ballot.countedSequence a b) hCS_fin
      (fun t _ => multiProjectionFiber_finite m hm1 a b t)
      (multiProjectionFiber_pairwise_disjoint hm1 a b)
      k hk_uniform
  -- ncard(MCS ∩ MSP) = k * ncard(CS ∩ SP)
  have hMCS_pos_ncard :
      (multiCountedSequence m hm1 a b ∩ multiStaysPositive m hm1).ncard =
      k * (Ballot.countedSequence a b ∩ Ballot.staysPositive).ncard := by
    rw [multiStaysPositive_eq_biUnion hm1 a b]
    exact ncard_biUnion_eq_of_uniform
      (multiProjectionFiber m hm1 a b)
      (Ballot.countedSequence a b ∩ Ballot.staysPositive)
      (hCS_fin.subset Set.inter_subset_left)
      (fun t _ => multiProjectionFiber_finite m hm1 a b t)
      (fun t1 ht1 t2 ht2 hne =>
        multiProjectionFiber_pairwise_disjoint hm1 a b t1 ht1.1 t2 ht2.1 hne)
      k (fun t ht => hk_uniform t ht.1)
  -- Assemble via ENNReal ratio: simp [uniformOn] gives ncard ratio,
  -- div_eq_div_iff reduces to cross-multiplication, fiber counting closes it.
  simp only [ProbabilityTheory.uniformOn]
  rw [ENNReal.div_eq_div_iff
    (by exact_mod_cast hMCS_pos.ne' :
      (↑(multiCountedSequence m hm1 a b).ncard : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top _)
    (by exact_mod_cast hCS_pos.ne' :
      (↑(Ballot.countedSequence a b).ncard : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top _)]
  exact_mod_cast (show
      (multiCountedSequence m hm1 a b ∩ multiStaysPositive m hm1).ncard *
        (Ballot.countedSequence a b).ncard =
      (Ballot.countedSequence a b ∩ Ballot.staysPositive).ncard *
        (multiCountedSequence m hm1 a b).ncard by
    rw [hMCS_pos_ncard, hMCS_ncard]; ring)

/-! ## Summary

**Proved (0 axioms, 0 sorries):**
1. `multiCountedSequence_eq_biUnion`: MCS decomposes as disjoint union of fibers over CS.
2. `multiProjectionFiber_pairwise_disjoint`: Fibers over distinct targets are disjoint.
3. `multiStaysPositive_eq_biUnion`: (MCS ∩ MSP) decomposes as union of fibers over (CS ∩ SP).
4. `ENNReal.div_eq_div_of_mul_eq`: Ratio preserved under uniform k-scaling.
5. `ncard_biUnion_eq_of_uniform`: ncard of uniform-fiber disjoint union = k × count.
6. `uniformOn_fiber_transfer'`: Uniform fibers preserve uniformOn probability.

**Key insight for OQ-02**: `ProbabilityTheory.uniformOn S P` unfolds via
`simp only [ProbabilityTheory.uniformOn]` to `↑(S ∩ P).ncard / ↑S.ncard` in ENNReal,
consistent with its `condCount`-based definition. This enables direct ncard-based
reasoning about conditional probabilities on finite uniform distributions.

**Proof strategy**: Fiber counting (ncard biUnion decomposition + ENNReal cross-mult)
provides a modular alternative to the bijection-based proof in the parent file.
Both proofs give 0 axioms. -/

end BallotFiberTransfer
