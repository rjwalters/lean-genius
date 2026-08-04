import Proofs.Erdos85Problem

/-!
# The common-neighbour conflict graph

Safe one-vertex extension is naturally an independent-set problem.  The
conflict graph of `G` joins two distinct vertices precisely when they have a
common neighbour in `G`.  Thus its independent sets are exactly the safe
attachment sets from `Erdos85Problem`.

This formulation isolates a concrete sufficient condition for the open
extension problem: it is enough to lower-bound the independence number of the
conflict graph of every extremal witness.
-/

open SimpleGraph Finset Filter

namespace Erdos85

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two vertices conflict when they are distinct and have a common neighbour.
An independent set in this graph is safe as the neighbourhood of one newly
attached vertex. -/
def commonNeighborConflict (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.neighborFinset x ∩ G.neighborFinset y).Nonempty
  symm.symm := by
    rintro x y ⟨hxy, h⟩
    exact ⟨Ne.symm hxy, by simpa [Finset.inter_comm] using h⟩
  loopless.irrefl := by simp

instance commonNeighborConflictDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (commonNeighborConflict G).Adj :=
  fun x y => inferInstanceAs
    (Decidable (x ≠ y ∧ (G.neighborFinset x ∩ G.neighborFinset y).Nonempty))

@[simp] theorem commonNeighborConflict_adj_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    (commonNeighborConflict G).Adj x y ↔
      x ≠ y ∧ (G.neighborFinset x ∩ G.neighborFinset y).Nonempty :=
  Iff.rfl

/-- The graph-theoretic reformulation of safe attachment: safe sets are
exactly independent sets in the common-neighbour conflict graph. -/
theorem commonNeighborIndependent_iff_isIndepSet (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    CommonNeighborIndependent G S ↔ (commonNeighborConflict G).IsIndepSet S := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro hsafe x hx y hy hxy hconf
    have hz := hsafe hx hy hxy
    rw [Finset.card_eq_zero] at hz
    rcases hconf.2 with ⟨z, hmem⟩
    rw [hz] at hmem
    simp at hmem
  · intro hind x hx y hy hxy
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (hind hx hy hxy) ⟨hxy, ⟨z, hz⟩⟩

/-- A maximum independent set of the conflict graph realizes a safe attachment
set of exactly the conflict independence number. -/
theorem exists_commonNeighborIndependent_card_eq_indepNum
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, CommonNeighborIndependent G S ∧
      S.card = (commonNeighborConflict G).indepNum := by
  obtain ⟨S, hS⟩ := (commonNeighborConflict G).exists_isNIndepSet_indepNum
  exact ⟨S, (commonNeighborIndependent_iff_isIndepSet G S).2 hS.1, hS.2⟩

/-- **Conflict-graph extension criterion.**  A `C₄`-free minimum-degree-`d`
witness extends by one vertex whenever its common-neighbour conflict graph has
independence number at least `d`. -/
theorem c4FreeMinDegreeWitness_succ_of_conflict_indepNum {n d : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : d ≤ G.minDegree) (hfree : ¬ containsC4 (Fin n) G)
    (hind : d ≤ (commonNeighborConflict G).indepNum) :
    C4FreeMinDegreeWitness (n + 1) d := by
  obtain ⟨S, hsafe, hcard⟩ :=
    exists_commonNeighborIndependent_card_eq_indepNum G
  exact c4FreeMinDegreeWitness_succ_of_commonNeighborIndependent
    G hdeg hfree S (by simpa [hcard] using hind) hsafe

/-- A checkable sufficient condition for one-step witness extension, stated
uniformly over all witnesses at `(n,d)`. -/
theorem witnessExtension_of_conflict_indepNum {n : ℕ}
    (hsel : ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      d ≤ G.minDegree → ¬ containsC4 (Fin n) G →
      d ≤ (commonNeighborConflict G).indepNum) :
    C4FreeWitnessExtension n := by
  rintro d ⟨G, hdec, hdeg, hfree⟩
  letI := hdec
  exact c4FreeMinDegreeWitness_succ_of_conflict_indepNum G hdeg hfree
    (hsel d G hdec hdeg hfree)

/-- Consequently, an eventual conflict-independence bound would settle
Erdős #85.  This records the precise selection statement that remains. -/
theorem erdos85Question_of_eventually_conflict_indepNum
    (h : ∀ᶠ n in Filter.atTop,
      ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        d ≤ G.minDegree →
        ¬ containsC4 (Fin n) G →
        d ≤ (commonNeighborConflict G).indepNum) :
    Erdos85Question := by
  rw [erdos85Question_iff_eventually_witnessExtension]
  filter_upwards [h, eventually_ge_atTop 4] with n hn hfour
  exact witnessExtension_of_conflict_indepNum hn

end Erdos85
