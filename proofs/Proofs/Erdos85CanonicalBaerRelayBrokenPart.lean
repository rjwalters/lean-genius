import Proofs.Erdos85CanonicalEvenRegularBaerRelayExists
import Proofs.Erdos85ActiveWitnessRelayBoundary
import Proofs.Erdos85TriangleFreeStarPairSeparation

/-!
# The broken part of the canonical completed Baer relay

For a completed neighbor-star mate which is canonical on triangle partners,
the triangle-partner and broken fibers remain invariant.  Consequently the
non-ambient edges of the full Eulerian relay are exactly the all-witness
broken relay edges.  This is the graph-level `00/11` decomposition of the
global paired-star transition graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A completed mate canonical on triangle partners preserves the broken
triangle-free-edge fiber. -/
theorem canonicalBaerMate_broken_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    {p x : V} (hx : (triangleFreeEdgeGraph A).Adj p x) :
    (triangleFreeEdgeGraph A).Adj p (mate p x) := by
  have hpx : A.Adj p x := ((mem_triangleFreeNeighbors A p x).mp hx).1
  have hpM : A.Adj p (mate p x) := hclosed p x hpx
  by_contra hnot
  have heligM : trianglePartnerEligible A p (mate p x) :=
    (trianglePartnerEligible_iff_not_triangleFreeEdge A p (mate p x)).2
      ⟨hpM, hnot⟩
  have heligX : trianglePartnerEligible A p x := by
    have hc := trianglePartner_closed heligM
    rw [← hcanonical p (mate p x) heligM, hinvol p x hpx] at hc
    exact hc
  exact ((trianglePartnerEligible_iff_not_triangleFreeEdge A p x).1
    heligX).2 hx

/-- The all-witness broken part of a canonical completed relay. -/
def canonicalBaerBrokenRelayGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x) : SimpleGraph V :=
  activeBrokenWitnessRelayGraph A (fun _ => True) mate
    (fun _ _ hx => canonicalBaerMate_broken_closed
      A mate hclosed hinvol hcanonical hx)
    (fun p x hx => hinvol p x ((mem_triangleFreeNeighbors A p x).mp hx).1)
    (fun p x hx => hfixed p x ((mem_triangleFreeNeighbors A p x).mp hx).1)

/-- **Global canonical relay `00/11` decomposition.** An endpoint pair is a
non-ambient edge of the full neighbor-star relay exactly when it is an edge
of the all-witness broken relay. -/
theorem canonicalBaerBrokenRelayGraph_adj_iff_fullRelay_and_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    {u v : V} :
    (canonicalBaerBrokenRelayGraph A mate hclosed hinvol hfixed
      hcanonical).Adj u v ↔
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj u v ∧
        ¬ A.Adj u v := by
  let hbclosed := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    canonicalBaerMate_broken_closed A mate hclosed hinvol hcanonical hx
  let hbinvol := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    hinvol p x ((mem_triangleFreeNeighbors A p x).mp hx).1
  let hbfixed := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    hfixed p x ((mem_triangleFreeNeighbors A p x).mp hx).1
  change (activeBrokenWitnessRelayGraph A (fun _ => True) mate
    hbclosed hbinvol hbfixed).Adj u v ↔ _
  constructor
  · intro hR
    change ∃ w, (True ∧ (triangleFreeEdgeGraph A).Adj w u) ∧
      mate w u = v at hR
    obtain ⟨w, ⟨_, hwu⟩, hm⟩ := hR
    constructor
    · change ∃ w, A.Adj w u ∧ mate w u = v
      exact ⟨w, ((mem_triangleFreeNeighbors A w u).mp hwu).1, hm⟩
    · apply triangleFreeStar_endpoints_not_adj A hwu
      rw [← hm]
      apply hbclosed w u hwu
  · rintro ⟨hP, hnotA⟩
    change ∃ w, A.Adj w u ∧ mate w u = v at hP
    obtain ⟨w, hwu, hm⟩ := hP
    have hbroken : (triangleFreeEdgeGraph A).Adj w u := by
      by_contra hnotT
      have helig :=
        (trianglePartnerEligible_iff_not_triangleFreeEdge A w u).2
          ⟨hwu, hnotT⟩
      have hadj : A.Adj u v := by
        rw [← hm, hcanonical w u helig]
        exact trianglePartner_pair_adj helig
      exact hnotA hadj
    change ∃ w, (True ∧ (triangleFreeEdgeGraph A).Adj w u) ∧ mate w u = v
    exact ⟨w, ⟨True.intro, hbroken⟩, hm⟩

end

end Erdos85

#print axioms Erdos85.canonicalBaerMate_broken_closed
#print axioms Erdos85.canonicalBaerBrokenRelayGraph_adj_iff_fullRelay_and_not_adj
