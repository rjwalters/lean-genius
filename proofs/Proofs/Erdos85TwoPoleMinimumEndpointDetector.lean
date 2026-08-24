import Proofs.Erdos85TwoPoleMinimumDefectSignature

/-!
# Endpoint detector for a minimum two-pole potential

This is the exact consumer form of `(73rnz_br)`.  Once the triangle-free
neighbors of an empty pole are identified with its full leaves, residual
incidence detects whether the pole's unique support point is one of them.
-/

open SimpleGraph

namespace Erdos85

/-- **Minimum two-pole endpoint detector (`73rnz_br`, one pole).** -/
theorem binaryTransportResidual_pole_apply_eq_leafIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (x : V → ZMod 2) (pole other p : V) (leaves : Finset V)
    (hnonadj : ¬ A.Adj pole other)
    (htransport :
      ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x =
        ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec x +
          (A.adjMatrix (ZMod 2)).mulVec
            (Pi.single pole 1 + Pi.single other 1))
    (hXline : f2PotentialSupport x ∩ A.neighborFinset pole = {p})
    (hTline : (triangleFreeEdgeGraph A).neighborFinset pole = leaves)
    (hleaves : leaves ⊆ A.neighborFinset pole) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x pole =
      if p ∈ leaves then 1 else 0 := by
  classical
  let K := binaryTransportResidualGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hline : leaves ∩ f2PotentialSupport x =
      if p ∈ leaves then {p} else ∅ := by
    split_ifs with hp
    · ext w
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro hw
        have hwA : w ∈ A.neighborFinset pole := hleaves hw.1
        have hwp : w = p := by
          have : w ∈ f2PotentialSupport x ∩ A.neighborFinset pole :=
            Finset.mem_inter.mpr ⟨hw.2, hwA⟩
          rw [hXline] at this
          exact Finset.mem_singleton.mp this
        simpa [hwp]
      · intro hw
        have hwp : w = p := hw
        subst w
        have hpX : p ∈ f2PotentialSupport x := by
          have : p ∈ f2PotentialSupport x ∩ A.neighborFinset pole := by
            rw [hXline]
            exact Finset.mem_singleton_self p
          exact (Finset.mem_inter.mp this).1
        exact ⟨hp, hpX⟩
    · ext w
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hwLeaf, hwX⟩
        have hwA : w ∈ A.neighborFinset pole := hleaves hwLeaf
        have hwp : w = p := by
          have : w ∈ f2PotentialSupport x ∩ A.neighborFinset pole :=
            Finset.mem_inter.mpr ⟨hwX, hwA⟩
          rw [hXline] at this
          exact Finset.mem_singleton.mp this
        have : False := hp (hwp ▸ hwLeaf)
        contradiction
      · intro hw
        simp at hw
  have hTapply : (T.adjMatrix (ZMod 2)).mulVec x pole =
      if p ∈ leaves then 1 else 0 := by
    rw [← f2Potential_neighborSupport_card_cast T x pole]
    change (((T.neighborFinset pole ∩ f2PotentialSupport x).card : ℕ) :
      ZMod 2) = _
    rw [hTline, hline]
    split_ifs <;> simp
  have hAapply : (A.adjMatrix (ZMod 2)).mulVec
      (Pi.single pole 1 + Pi.single other 1) pole = 0 := by
    rw [adjMatrix_mulVec_twoCoordinate_apply]
    simp [SimpleGraph.adjMatrix_apply, hnonadj]
  have hpole := congrFun htransport pole
  dsimp [K] at hpole ⊢
  dsimp [T] at hTapply
  rw [hpole, hTapply, hAapply, add_zero]

end Erdos85

#print axioms Erdos85.binaryTransportResidual_pole_apply_eq_leafIndicator
