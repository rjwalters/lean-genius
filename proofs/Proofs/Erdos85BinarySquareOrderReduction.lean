import Proofs.Erdos85EnergyMinimalEdgeCover
import Proofs.Erdos85PlaneOrderDropFamily

/-! # Normalized reduction for the binary square-order obstruction -/

open SimpleGraph

namespace Erdos85

/-- The normalized square-order object consumed by the incidence, defect,
and spectral toolkits: energy minimality supplies both the tight-edge cover
and saturation against every admissible degree-balancing edge slide. -/
def SquareOrderTightCoreExists (d : Nat) : Prop :=
  ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin (d * d)) G ∧
    d ≤ G.minDegree ∧
    IsDegreeSquareMinimizer G d ∧
    (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
    ∀ x y z : Fin (d * d), y ≠ z → G.Adj x z → ¬ G.Adj y z →
      G.degree y + 1 < G.degree x →
        HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z

/-- Every nontrivial square-order witness has a normalized tight core. -/
theorem squareOrderTightCoreExists_of_witness
    {d : Nat} (hd : 1 ≤ d)
    (h : C4FreeMinDegreeWitness (d * d) d) :
    SquareOrderTightCoreExists d := by
  rcases h with ⟨G₀, hdec₀, hmin₀, hfree₀⟩
  letI : DecidableRel G₀.Adj := hdec₀
  letI : Nonempty (Fin (d * d)) := ⟨⟨0, by positivity⟩⟩
  obtain ⟨G, hdec, hfree, hmin, hminimal, hcover, hslide⟩ :=
    exists_degreeSquareMinimizer_with_tightCover_and_slideSaturation
      G₀ hfree₀ hmin₀
  exact ⟨G, hdec, hfree, hmin, hminimal, hcover, hslide⟩

/-- Forgetting normalization recovers the original witness. -/
theorem witness_of_squareOrderTightCoreExists
    {d : Nat} (h : SquareOrderTightCoreExists d) :
    C4FreeMinDegreeWitness (d * d) d := by
  rcases h with ⟨G, hdec, hfree, hmin, _hminimal, _hcover, _hslide⟩
  exact ⟨G, hdec, hmin, hfree⟩

theorem squareOrderTightCoreExists_iff_witness
    {d : Nat} (hd : 1 ≤ d) :
    SquareOrderTightCoreExists d ↔
      C4FreeMinDegreeWitness (d * d) d := by
  exact ⟨witness_of_squareOrderTightCoreExists,
    squareOrderTightCoreExists_of_witness hd⟩

/-- Uniform binary obstruction stated only for normalized cores.  This is the
working target for the `63/64`, `255/256`, ... nonexistence jaw. -/
def BinarySquareOrderTightCoreExclusion : Prop :=
  ∀ k : Nat, 3 ≤ k → ¬ SquareOrderTightCoreExists (2 ^ k)

/-- The normalized binary obstruction is exactly the square-order hypothesis
which, together with the characteristic-two polarity witnesses, refutes
eventual monotonicity. -/
theorem binarySquareOrderTightCoreExclusion_iff :
    BinarySquareOrderTightCoreExclusion ↔ BinarySquareOrderExclusion := by
  constructor
  · intro h k hk hwitness
    exact h k hk (squareOrderTightCoreExists_of_witness
      (Nat.one_le_pow k 2 (by decide)) hwitness)
  · intro h k hk hcore
    exact h k hk (witness_of_squareOrderTightCoreExists hcore)

theorem erdos85Negation_of_binarySquareOrderTightCoreExclusion
    (h : BinarySquareOrderTightCoreExclusion) : Erdos85Negation :=
  erdos85Negation_of_binarySquareOrderExclusion
    (binarySquareOrderTightCoreExclusion_iff.mp h)

theorem not_erdos85Question_of_binarySquareOrderTightCoreExclusion
    (h : BinarySquareOrderTightCoreExclusion) : ¬ Erdos85Question :=
  not_erdos85Question_of_binarySquareOrderExclusion
    (binarySquareOrderTightCoreExclusion_iff.mp h)

end Erdos85
