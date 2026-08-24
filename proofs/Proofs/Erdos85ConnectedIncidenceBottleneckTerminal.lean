import Proofs.Erdos85ConnectedIncidenceBottleneckDyadicStrict

/-!
# Conditional terminal for NONBIP-CONNECTED

The connected dyadic branch already forces the incidence bottleneck
`E = AD-(J-A)` to have Frobenius energy at least `q^3+2`.  Consequently a
single nonlinear, entrywise-incidence upper bound `||E||_F^2 ≤ q^3` closes
the whole NONBIP-CONNECTED node.  This file formalizes that final composition
and thereby isolates the exact remaining GAP: prove the displayed upper
bound from binary `0/1` realizability (or replace it by any stronger bound).

No such upper bound is asserted here.  It is only a minimal sufficient
AXIOM/GAP, not a currently supported conjecture: through the banked exact
row-cut identity and connected lower bound, it would force every closed
defect-neighborhood cut to attain its minimum `q`, whereas the strict-residue
theorem says their total exceeds `q^3`.  Equivalently it asks for a strong
defect-triangle lower bound, while the established connected theorem gives
the opposite triangle upper bound.  The exact fixed-point-free `q=4` ambient
control also has energy `96 > 4^3`; hence any possible proof must use both
connectedness and the standing `k ≥ 3` hypothesis essentially.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic contradiction at the candidate-(vi) energy interface. -/
theorem false_of_cube_add_two_le_energy_le_cube
    (q : ℕ) (energy : ℤ)
    (hlower : ((q * q * q + 2 : ℕ) : ℤ) ≤ energy)
    (hupper : energy ≤ ((q * q * q : ℕ) : ℤ)) : False := by
  omega

/-- Conditional graph-facing terminal for `NONBIP-CONNECTED`.

The only unproved input is `hupper`, the unsupported nonlinear
binary-incidence energy upper bound described above.  All other hypotheses
are the established connected square-order branch, and the strict lower
bound is already banked. -/
theorem false_of_connected_binarySquare_dyadic_incidenceBottleneck_energy_le_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected)
    (hupper :
      let A := G.adjMatrix ℤ
      let D := (secondOrderDefectGraph G).adjMatrix ℤ
      let J := Matrix.of (fun _ _ : V => (1 : ℤ))
      let E := A * D - (J - A)
      (∑ x : V, ∑ y : V, (E x y) ^ 2) ≤
        ((q * q * q : ℕ) : ℤ)) : False := by
  have hlower :=
    connected_binarySquare_dyadic_incidenceBottleneck_energy_ge_cube_add_two
      G hfree hq hqpow hreg hcard hDconn
  dsimp only at hlower hupper
  exact false_of_cube_add_two_le_energy_le_cube q _ hlower hupper

end

end Erdos85

#print axioms Erdos85.false_of_cube_add_two_le_energy_le_cube
#print axioms Erdos85.false_of_connected_binarySquare_dyadic_incidenceBottleneck_energy_le_cube
