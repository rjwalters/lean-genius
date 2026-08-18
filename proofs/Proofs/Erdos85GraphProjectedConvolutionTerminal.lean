import Proofs.Erdos85ZModProjectionFiber

/-!
# Graph terminal from projected convolution constancy

All combinatorial and parity inputs are discharged here.  For a prime-order
quotient `p ≥ 7`, the only remaining hypothesis is the convolution constancy
which the square Fourier-operator branch must provide.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem false_of_graph_projectedAnchor_convolution_constancy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r p : ℕ} [NeZero r] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 7 ≤ r) (hrOdd : Odd r)
    (hp : 7 ≤ p) (hpdiv : p ∣ r)
    (hoddQuotient : Odd (r / p))
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hoddComponents : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (b : ZMod r) (hb : b + b = 1)
    (hconstant :
      let q := ZMod.castHom hpdiv (ZMod p)
      let a := q b
      let m : ZMod r → ℕ := anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
      ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
        cyclicConvolution
            (fun y ↦ (projectedMultiplicity q m y : ℤ))
            (fun y ↦ (projectedMultiplicity q m y : ℤ)) a =
          cyclicConvolution
            (fun y ↦ (projectedMultiplicity q m y : ℤ))
            (fun y ↦ (projectedMultiplicity q m y : ℤ)) g) : False := by
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  have hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r := by
    intro h
    exact odd_graph_diagonalAnchorMultiplicity_iff
      G hfree hd heven hmin hcard (by omega) hrOdd u hu huRange huD
        hsep hoddComponents h
  exact false_of_zmod_projection_and_convolution_constancy
    hpdiv hp hr hrOdd hoddQuotient b hb m hbase hconstant

end

end Erdos85
