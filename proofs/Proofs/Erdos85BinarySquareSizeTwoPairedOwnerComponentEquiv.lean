import Proofs.Erdos85BinarySquareSizeTwoCrossOwnerComponentSize

/-! # Paired owner factors have canonically equivalent components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Swapping the two sides identifies a component cross-block graph with the
reverse cross-block graph. -/
def componentCrossBipartiteGraphIsoSwap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    componentCrossBipartiteGraph G c d ≃g
      componentCrossBipartiteGraph G d c where
  toEquiv := Equiv.sumComm c.supp d.supp
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;>
      simp [componentCrossBipartiteGraph, adj_comm]

/-- The side swap induces an equivalence of cross-block cycle components. -/
def componentCrossBipartiteComponentEquivSwap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentCrossBipartiteGraph G c d).ConnectedComponent ≃
      (componentCrossBipartiteGraph G d c).ConnectedComponent :=
  (componentCrossBipartiteGraphIsoSwap G c d).connectedComponentEquiv

/-- Side swap preserves the order of every cross-block component. -/
theorem componentCrossBipartiteComponentEquivSwap_supp_ncard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    ((componentCrossBipartiteComponentEquivSwap G c d) e).supp.ncard =
      e.supp.ncard := by
  let φ := componentCrossBipartiteGraphIsoSwap G c d
  let s := ConnectedComponent.isoEquivSupp φ e
  calc
    ((componentCrossBipartiteComponentEquivSwap G c d) e).supp.ncard =
        Nat.card (((componentCrossBipartiteComponentEquivSwap G c d) e).supp) :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card e.supp := (Nat.card_congr s).symm
    _ = e.supp.ncard := Nat.card_coe_set_eq _

/-- Composing owner-to-cross, side swap, and inverse owner-to-cross gives a
canonical equivalence between the cycle components of paired restricted owner
factors. -/
def binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    (restrictedComponentOwnerGraph G c d).ConnectedComponent ≃
      (restrictedComponentOwnerGraph G d c).ConnectedComponent :=
  (binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
      G hfree hq hreg hcard c d hc).trans
    ((componentCrossBipartiteComponentEquivSwap G c d).trans
      (binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
        G hfree hq hreg hcard d c hd).symm)

/-- In particular, paired restricted owner factors have the same number of
cycle components. -/
theorem binarySquare_regular_twoSizeTwoParts_pairedOwnerComponent_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    Fintype.card
        (restrictedComponentOwnerGraph G c d).ConnectedComponent =
      Fintype.card
        (restrictedComponentOwnerGraph G d c).ConnectedComponent :=
  Fintype.card_congr
    (binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
      G hfree hq hreg hcard c d hc hd)

/-- The canonical paired-component equivalence preserves each individual
cycle order. -/
theorem binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv_supp_ncard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (a : (restrictedComponentOwnerGraph G c d).ConnectedComponent) :
    ((binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
        G hfree hq hreg hcard c d hc hd) a).supp.ncard = a.supp.ncard := by
  let Ec := binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    G hfree hq hreg hcard c d hc
  let Ed := binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    G hfree hq hreg hcard d c hd
  let S := componentCrossBipartiteComponentEquivSwap G c d
  let P := binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
    G hfree hq hreg hcard c d hc hd
  let b := P a
  have hcsize : (Ec a).supp.ncard = 2 * a.supp.ncard := by
    simpa [Ec, binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross]
      using binarySquare_regular_twoSizeTwoParts_crossComponent_ncard_eq_two_mul_owner
        G hfree hq hreg hcard c d hc hd a
  have hdsize : (Ed b).supp.ncard = 2 * b.supp.ncard := by
    simpa [Ed, binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross]
      using binarySquare_regular_twoSizeTwoParts_crossComponent_ncard_eq_two_mul_owner
        G hfree hq hreg hcard d c hd hc b
  have hlink : Ed b = S (Ec a) := by
    simp [b, P, Ec, Ed, S,
      binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv]
  have hswap : (S (Ec a)).supp.ncard = (Ec a).supp.ncard := by
    exact componentCrossBipartiteComponentEquivSwap_supp_ncard G c d (Ec a)
  rw [hlink] at hdsize
  change b.supp.ncard = a.supp.ncard
  omega

end

end Erdos85
