import Proofs.Erdos85BinarySquareOwnerBlockEquitable
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus

/-! # Component-pattern capacities for mixed-owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Mixed colored triples with their three vertices in prescribed defect
components, in cyclic order. -/
def cyclicColoredTriplesInBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent) : Finset (V × V × V) :=
  (cyclicColoredTriples A B C).filter fun p =>
    p.1 ∈ e.supp ∧ p.2.2 ∈ f.supp ∧ p.2.1 ∈ g.supp

/-- A fixed component-membership pattern is bounded by the number of
two-step walks in its first two owner colors.  The two block degrees are
exactly the equitable owner-quotient entries. -/
theorem binarySquare_regular_card_cyclicColoredTriplesInBlocks_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b c e f g : (secondOrderDefectGraph G).ConnectedComponent) :
    (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card ≤
        q * m e *
          (if e = f then m a * (m f - 1) else m a * m f) *
          (if f = g then m b * (m g - 1) else m b * m g) := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let C := componentOwnerGraph G D c
  let T := (e.supp.toFinite.toFinset).sigma fun x =>
    (componentNeighborFinset A D f x).sigma fun y =>
      componentNeighborFinset B D g y
  have hle : (cyclicColoredTriplesInBlocks D A B C e f g).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : V × V × V => (⟨p.1, ⟨p.2.2, p.2.1⟩⟩ :
        Σ x : V, Σ y : V, V))
    · intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpColor := (Finset.mem_filter.mp hpFilter.1).2
      change (⟨p.1, ⟨p.2.2, p.2.1⟩⟩ : Σ x : V, Σ y : V, V) ∈ T
      simp only [T, Finset.mem_sigma]
      refine ⟨by simpa using hpFilter.2.1, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1,
          (ConnectedComponent.mem_supp_iff f p.2.2).mp hpFilter.2.2.1⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(B.mem_neighborFinset p.2.2 p.2.1).mpr hpColor.2.1,
          (ConnectedComponent.mem_supp_iff g p.2.1).mp hpFilter.2.2.2⟩
    · intro p hp p' hp' heq
      rcases p with ⟨x, z, y⟩
      rcases p' with ⟨x', z', y'⟩
      simp only at heq
      cases heq
      rfl
  calc
    (cyclicColoredTriplesInBlocks D A B C e f g).card ≤ T.card := hle
    _ = q * m e *
          (if e = f then m a * (m f - 1) else m a * m f) *
          (if f = g then m b * (m g - 1) else m b * m g) := by
      simp only [T, Finset.card_sigma]
      have heCard : e.supp.toFinite.toFinset.card = q * m e := by
        simpa using (Set.ncard_eq_toFinset_card' e.supp).symm.trans (hm e)
      let kA := if e = f then m a * (m f - 1) else m a * m f
      let kB := if f = g then m b * (m g - 1) else m b * m g
      have houter : ∀ x ∈ e.supp.toFinite.toFinset,
          (componentNeighborFinset A D f x).card = kA := by
        intro x hx
        have hx' : x ∈ e.supp := by simpa using hx
        simpa [A, D, kA] using
          binarySquare_regular_componentOwnerGraph_blockNeighborCard
            G hfree hq hreg hcard m hm a e f ⟨x, hx'⟩
      have hinner : ∀ y ∈ f.supp.toFinite.toFinset,
          (componentNeighborFinset B D g y).card = kB := by
        intro y hy
        have hy' : y ∈ f.supp := by simpa using hy
        simpa [B, D, kB] using
          binarySquare_regular_componentOwnerGraph_blockNeighborCard
            G hfree hq hreg hcard m hm b f g ⟨y, hy'⟩
      calc
        (∑ x ∈ e.supp.toFinite.toFinset,
            ∑ y ∈ componentNeighborFinset A D f x,
              (componentNeighborFinset B D g y).card) =
            ∑ x ∈ e.supp.toFinite.toFinset, kA * kB := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                (∑ y ∈ componentNeighborFinset A D f x,
                    (componentNeighborFinset B D g y).card) =
                    (componentNeighborFinset A D f x).card * kB := by
                      apply Finset.sum_const_nat
                      intro y hy
                      have hyComp : D.connectedComponentMk y = f :=
                        (Finset.mem_filter.mp hy).2
                      exact hinner y
                        (by simpa using
                          (ConnectedComponent.mem_supp_iff f y).mpr hyComp)
                _ = kA * kB := by rw [houter x hx]
        _ = q * m e * kA * kB := by
          rw [Finset.sum_const, heCard, nsmul_eq_mul]
          simp [Nat.mul_assoc]
        _ = _ := by rfl

/-- The `|Comp|³` component-membership blocks partition the entire mixed
colored-triple census exactly. -/
theorem sum_card_cyclicColoredTriplesInBlocks_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (∑ e : D.ConnectedComponent,
      ∑ f : D.ConnectedComponent,
        ∑ g : D.ConnectedComponent,
          (cyclicColoredTriplesInBlocks D A B C e f g).card) =
      (cyclicColoredTriples A B C).card := by
  classical
  let S := cyclicColoredTriples A B C
  let Sx := fun e : D.ConnectedComponent =>
    S.filter fun p => D.connectedComponentMk p.1 = e
  let Sxy := fun e f : D.ConnectedComponent =>
    (Sx e).filter fun p => D.connectedComponentMk p.2.2 = f
  have hx : S.card = ∑ e : D.ConnectedComponent, (Sx e).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset D.ConnectedComponent))
      (f := fun p => D.connectedComponentMk p.1)
      (fun _ _ => Finset.mem_univ _)]
  have hxy : (∑ e : D.ConnectedComponent, (Sx e).card) =
      ∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
        (Sxy e f).card := by
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Sx e) (t := (Finset.univ : Finset D.ConnectedComponent))
      (f := fun p => D.connectedComponentMk p.2.2)
      (fun _ _ => Finset.mem_univ _)]
  have hxyz :
      (∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
        (Sxy e f).card) =
      ∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
        ∑ g : D.ConnectedComponent,
          ((Sxy e f).filter fun p =>
            D.connectedComponentMk p.2.1 = g).card := by
    apply Finset.sum_congr rfl
    intro e _he
    apply Finset.sum_congr rfl
    intro f _hf
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Sxy e f) (t := (Finset.univ : Finset D.ConnectedComponent))
      (f := fun p => D.connectedComponentMk p.2.1)
      (fun _ _ => Finset.mem_univ _)]
  symm
  calc
    (cyclicColoredTriples A B C).card = S.card := by rfl
    _ = ∑ e : D.ConnectedComponent, (Sx e).card := hx
    _ = ∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
          (Sxy e f).card := hxy
    _ = ∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
          ∑ g : D.ConnectedComponent,
            ((Sxy e f).filter fun p =>
              D.connectedComponentMk p.2.1 = g).card := hxyz
    _ = ∑ e : D.ConnectedComponent, ∑ f : D.ConnectedComponent,
          ∑ g : D.ConnectedComponent,
            (cyclicColoredTriplesInBlocks D A B C e f g).card := by
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro f _hf
      apply Finset.sum_congr rfl
      intro g _hg
      congr 1
      ext p
      simp [Sxy, Sx, S, cyclicColoredTriplesInBlocks,
        ConnectedComponent.mem_supp_iff, and_assoc, and_left_comm, and_comm]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_card_cyclicColoredTriplesInBlocks_le
#print axioms Erdos85.sum_card_cyclicColoredTriplesInBlocks_eq
