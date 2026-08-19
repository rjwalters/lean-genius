import Proofs.Erdos85SizeTwoEigenlineSixTenAntipodalTraceSharp
import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTriangleShape

/-!
# Sharp trace in the high all-triangle C10 branch

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The six directed orderings of the C10 triangle with successive offsets
`3,3,4`, based at `i`. -/
def sixTenLongTrianglePattern (p : ZMod 10 × Fin 6) :
    ZMod 10 × ZMod 10 × ZMod 10 :=
  let i := p.1
  ![(i, i + 3, i + 6), (i, i + 6, i + 3),
    (i + 3, i, i + 6), (i + 3, i + 6, i),
    (i + 6, i, i + 3), (i + 6, i + 3, i)] p.2

theorem sixTenLongTrianglePattern_injective :
    Function.Injective sixTenLongTrianglePattern := by
  decide

set_option maxHeartbeats 800000 in
/-- Every encoded `3,3,4` pattern is a directed antipodal triangle when the
long C10 shore has support `{±3,±4}`. -/
theorem sixTenLongTrianglePattern_mem_cyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (v : ZMod 10 → V)
    (hoff : ∀ i j, (antipodalGraph G).Adj (v i) (v j) ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7) :
    ∀ p : ZMod 10 × Fin 6,
      let q := sixTenLongTrianglePattern p
      (v q.1, v q.2.1, v q.2.2) ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
  intro p
  have hanti : ∀ x y : ZMod 10,
      (y - x = 3 ∨ y - x = 4 ∨ y - x = 6 ∨ y - x = 7) →
        (antipodalGraph G).Adj (v x) (v y) := by
    intro x y h
    exact (hoff x y).2 h
  rcases p with ⟨i, k⟩
  simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
    true_and]
  fin_cases k
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti i (i + 6) (by right; right; left; ring),
      hanti (i + 6) (i + 3) (by right; right; right; ring_nf; decide),
      hanti (i + 3) i (by right; right; right; ring_nf; decide)⟩
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti i (i + 3) (by left; ring),
      hanti (i + 3) (i + 6) (by left; ring),
      hanti (i + 6) i (by right; left; ring_nf; decide)⟩
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti (i + 3) (i + 6) (by left; ring),
      hanti (i + 6) i (by right; left; ring_nf; decide),
      hanti i (i + 3) (by left; ring)⟩
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti (i + 3) i (by right; right; right; ring_nf; decide),
      hanti i (i + 6) (by right; right; left; ring),
      hanti (i + 6) (i + 3) (by right; right; right; ring_nf; decide)⟩
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti (i + 6) (i + 3) (by right; right; right; ring_nf; decide),
      hanti (i + 3) i (by right; right; right; ring_nf; decide),
      hanti i (i + 6) (by right; right; left; ring)⟩
  · dsimp [sixTenLongTrianglePattern]
    exact ⟨hanti (i + 6) i (by right; left; ring_nf; decide),
      hanti i (i + 3) (by left; ring),
      hanti (i + 3) (i + 6) (by left; ring)⟩

/-- Add the 60 all-long `3,3,4` patterns to any 180 cyclic triples each of
which contains a vertex off the long shore. -/
theorem antipodalCubeTrace_ge_twoForty_of_mixedTriples_and_highC10
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (v : ZMod 10 → V) (hvinj : Function.Injective v)
    (hoff : ∀ i j, (antipodalGraph G).Adj (v i) (v j) ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7)
    (F : Finset (V × V × V))
    (hFcard : F.card = 180)
    (hFmem : ∀ q ∈ F, q ∈ cyclicColoredTriples
      (antipodalGraph G) (antipodalGraph G) (antipodalGraph G))
    (hFoff : ∀ q ∈ F,
      q.1 ∉ Set.range v ∨ q.2.1 ∉ Set.range v ∨ q.2.2 ∉ Set.range v) :
    (240 : ℤ) ≤ Matrix.trace
      ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  classical
  let g : ZMod 10 × Fin 6 → V × V × V := fun p =>
    let q := sixTenLongTrianglePattern p
    (v q.1, v q.2.1, v q.2.2)
  let L := (Finset.univ : Finset (ZMod 10 × Fin 6)).image g
  have hginj : Function.Injective g := by
    intro p p' heq
    apply sixTenLongTrianglePattern_injective
    apply Prod.ext
    · exact hvinj (congrArg Prod.fst heq)
    · apply Prod.ext
      · exact hvinj (congrArg (fun q => q.2.1) heq)
      · exact hvinj (congrArg (fun q => q.2.2) heq)
  have hLcard : L.card = 60 := by
    change ((Finset.univ : Finset (ZMod 10 × Fin 6)).image g).card = 60
    rw [Finset.card_image_of_injective _ hginj]
    decide
  have hLmem : ∀ q ∈ L, q ∈ cyclicColoredTriples
      (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact sixTenLongTrianglePattern_mem_cyclicColoredTriples G v hoff p
  have hLrange : ∀ q ∈ L,
      q.1 ∈ Set.range v ∧ q.2.1 ∈ Set.range v ∧ q.2.2 ∈ Set.range v := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  have hdisj : Disjoint F L := by
    rw [Finset.disjoint_left]
    intro q hqF hqL
    rcases hFoff q hqF with h1 | h2 | h3
    · exact h1 (hLrange q hqL).1
    · exact h2 (hLrange q hqL).2.1
    · exact h3 (hLrange q hqL).2.2
  have hunion : ∀ q ∈ F ∪ L, q ∈ cyclicColoredTriples
      (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqF | hqL
    · exact hFmem q hqF
    · exact hLmem q hqL
  have hcardle := Finset.card_le_card_of_injOn
    (fun q : V × V × V => q) hunion (by
      intro x _ y _ h
      exact h)
  rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples]
  have hcard : (F ∪ L).card = 240 := by
    rw [Finset.card_union_of_disjoint hdisj, hFcard, hLcard]
  exact_mod_cast hcard ▸ hcardle

/-- In the high `{±3,±4}` all-triangle long-shore branch, the 180 forced
mixed-shore directed triangles and the 60 internal C10 directed triangles
are disjoint, so the antipodal cube trace is at least 240. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_high_antipodalCubeTrace_ge_twoForty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hoff : ∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7) :
    (240 : ℤ) ≤ Matrix.trace
      ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  obtain ⟨F, hFcard, hFmem, hFoff⟩ :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_exists_mixedTriples_card_oneEighty
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  exact antipodalCubeTrace_ge_twoForty_of_mixedTriples_and_highC10
    G (fun i => (v i).1) (fun _ _ h => hvinj (Subtype.ext h)) hoff
      F hFcard hFmem hFoff

end


end Erdos85

#print axioms Erdos85.sixTenLongTrianglePattern_injective
#print axioms Erdos85.sixTenLongTrianglePattern_mem_cyclicColoredTriples
#print axioms Erdos85.antipodalCubeTrace_ge_twoForty_of_mixedTriples_and_highC10
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_high_antipodalCubeTrace_ge_twoForty
