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

end


end Erdos85

#print axioms Erdos85.sixTenLongTrianglePattern_injective
#print axioms Erdos85.sixTenLongTrianglePattern_mem_cyclicColoredTriples
