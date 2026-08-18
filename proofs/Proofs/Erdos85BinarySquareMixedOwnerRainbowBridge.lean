import Proofs.Erdos85BinarySquareMixedOwnerComponentSplit
import Proofs.Erdos85BinarySquareOwnerRainbowSymmetry

/-! # Same-component mixed triangles are routing owner rainbows -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The same-component part of the mixed owner-triangle census is nonempty
exactly when some defect component contains the corresponding routing owner
rainbow. -/
theorem sameComponent_mixedOwnerTriangles_nonempty_iff_exists_routingOwnerRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (sameComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).Nonempty ↔
      ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
        routingOwnerRainbow G d a b c := by
  classical
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  let C := componentOwnerGraph G (secondOrderDefectGraph G) c
  constructor
  · rintro ⟨p, hp⟩
    have hp' := (mem_sameComponentCyclicColoredTriples_iff_exists_component
      (secondOrderDefectGraph G) A B C p).mp hp
    rcases hp' with ⟨hcolored, d, hx, hy, hz⟩
    have hadj : A.Adj p.1 p.2.2 ∧ B.Adj p.2.2 p.2.1 ∧
        C.Adj p.2.1 p.1 := by
      exact (Finset.mem_filter.mp hcolored).2
    let x : d.supp := ⟨p.1, hx⟩
    let y : d.supp := ⟨p.2.2, hy⟩
    let z : d.supp := ⟨p.2.1, hz⟩
    refine ⟨d, x, y, z, ?_, ?_, ?_, hadj.1, hadj.2.1, hadj.2.2⟩
    · intro hxy
      exact hadj.1.ne (congrArg Subtype.val hxy)
    · intro hyz
      exact hadj.2.1.ne (congrArg Subtype.val hyz)
    · intro hzx
      exact hadj.2.2.ne (congrArg Subtype.val hzx)
  · rintro ⟨d, x, y, z, hxy, hyz, hzx, ha, hb, hc⟩
    refine ⟨(x.1, z.1, y.1), ?_⟩
    apply (mem_sameComponentCyclicColoredTriples_iff_exists_component
      (secondOrderDefectGraph G) A B C (x.1, z.1, y.1)).mpr
    refine ⟨?_, d, x.2, y.2, z.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb, hc⟩

end

end Erdos85
