import Proofs.Erdos85ExteriorPermutationCodeAgreement
import Proofs.Erdos85CrossEdgeTriangleDichotomy

/-! # Row and column partners of an exterior grid cell

The exterior triangle dichotomy translates directly into the partner rule of
the `(rho, phi)` code: a cell has one same-row and one same-column partner when
its two component coordinates are nonadjacent, and neither when they are
adjacent.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact row/column partner dichotomy for an exhaustive signed grid label. -/
theorem c4Free_exteriorGridLabel_partner_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (label : {u : V // u ∉ d.supp} →
      {z : V // z ∈ d.supp ∧ s z = 1} ×
        {z : V // z ∈ d.supp ∧ s z = -1})
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hexhaust : ∀ u y, G.Adj u.1 y → y ∈ d.supp →
      y = (label u).1.1 ∨ y = (label u).2.1)
    (u : {u : V // u ∉ d.supp}) :
    let p := (label u).1.1
    let n := (label u).2.1
    (¬ G.Adj p n →
        (∃! v : {v : V // v ∉ d.supp},
          G.Adj u.1 v.1 ∧ (label v).1 = (label u).1) ∧
        (∃! v : {v : V // v ∉ d.supp},
          G.Adj u.1 v.1 ∧ (label v).2 = (label u).2)) ∧
      (G.Adj p n →
        (¬ ∃ v : {v : V // v ∉ d.supp},
          G.Adj u.1 v.1 ∧ (label v).1 = (label u).1) ∧
        (¬ ∃ v : {v : V // v ∉ d.supp},
          G.Adj u.1 v.1 ∧ (label v).2 = (label u).2)) := by
  classical
  let p := (label u).1.1
  let n := (label u).2.1
  have hpn : p ≠ n := by
    intro h
    have hp := (label u).1.2.2
    have hn := (label u).2.2.2
    change s p = 1 at hp
    change s n = -1 at hn
    rw [h] at hp
    omega
  have htri := exterior_triangle_dichotomy G hfree d u.2
    (label u).1.2.1 (label u).2.2.1 hpn (hadj u).1 (hadj u).2
    (hexhaust u)
  constructor
  · intro hnon
    obtain ⟨hrow, hcol⟩ := htri.2 hnon
    constructor
    · obtain ⟨y, hy, hyuniq⟩ := hrow
      let v : {v : V // v ∉ d.supp} := ⟨y, hy.2.1⟩
      have hvp : (label v).1 = (label u).1 := by
        have hpick := hexhaust v p hy.2.2.symm (label u).1.2.1
        rcases hpick with hpick | hpick
        · apply Subtype.ext
          exact hpick.symm
        · have hs := (label v).2.2.2
          have ht := (label u).1.2.2
          change s (label v).2.1 = -1 at hs
          change s p = 1 at ht
          rw [hpick] at ht
          omega
      refine ⟨v, ⟨hy.1, hvp⟩, ?_⟩
      intro w hw
      apply Subtype.ext
      apply hyuniq w.1
      refine ⟨hw.1, w.2, ?_⟩
      have := (hadj w).1.symm
      simpa [p, hw.2] using this
    · obtain ⟨y, hy, hyuniq⟩ := hcol
      let v : {v : V // v ∉ d.supp} := ⟨y, hy.2.1⟩
      have hvn : (label v).2 = (label u).2 := by
        have hpick := hexhaust v n hy.2.2.symm (label u).2.2.1
        rcases hpick with hpick | hpick
        · have hs := (label v).1.2.2
          have ht := (label u).2.2.2
          change s (label v).1.1 = 1 at hs
          change s n = -1 at ht
          rw [hpick] at ht
          omega
        · apply Subtype.ext
          exact hpick.symm
      refine ⟨v, ⟨hy.1, hvn⟩, ?_⟩
      intro w hw
      apply Subtype.ext
      apply hyuniq w.1
      refine ⟨hw.1, w.2, ?_⟩
      have := (hadj w).2.symm
      simpa [n, hw.2] using this
  · intro hpnadj
    have hnone := htri.1 hpnadj
    constructor
    · rintro ⟨v, huv, hvp⟩
      have hnot := (hnone v.1 huv v.2).1
      apply hnot
      have := (hadj v).1.symm
      simpa [p, hvp] using this
    · rintro ⟨v, huv, hvn⟩
      have hnot := (hnone v.1 huv v.2).2
      apply hnot
      have := (hadj v).2.symm
      simpa [n, hvn] using this

end


end Erdos85

#print axioms Erdos85.c4Free_exteriorGridLabel_partner_dichotomy
