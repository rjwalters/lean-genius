import Proofs.Erdos85Problem

/-!
# The regularity-free defect-degree bound

In a `C4`-free graph with minimum degree at least `d`, the punctured
neighborhoods of a vertex's neighbors are pairwise disjoint, so at least
`d(d-1)` other vertices share a common neighbor with any given vertex.
The number of "defect partners" — vertices with **no** common
neighbor — is therefore at most `m - 1 - d(d-1)`, with no regularity
hypothesis.  At plateau orders `m ≤ d(d-1) + 3 + e` this bounds the
defect degree by `e + 2` for every vertex of every subgraph
configuration arising in surgery arguments.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The defect partners of `v`: other vertices with no common
neighbor. -/
def defectPartners (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset V :=
  Finset.univ.filter fun u ↦ u ≠ v ∧
    (G.neighborFinset u ∩ G.neighborFinset v) = ∅

theorem mem_defectPartners (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) : u ∈ defectPartners G v ↔ u ≠ v ∧
      (G.neighborFinset u ∩ G.neighborFinset v) = ∅ := by
  simp [defectPartners]

/-- **The defect-degree bound.**  In a `C4`-free graph with minimum
degree at least `d`, every vertex has at most `m - 1 - d(d-1)` defect
partners; equivalently `d(d-1) + #defectPartners ≤ m - 1`. -/
theorem defectPartners_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hmin : d ≤ G.minDegree)
    (v : V) :
    d * (d - 1) + (defectPartners G v).card + 1 ≤ Fintype.card V := by
  classical
  -- The covered set: vertices other than `v` reachable in two steps.
  set B : Finset V :=
    (G.neighborFinset v).biUnion (fun x ↦ (G.neighborFinset x).erase v)
    with hB
  -- Disjointness of the punctured neighborhoods (C4-freeness).
  have hdisj : ∀ x ∈ G.neighborFinset v, ∀ y ∈ G.neighborFinset v,
      x ≠ y → Disjoint ((G.neighborFinset x).erase v)
        ((G.neighborFinset y).erase v) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro u hux huy
    have hux' := Finset.mem_of_mem_erase hux
    have huy' := Finset.mem_of_mem_erase huy
    have huv : u ≠ v := Finset.ne_of_mem_erase hux
    rw [mem_neighborFinset] at hux' huy'
    rw [mem_neighborFinset] at hx hy
    exact hfree (containsC4_of_two_common hxy huv.symm hx hy
      hux'.symm huy'.symm)
  -- Size of the covered set.
  have hBcard : d * (d - 1) ≤ B.card := by
    rw [hB, Finset.card_biUnion hdisj]
    have hterm : ∀ x ∈ G.neighborFinset v,
        d - 1 ≤ ((G.neighborFinset x).erase v).card := by
      intro x hx
      have hdeg : d ≤ (G.neighborFinset x).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact hmin.trans (G.minDegree_le_degree x)
      have herase := Finset.pred_card_le_card_erase (a := v)
        (s := G.neighborFinset x)
      omega
    calc
      d * (d - 1) ≤ (G.neighborFinset v).card * (d - 1) := by
        apply Nat.mul_le_mul_right
        rw [G.card_neighborFinset_eq_degree]
        exact hmin.trans (G.minDegree_le_degree v)
      _ = ∑ _x ∈ G.neighborFinset v, (d - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ G.neighborFinset v, ((G.neighborFinset x).erase v).card :=
        Finset.sum_le_sum hterm
  -- `B` avoids `v` and is disjoint from the defect partners.
  have hvB : v ∉ B := by
    rw [hB, Finset.mem_biUnion]
    rintro ⟨x, _, hvx⟩
    exact (Finset.ne_of_mem_erase hvx) rfl
  have hBdefect : Disjoint B (defectPartners G v) := by
    rw [Finset.disjoint_left]
    intro u huB hud
    rw [hB, Finset.mem_biUnion] at huB
    obtain ⟨x, hx, hux⟩ := huB
    have hux' := Finset.mem_of_mem_erase hux
    rw [mem_neighborFinset] at hux' hx
    rw [mem_defectPartners] at hud
    have hxmem : x ∈ G.neighborFinset u ∩ G.neighborFinset v := by
      rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact ⟨hux'.symm, hx⟩
    rw [hud.2] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)
  have hvD : v ∉ defectPartners G v := by
    rw [mem_defectPartners]
    exact fun h ↦ h.1 rfl
  -- Assemble: `B ⊔ defectPartners ⊔ {v}` fits inside `V`.
  have hunion : (B ∪ defectPartners G v ∪ {v}).card ≤ Fintype.card V := by
    calc
      (B ∪ defectPartners G v ∪ {v}).card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hcards : (B ∪ defectPartners G v ∪ {v}).card =
      B.card + (defectPartners G v).card + 1 := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint
      hBdefect, Finset.card_singleton]
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    rintro (h | h)
    · exact hvB h
    · exact hvD h
  omega

/-- Plateau-order corollary: at order `m ≤ d(d-1) + 3 + e` every vertex
has at most `e + 2` defect partners. -/
theorem defectPartners_card_le_of_plateau_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V ≤ d * (d - 1) + 3 + e) (v : V) :
    (defectPartners G v).card ≤ e + 2 := by
  have h := defectPartners_card_le G hfree hmin v
  omega

end

end Erdos85
