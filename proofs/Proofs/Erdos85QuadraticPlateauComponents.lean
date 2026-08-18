import Proofs.Erdos85BoundaryConnectedClean
import Proofs.Erdos85ConflictComponents
import Proofs.Erdos85QuadraticConductor

/-!
# Uniformly bounded component count for plateau cores

Every connected component inherits the minimum-degree condition and hence
contains a clean Moore ball of quadratic size.  Combining that componentwise
lower bound with the quadratic witness conductor shows that a plateau core
has fewer than `72` connected components, independently of its degree.
-/

namespace Erdos85

open SimpleGraph

/-- The clean Moore lower bound summed over every connected component. -/
theorem connectedComponent_count_mul_cleanMoore_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree) :
    Fintype.card G.ConnectedComponent * (d * (d - 1) + 2) ≤
      Fintype.card V := by
  classical
  let L := d * (d - 1) + 2
  have hcomponent (c : G.ConnectedComponent) : L ≤ c.supp.ncard :=
    connectedComponent_clean_moore_bound G hfree hd hmin c
  have hparts : (∑ c : G.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
  have hsum : (∑ _c : G.ConnectedComponent, L) ≤
      ∑ c : G.ConnectedComponent, c.supp.ncard := by
    exact Finset.sum_le_sum fun c _ ↦ hcomponent c
  rw [hparts] at hsum
  simpa [L, Nat.mul_comm] using hsum

/-- **Bounded-component plateau localization.** Every nondegenerate plateau
core has fewer than `72` connected components.  The constant comes from
`m < 36d²` and the elementary component bound
`d(d-1)+2 ≥ d²/2`. -/
theorem C4PlateauCore.exists_component_count_lt_seventyTwo
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent < 72 := by
  have hd2 : 2 ≤ d := hcore.two_le_degree hm
  by_cases hd : 3 ≤ d
  · rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
    letI : DecidableRel G.Adj := hdec
    have hcomp := connectedComponent_count_mul_cleanMoore_le_card
      G hfree hd hmin.ge
    have hmUpper : m < 36 * d * d := by
      have hs := C4PlateauCore.order_succ_lt_quadratic hm
        ⟨G, hdec, hmin, hfree, hcover, hnext⟩
      omega
    have hL : d * d ≤ 2 * (d * (d - 1) + 2) := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
      norm_num
      nlinarith
    let k := Fintype.card G.ConnectedComponent
    have hkScale : k * (d * d) ≤
        2 * (k * (d * (d - 1) + 2)) := by
      have := Nat.mul_le_mul_left k hL
      nlinarith
    refine ⟨G, hdec, hmin, hfree, ?_⟩
    simp only [Fintype.card_fin] at hcomp
    by_contra hnot
    have hk72 : 72 ≤ k := by omega
    have h72Scale : 72 * (d * d) ≤ k * (d * d) :=
      Nat.mul_le_mul_right (d * d) hk72
    have hcompScale : 2 * (k * (d * (d - 1) + 2)) ≤ 2 * m :=
      Nat.mul_le_mul_left 2 hcomp
    have hmScale : 2 * m < 72 * (d * d) := by nlinarith
    exact (not_lt_of_ge
      (h72Scale.trans (hkScale.trans hcompScale))) hmScale
  · have hdEq : d = 2 := by omega
    subst d
    rcases hcore.connectedComponent_count_lt with
      ⟨G, hdec, hmin, hfree, hcount⟩
    exact ⟨G, hdec, hmin, hfree, by omega⟩

/-- A sharper use of the same clean Moore bound gives the uniform constant
`44`: for `d ≥ 3`, `5d² ≤ 6(d(d-1)+2)`. -/
theorem C4PlateauCore.exists_component_count_lt_fortyFour
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent < 44 := by
  have hd2 : 2 ≤ d := hcore.two_le_degree hm
  by_cases hd : 3 ≤ d
  · rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
    letI : DecidableRel G.Adj := hdec
    let L := d * (d - 1) + 2
    let k := Fintype.card G.ConnectedComponent
    have hcomp : k * L ≤ m := by
      simpa [k, L] using connectedComponent_count_mul_cleanMoore_le_card
        G hfree hd hmin.ge
    have hmUpper : m < 36 * d * d := by
      have hs := C4PlateauCore.order_succ_lt_quadratic hm
        ⟨G, hdec, hmin, hfree, hcover, hnext⟩
      omega
    have hratio : 5 * (d * d) ≤ 6 * L := by
      obtain ⟨a, rfl⟩ : ∃ a, d = a + 3 := ⟨d - 3, by omega⟩
      dsimp [L]
      nlinarith
    refine ⟨G, hdec, hmin, hfree, ?_⟩
    by_contra hnot
    have hk44 : 44 ≤ k := by omega
    have hA : 44 * (5 * (d * d)) ≤ k * (5 * (d * d)) :=
      Nat.mul_le_mul_right (5 * (d * d)) hk44
    have hB : k * (5 * (d * d)) ≤ k * (6 * L) :=
      Nat.mul_le_mul_left k hratio
    have hC : 6 * (k * L) ≤ 6 * m := Nat.mul_le_mul_left 6 hcomp
    have hchain : 220 * d * d ≤ 6 * m := by
      calc
        220 * d * d = 44 * (5 * (d * d)) := by ring
        _ ≤ k * (5 * (d * d)) := hA
        _ ≤ k * (6 * L) := hB
        _ = 6 * (k * L) := by ring
        _ ≤ 6 * m := hC
    nlinarith
  · have hdEq : d = 2 := by omega
    subst d
    rcases hcore.connectedComponent_count_lt with
      ⟨G, hdec, hmin, hfree, hcount⟩
    exact ⟨G, hdec, hmin, hfree, by omega⟩

end Erdos85
