import Proofs.Erdos85C4FreeDefectCutIdentity
import Proofs.Erdos85OrderNineNearRegularCutSpecialization
import Proofs.Erdos85GadgetCounting

/-! # Extracting ordinary q=9 moments from a three-high graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Split a sum over a finite type into a distinguished finset and its
complement subtype. -/
theorem sum_eq_sum_complSubtype_add_sum_finset
    {V M : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid M]
    (H : Finset V) (F : V → M) :
    (∑ x : V, F x) =
      (∑ x : ↥(↑(Finset.univ \ H) : Set V), F x.1) + ∑ h ∈ H, F h := by
  let O := Finset.univ \ H
  have hdis : Disjoint O H := by
    rw [Finset.disjoint_left]
    intro x hxO hxH
    exact (Finset.mem_sdiff.mp hxO).2 hxH
  have hunion : O ∪ H = Finset.univ := by
    ext x
    simp [O]
  have hsplit := Finset.sum_union hdis (f := F)
  rw [hunion] at hsplit
  rw [hsplit]
  congr 1
  exact Finset.sum_subtype O (fun x => by simp [O]) F

/-- Ordinary incidence total after splitting off the high vertices. -/
theorem orderNine_ordinary_neighbor_inter_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V)
    (hSH : Disjoint S H)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9) :
    let O := Finset.univ \ H
    let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ S).card
    (∑ x, f x) = 9 * S.card -
      ∑ h ∈ H, (G.neighborFinset h ∩ S).card := by
  classical
  dsimp only
  let O := Finset.univ \ H
  let F := fun x : V => (G.neighborFinset x ∩ S).card
  have htotal := sum_card_neighbor_inter_eq_sum_degree G S
  have hdeg : (∑ x ∈ S, G.degree x) = 9 * S.card := by
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, 9 := by
        apply Finset.sum_congr rfl
        intro x hxS
        exact hdegOrd x (fun hxH => Finset.disjoint_left.mp hSH hxS hxH)
      _ = 9 * S.card := by simp [mul_comm]
  rw [hdeg] at htotal
  have hsplit := sum_eq_sum_complSubtype_add_sum_finset H F
  dsimp only [F, O] at hsplit
  omega

/-- With zero oriented defect boundary, the generic exact cut identity splits
into the ordinary degree-nine and high degree-ten product moments. -/
theorem orderNine_zeroCut_ordinary_high_product_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (H S : Finset V)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hzero : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 0) :
    let O := Finset.univ \ H
    let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ S).card
    (∑ x, f x * (9 - f x)) +
      (∑ h ∈ H, (G.neighborFinset h ∩ S).card *
        (10 - (G.neighborFinset h ∩ S).card)) =
      S.card * (81 - S.card) := by
  classical
  dsimp only
  let F := fun x : V => (G.neighborFinset x ∩ S).card *
    (G.degree x - (G.neighborFinset x ∩ S).card)
  have hcut := c4Free_defect_cut_add_degree_product_eq_complete_cut
    G hfree S
  dsimp only at hcut
  rw [hzero, zero_add, hcard] at hcut
  have hsplit := sum_eq_sum_complSubtype_add_sum_finset H F
  rw [hsplit] at hcut
  dsimp only [F] at hcut
  convert hcut using 1
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2]
  · apply Finset.sum_congr rfl
    intro x hxH
    rw [hdegHigh x hxH]

#print axioms sum_eq_sum_complSubtype_add_sum_finset
#print axioms orderNine_ordinary_neighbor_inter_sum
#print axioms orderNine_zeroCut_ordinary_high_product_identity

end

end Erdos85
