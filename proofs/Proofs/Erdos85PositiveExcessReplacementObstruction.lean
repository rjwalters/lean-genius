import Proofs.Erdos85BoundedReplacementObstruction

/-!
# Bounded replacement above the Moore order

The Moore-order replacement obstruction extends without changing its
combinatorial input when the original graph has `q` vertices of order
excess.  Those vertices consume `q` units of the attachment budget: a
delete-`k`/add-`k+1` replacement must pay weighted survivor loss at least
`(k+1) * (d-1-k-q)`.
-/

open SimpleGraph

namespace Erdos85

/-- **Positive-order-excess replacement loss bound.**  If the original
graph has order `d(d-1)+1+q`, deleting `k` vertices and adding a compatible
`k+1` vertex gadget requires total attachment-weighted survivor loss at
least `(k+1)(d-1-k-q)`.

The hypothesis `k+q ≤ d-1` isolates the nontrivial range of the natural
number subtraction. -/
theorem card_succ_mul_degree_pred_sub_card_sub_excess_le_replacementLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k q : ℕ}
    (hd : 1 ≤ d) (hkq : k + q ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (k + 1) * (d - 1 - k - q) ≤
      ∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a := by
  have hsize : Fintype.card W - 1 ≤ d := by omega
  have hbound :=
    card_gadget_mul_degree_sq_le_survivor_mul_gadget_add_two_gadget_pred_add_replacementLoss
      G D K hKle F A hsize hmin hnew hcompat
  have hUcard : Fintype.card {v : V // v ∉ D} =
      (d * (d - 1) + 1 + q) - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hcard, hDcard]
  rw [hUcard, hWcard] at hbound
  have hk : k ≤ d - 1 := by omega
  have hkbase : k ≤ d * (d - 1) + 1 + q := by nlinarith
  have hbasesub :
      d * (d - 1) + 1 + q - k + k = d * (d - 1) + 1 + q :=
    Nat.sub_add_cancel hkbase
  have htail : d - 1 - k - q + (k + q) = d - 1 := by omega
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hsquare : d * d = d * (d - 1) + d := by
    calc
      d * d = d * ((d - 1) + 1) := by rw [hdsub]
      _ = d * (d - 1) + d := by ring
  have hinner : d * d =
      (d * (d - 1) + 1 + q - k) + 2 * k + (d - 1 - k - q) := by
    omega
  have heq : (k + 1) * (d * d) =
      (d * (d - 1) + 1 + q - k) * (k + 1) +
        2 * ((k + 1) * k) + (k + 1) * (d - 1 - k - q) := by
    rw [hinner, Nat.mul_add, Nat.mul_add]
    ring
  rw [heq] at hbound
  simp only [Nat.add_sub_cancel] at hbound
  omega

/-- A successful deletion-only delete-`k`/add-`k+1` replacement whose
deleted vertices are all tight forces the target degree below the
positive-excess replacement polynomial. -/
theorem degree_le_replacementPolynomial_of_positiveExcess_tight_set
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k q : ℕ}
    (hd : 1 ≤ d) (hkq : k + q ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree) (hDtight : ∀ x ∈ D, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    d ≤ (k + 1) * (k + q + 1) + k * (k + 1).choose 2 := by
  have hlower :=
    card_succ_mul_degree_pred_sub_card_sub_excess_le_replacementLoss
      G D (deleteVertexSetGraph G D) (le_refl _) F A hd hkq hcard
        hDcard hWcard hmin hnew hcompat
  have hupper :=
    sum_replacementLoss_le_card_mul_degree_add_card_mul_choose_of_tight_set
      G D F A hDcard hDtight hcompat
  rw [hWcard] at hupper
  have htail : d - 1 - k - q + (k + q + 1) = d := by omega
  nlinarith

/-- Contrapositive no-go form of
`degree_le_replacementPolynomial_of_positiveExcess_tight_set`. -/
theorem not_gadgetCompatible_bounded_replacement_of_positiveExcess_tight_set
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k q : ℕ}
    (hd : 1 ≤ d) (hkq : k + q ≤ d - 1)
    (hlarge : (k + 1) * (k + q + 1) + k * (k + 1).choose 2 < d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree) (hDtight : ∀ x ∈ D, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A := by
  intro hcompat
  have hle := degree_le_replacementPolynomial_of_positiveExcess_tight_set
    G D F A hd hkq hcard hDcard hWcard hmin hDtight hnew hcompat
  omega

end Erdos85
