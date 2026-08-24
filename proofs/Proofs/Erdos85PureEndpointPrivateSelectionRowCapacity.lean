import Proofs.Erdos85PureEndpointPrivateSelectionCollisionRigidity
import Proofs.Erdos85PureEndpointOffShoreSelectionFiberBound

/-!
# Almost-injective capacity of the off-shore private row

If every selection collision maps, through an injective realization, to one
fixed exceptional point and every fiber has size at most two, then the domain
has size at most the image size plus one.  The private-selection collision
rigidity supplies exactly this situation at the forced half-occupancy vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A map whose collisions can occur only over one injectively realized
exceptional value, and whose fibers have size at most two, loses at most one
element under `Finset.image`. -/
theorem card_le_card_image_add_one_of_unique_exceptional_collision
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (f : A → B) (g : B → Z) (z : Z)
    (hg : Function.Injective g)
    (hfiber : ∀ b, (s.filter fun a => f a = b).card ≤ 2)
    (hcollision : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = f j → g (f i) = z) :
    s.card ≤ (s.image f).card + 1 := by
  classical
  let T := s.image f
  have hsmall : ∀ b ∈ T,
      (s.filter fun a => f a = b).card ≤
        1 + if g b = z then 1 else 0 := by
    intro b hb
    by_cases hbz : g b = z
    · simp [hbz]
      exact hfiber b
    · simp [hbz]
      apply Finset.card_le_one.mpr
      intro i hi j hj
      have hiData := Finset.mem_filter.mp hi
      have hjData := Finset.mem_filter.mp hj
      by_contra hij
      have hc := hcollision i hiData.1 j hjData.1 hij
        (hiData.2.trans hjData.2.symm)
      rw [hiData.2] at hc
      exact hbz hc
  have hsum := Finset.sum_card_fiberwise_eq_card_filter s T f
  have hfilter : s.filter (fun a => f a ∈ T) = s := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).1
    · intro ha
      apply Finset.mem_filter.mpr
      exact ⟨ha, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  rw [hfilter] at hsum
  calc
    s.card = ∑ b ∈ T, (s.filter fun a => f a = b).card := hsum.symm
    _ ≤ ∑ b ∈ T, (1 + if g b = z then 1 else 0) :=
      Finset.sum_le_sum hsmall
    _ ≤ T.card + 1 := by
      by_cases hz : ∃ b ∈ T, g b = z
      · obtain ⟨b₀, hb₀T, hb₀z⟩ := hz
        have hunique : ∀ b ∈ T, g b = z ↔ b = b₀ := by
          intro b _hb
          constructor
          · intro hbz
            exact hg (hbz.trans hb₀z.symm)
          · rintro rfl
            exact hb₀z
        calc
          (∑ b ∈ T, (1 + if g b = z then 1 else 0)) =
              ∑ b ∈ T, (1 + if b = b₀ then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro b hb
                by_cases hbb : b = b₀
                · subst b
                  simp [hb₀z]
                · have hgn : g b ≠ z := fun h => hbb ((hunique b hb).mp h)
                  simp [hbb, hgn]
          _ = T.card + 1 := by
            simp [Finset.sum_add_distrib, hb₀T]
          _ ≤ T.card + 1 := le_rfl
      · have hnone : ∀ b ∈ T, g b ≠ z := by
          intro b hb hbz
          exact hz ⟨b, hb, hbz⟩
        calc
          (∑ b ∈ T, (1 + if g b = z then 1 else 0)) =
              ∑ _b ∈ T, 1 := by
                apply Finset.sum_congr rfl
                intro b hb
                simp [hnone b hb]
          _ = T.card := by simp
          _ ≤ T.card + 1 := Nat.le_succ _
    _ = (s.image f).card + 1 := by rfl

/-- The off-shore centers whose canonical private points neighbor the forced
half-occupancy vertex map almost injectively under the canonical pair
selection: their number is at most the number of selected pair blocks plus
one. -/
theorem c4Free_binarySquare_pureEndpoint_privateSelection_rowCapacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let C := {i : V // i ∈ F}
    let I := {e : Finset V // e ∈ F.powersetCard 2}
    let O := {i : V // i ∈ F ∧ i ∉ S}
    ∃ p : C → V, ∃ φ : I → V, ∃ σ : O → I, ∃ w,
      let A := (Finset.univ : Finset O).filter fun i =>
        G.Adj (p ⟨i.1, i.2.1⟩) w
      (G.neighborFinset w ∩ S).card = m ∧
      A.card ≤ (A.image σ).card + 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let O := {i : V // i ∈ F ∧ i ∉ S}
  obtain ⟨p, φ, σ, w, hpInj, hφInj, hwCard, _hpTwo,
      hinc, _halign, hcollision⟩ :=
    c4Free_binarySquare_pureEndpoint_privateSelection_collisionRigidity
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let A := (Finset.univ : Finset O).filter fun i =>
    G.Adj (p ⟨i.1, i.2.1⟩) w
  have hfiber : ∀ e : I, (A.filter fun i => σ i = e).card ≤ 2 := by
    intro e
    have hsub : A.filter (fun i => σ i = e) ⊆
        (Finset.univ : Finset O).filter fun i => σ i = e := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    apply (Finset.card_le_card hsub).trans
    apply incident_twoSubset_selection_fiber_card_le_two
      (val := fun i : O => i.1) (edge := fun e : I => e.1)
      (σ := σ) (e := e)
    · exact Subtype.val_injective
    · intro a
      exact (Finset.mem_powersetCard.1 a.2).2
    · exact hinc
  have hcap := card_le_card_image_add_one_of_unique_exceptional_collision
    A σ φ w hφInj hfiber
  apply_rules [Exists.intro p, Exists.intro φ, Exists.intro σ,
    Exists.intro w]
  exact ⟨hwCard, hcap (by
    intro i hiA j hjA hij hσij
    have hiAdj := (Finset.mem_filter.mp hiA).2
    have hjAdj := (Finset.mem_filter.mp hjA).2
    exact hcollision i j hij hiAdj hjAdj hσij)⟩

end

end Erdos85

#print axioms
  Erdos85.card_le_card_image_add_one_of_unique_exceptional_collision
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateSelection_rowCapacity
