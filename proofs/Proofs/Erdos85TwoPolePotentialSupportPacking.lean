import Proofs.Erdos85TwoPoleKernelImageDichotomy
import Proofs.Erdos85BinaryCutGraphTwoPoleRoute
import Proofs.Erdos85C4FreeCommonNeighborUnique

/-!
# Packing a two-pole adjacency potential

This is the sharp support bound `(73rnz_bm)`.  A support point on the first
pole line forces a second support point on every other line through it.
C4-freeness makes those witnesses distinct.
-/

open SimpleGraph

namespace Erdos85

/-- **Two-pole syndrome packing (`73rnz_bm`).** -/
theorem degree_le_card_f2PotentialSupport_of_twoPole
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (hreg : ∀ u, G.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hcommon : G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ = ∅)
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1) :
    q ≤ (f2PotentialSupport x).card := by
  classical
  let X := f2PotentialSupport x
  have hodd₁ : Odd ((G.neighborFinset pole₁ ∩ X).card) := by
    rw [← ZMod.natCast_eq_one_iff_odd,
      f2Potential_neighborSupport_card_cast, hpotential]
    simp [hpoles]
  have hnonempty : (G.neighborFinset pole₁ ∩ X).Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.pos_of_ne_zero (fun hz => by
      rw [hz] at hodd₁
      exact Nat.not_odd_zero hodd₁)
  rcases hnonempty with ⟨p, hp⟩
  have ⟨hpN₁, hpX⟩ := Finset.mem_inter.mp hp
  have hp₁ : G.Adj pole₁ p := (G.mem_neighborFinset pole₁ p).mp hpN₁
  let B := (G.neighborFinset p).erase pole₁
  have hBcard : B.card = q - 1 := by
    rw [show B = (G.neighborFinset p).erase pole₁ from rfl,
      Finset.card_erase_of_mem]
    · rw [G.card_neighborFinset_eq_degree, hreg p]
    · exact (G.mem_neighborFinset p pole₁).mpr hp₁.symm
  have hwitness : ∀ y ∈ B, ∃ w ∈ X, w ≠ p ∧ G.Adj y w := by
    intro y hyB
    have hyN : G.Adj p y :=
      (G.mem_neighborFinset p y).mp (Finset.mem_of_mem_erase hyB)
    have hyne₁ : y ≠ pole₁ := Finset.ne_of_mem_erase hyB
    have hyne₂ : y ≠ pole₂ := by
      intro hy
      subst y
      have hpN₂ : p ∈ G.neighborFinset pole₂ :=
        (G.mem_neighborFinset pole₂ p).mpr hyN.symm
      have : p ∈ G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ :=
        Finset.mem_inter.mpr ⟨hpN₁, hpN₂⟩
      simp [hcommon] at this
    have hAy : (G.adjMatrix (ZMod 2)).mulVec x y = 0 := by
      rw [hpotential]
      simp [hyne₁, hyne₂]
    have heven : Even ((G.neighborFinset y ∩ X).card) := by
      rw [← ZMod.natCast_eq_zero_iff_even,
        f2Potential_neighborSupport_card_cast, hAy]
    have hpMem : p ∈ G.neighborFinset y ∩ X :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y p).mpr hyN.symm, hpX⟩
    have hlt : 1 < (G.neighborFinset y ∩ X).card := by
      have hpos : 0 < (G.neighborFinset y ∩ X).card :=
        Finset.card_pos.mpr ⟨p, hpMem⟩
      rcases heven with ⟨k, hk⟩
      omega
    rcases Finset.one_lt_card.mp hlt with ⟨a, ha, b, hb, hab⟩
    have ⟨haN, haX⟩ := Finset.mem_inter.mp ha
    have ⟨hbN, hbX⟩ := Finset.mem_inter.mp hb
    by_cases hap : a = p
    · exact ⟨b, hbX, fun hbp => hab (hap.trans hbp.symm),
        (G.mem_neighborFinset y b).mp hbN⟩
    · exact ⟨a, haX, hap, (G.mem_neighborFinset y a).mp haN⟩
  let f : {y // y ∈ B} → {z // z ∈ X.erase p} := fun y =>
    ⟨Classical.choose (hwitness y.1 y.2), Finset.mem_erase.mpr
      ⟨(Classical.choose_spec (hwitness y.1 y.2)).2.1,
       (Classical.choose_spec (hwitness y.1 y.2)).1⟩⟩
  have hfinj : Function.Injective f := by
    intro y₁ y₂ heq
    apply Subtype.ext
    have hwEq : (f y₁).1 = (f y₂).1 := congrArg Subtype.val heq
    have hpw : p ≠ (f y₁).1 :=
      (Finset.mem_erase.mp (f y₁).2).1.symm
    have hpy₁ : G.Adj p y₁.1 :=
      (G.mem_neighborFinset p y₁.1).mp (Finset.mem_of_mem_erase y₁.2)
    have hpy₂ : G.Adj p y₂.1 :=
      (G.mem_neighborFinset p y₂.1).mp (Finset.mem_of_mem_erase y₂.2)
    have hy₁w : G.Adj y₁.1 (f y₁).1 :=
      (Classical.choose_spec (hwitness y₁.1 y₁.2)).2.2
    have hy₂w : G.Adj y₂.1 (f y₂).1 :=
      (Classical.choose_spec (hwitness y₂.1 y₂.2)).2.2
    exact commonNeighbor_unique_of_c4Free hfree hpw hpy₁ hy₁w.symm
      hpy₂ (by simpa [hwEq] using hy₂w.symm)
  have hcardle : B.card ≤ (X.erase p).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
  have hXerase : (X.erase p).card = X.card - 1 :=
    Finset.card_erase_of_mem hpX
  have hqpos : 0 < q := by
    have : 0 < (G.neighborFinset pole₁).card :=
      Finset.card_pos.mpr ⟨p, hpN₁⟩
    rwa [G.card_neighborFinset_eq_degree, hreg pole₁] at this
  have hXpos : 0 < X.card := Finset.card_pos.mpr ⟨p, hpX⟩
  rw [hBcard, hXerase] at hcardle
  change q ≤ X.card
  dsimp only [X] at hcardle hXpos ⊢
  omega

end Erdos85

#print axioms Erdos85.degree_le_card_f2PotentialSupport_of_twoPole
