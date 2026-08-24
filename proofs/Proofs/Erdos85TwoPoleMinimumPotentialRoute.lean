import Proofs.Erdos85TwoPolePotentialSupportPacking

/-!
# The route carried by a minimum two-pole potential

This formalizes `(73rnz_bn)`: equality in the sharp two-pole support packing
forces an explicit alternating path of length four between the poles.
-/

open SimpleGraph

namespace Erdos85

/-- **Minimum two-pole route (`73rnz_bn`).**  If a two-pole potential has the
minimum possible support size `q`, then the two poles are joined by a
length-four walk whose two point vertices lie in the support. -/
theorem exists_lengthFourRoute_of_twoPolePotentialSupport_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (hreg : ∀ u, G.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hcommon : G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ = ∅)
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hcard : (f2PotentialSupport x).card = q) :
    ∃ p y r,
      p ∈ f2PotentialSupport x ∧ r ∈ f2PotentialSupport x ∧ p ≠ r ∧
      G.Adj pole₁ p ∧ G.Adj p y ∧ G.Adj y r ∧ G.Adj r pole₂ := by
  classical
  let X := f2PotentialSupport x
  have hodd₁ : Odd ((G.neighborFinset pole₁ ∩ X).card) := by
    rw [← ZMod.natCast_eq_one_iff_odd,
      f2Potential_neighborSupport_card_cast, hpotential]
    simp [hpoles]
  have hodd₂ : Odd ((G.neighborFinset pole₂ ∩ X).card) := by
    rw [← ZMod.natCast_eq_one_iff_odd,
      f2Potential_neighborSupport_card_cast, hpotential]
    simp [hpoles]
  obtain ⟨p, hpN₁, hpX⟩ :
      ∃ p, p ∈ G.neighborFinset pole₁ ∧ p ∈ X := by
    have hn : (G.neighborFinset pole₁ ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      exact Nat.pos_of_ne_zero (fun hz => by
        rw [hz] at hodd₁
        exact Nat.not_odd_zero hodd₁)
    rcases hn with ⟨p, hp⟩
    exact ⟨p, (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
  obtain ⟨r, hrN₂, hrX⟩ :
      ∃ r, r ∈ G.neighborFinset pole₂ ∧ r ∈ X := by
    have hn : (G.neighborFinset pole₂ ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      exact Nat.pos_of_ne_zero (fun hz => by
        rw [hz] at hodd₂
        exact Nat.not_odd_zero hodd₂)
    rcases hn with ⟨r, hr⟩
    exact ⟨r, (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩
  have hp₁ : G.Adj pole₁ p := (G.mem_neighborFinset pole₁ p).mp hpN₁
  have hr₂ : G.Adj r pole₂ :=
    ((G.mem_neighborFinset pole₂ r).mp hrN₂).symm
  have hpnotN₂ : p ∉ G.neighborFinset pole₂ := by
    intro hpN₂
    have : p ∈ G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ :=
      Finset.mem_inter.mpr ⟨hpN₁, hpN₂⟩
    simpa [hcommon] using this
  have hpr : p ≠ r := by
    intro h
    apply hpnotN₂
    simpa [h] using hrN₂
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
      exact hpnotN₂ ((G.mem_neighborFinset pole₂ p).mpr hyN.symm)
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
  have hsamecard : Fintype.card {y // y ∈ B} =
      Fintype.card {z // z ∈ X.erase p} := by
    simp only [Fintype.card_coe, hBcard, Finset.card_erase_of_mem hpX]
    rw [show X.card = q by simpa only [X] using hcard]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hsamecard⟩
  have hrErase : r ∈ X.erase p := Finset.mem_erase.mpr ⟨hpr.symm, hrX⟩
  obtain ⟨y, hy⟩ := hfbij.2 ⟨r, hrErase⟩
  refine ⟨p, y.1, r, hpX, hrX, hpr, hp₁, ?_, ?_, hr₂⟩
  · exact (G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2)
  · have := (Classical.choose_spec (hwitness y.1 y.2)).2.2
    change G.Adj y.1 (f y).1 at this
    have hv : (f y).1 = r := congrArg Subtype.val hy
    simpa [hv] using this

end Erdos85

#print axioms Erdos85.exists_lengthFourRoute_of_twoPolePotentialSupport_card_eq
