import Proofs.Erdos85TwoPoleMinimumPotentialRoute

/-!
# Pencil rigidity of a minimum two-pole potential

Equality in the sharp support packing makes the witness injection bijective.
Consequently every non-pole line through a chosen support point contains
exactly one further support point.  This is the rigorous pencil core of
`(73rnz_bo)`.
-/

open SimpleGraph

namespace Erdos85

/-- **Minimum two-pole pencil rigidity (core of `73rnz_bo`).** -/
theorem existsUnique_otherSupportNeighbor_of_minimum_twoPolePotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (hreg : ∀ u, G.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ p : V)
    (hcommon : G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ = ∅)
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hcard : (f2PotentialSupport x).card = q)
    (hpX : p ∈ f2PotentialSupport x) (hp₁ : G.Adj pole₁ p) :
    ∀ y, G.Adj p y → y ≠ pole₁ →
      ∃! w, w ∈ f2PotentialSupport x ∧ w ≠ p ∧ G.Adj y w := by
  classical
  let X := f2PotentialSupport x
  have hpN₁ : p ∈ G.neighborFinset pole₁ :=
    (G.mem_neighborFinset pole₁ p).mpr hp₁
  have hpnotN₂ : p ∉ G.neighborFinset pole₂ := by
    intro hpN₂
    have : p ∈ G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ :=
      Finset.mem_inter.mpr ⟨hpN₁, hpN₂⟩
    simpa [hcommon] using this
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
    simp only [Fintype.card_coe, hBcard]
    rw [Finset.card_erase_of_mem (show p ∈ X from hpX)]
    rw [show X.card = q by simpa only [X] using hcard]
  have hfsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, hsamecard⟩).2
  intro y hpy hyne₁
  have hyB : y ∈ B := Finset.mem_erase.mpr
    ⟨hyne₁, (G.mem_neighborFinset p y).mpr hpy⟩
  let ys : {y // y ∈ B} := ⟨y, hyB⟩
  refine ⟨(f ys).1, ?_, ?_⟩
  · exact ⟨(Finset.mem_erase.mp (f ys).2).2,
      (Finset.mem_erase.mp (f ys).2).1,
      (Classical.choose_spec (hwitness ys.1 ys.2)).2.2⟩
  · intro w hw
    have hwErase : w ∈ X.erase p := Finset.mem_erase.mpr ⟨hw.2.1, hw.1⟩
    obtain ⟨ys', hys'⟩ := hfsurj ⟨w, hwErase⟩
    have hpw : p ≠ w := hw.2.1.symm
    have hpy' : G.Adj p ys'.1 :=
      (G.mem_neighborFinset p ys'.1).mp (Finset.mem_of_mem_erase ys'.2)
    have hy'w : G.Adj ys'.1 w := by
      have hchosen := (Classical.choose_spec (hwitness ys'.1 ys'.2)).2.2
      change G.Adj ys'.1 (f ys').1 at hchosen
      have hv : (f ys').1 = w := congrArg Subtype.val hys'
      simpa [hv] using hchosen
    have hyy' : y = ys'.1 :=
      commonNeighbor_unique_of_c4Free hfree hpw hpy hw.2.2.symm
        hpy' hy'w.symm
    have hsub : ys = ys' := Subtype.ext hyy'
    have : f ys = f ys' := congrArg f hsub
    exact (congrArg Subtype.val this |>.trans
      (congrArg Subtype.val hys')).symm

end Erdos85

#print axioms Erdos85.existsUnique_otherSupportNeighbor_of_minimum_twoPolePotential
