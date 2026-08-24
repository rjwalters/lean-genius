import Proofs.Erdos85TwoPoleMinimumPencilRigidity

/-!
# Pole-line singleton rigidity for a minimum two-pole potential

The exact pencil occupancy map has equal-size domain and codomain, hence is
surjective.  A second supported point on a pole line would then acquire a
second common neighbor with the chosen supported point, contradicting
C4-freeness.  This proves `(73rnz_bo)`.
-/

open SimpleGraph

namespace Erdos85

/-- Every other support point lies with `p` on a non-pole line center. -/
theorem exists_nonPole_commonNeighbor_of_minimum_twoPolePotential
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
    ∀ w, w ∈ f2PotentialSupport x → w ≠ p →
      ∃ y, y ≠ pole₁ ∧ G.Adj p y ∧ G.Adj y w := by
  classical
  let X := f2PotentialSupport x
  let B := (G.neighborFinset p).erase pole₁
  have hunique :=
    existsUnique_otherSupportNeighbor_of_minimum_twoPolePotential
      G hfree hreg x pole₁ pole₂ p hcommon hpotential hcard hpX hp₁
  let f : {y // y ∈ B} → {z // z ∈ X.erase p} := fun y =>
    ⟨Classical.choose (hunique y.1
        ((G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2))
        (Finset.ne_of_mem_erase y.2)),
      Finset.mem_erase.mpr
        ⟨(Classical.choose_spec (hunique y.1
          ((G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2))
          (Finset.ne_of_mem_erase y.2))).1.2.1,
         (Classical.choose_spec (hunique y.1
          ((G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2))
          (Finset.ne_of_mem_erase y.2))).1.1⟩⟩
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
    have hy₁w : G.Adj y₁.1 (f y₁).1 := by
      exact (Classical.choose_spec (hunique y₁.1 hpy₁
        (Finset.ne_of_mem_erase y₁.2))).1.2.2
    have hy₂w : G.Adj y₂.1 (f y₂).1 := by
      exact (Classical.choose_spec (hunique y₂.1 hpy₂
        (Finset.ne_of_mem_erase y₂.2))).1.2.2
    exact commonNeighbor_unique_of_c4Free hfree hpw hpy₁ hy₁w.symm
      hpy₂ (by simpa [hwEq] using hy₂w.symm)
  have hBcard : B.card = q - 1 := by
    rw [show B = (G.neighborFinset p).erase pole₁ from rfl,
      Finset.card_erase_of_mem]
    · rw [G.card_neighborFinset_eq_degree, hreg p]
    · exact (G.mem_neighborFinset p pole₁).mpr hp₁.symm
  have hsamecard : Fintype.card {y // y ∈ B} =
      Fintype.card {z // z ∈ X.erase p} := by
    simp only [Fintype.card_coe, hBcard]
    rw [Finset.card_erase_of_mem (show p ∈ X from hpX)]
    rw [show X.card = q by simpa only [X] using hcard]
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, hsamecard⟩).2
  intro w hwX hwp
  have hwErase : w ∈ X.erase p := Finset.mem_erase.mpr ⟨hwp, hwX⟩
  obtain ⟨y, hy⟩ := hsurj ⟨w, hwErase⟩
  refine ⟨y.1, Finset.ne_of_mem_erase y.2,
    (G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2), ?_⟩
  have hyw : G.Adj y.1 (f y).1 := by
    exact (Classical.choose_spec (hunique y.1
      ((G.mem_neighborFinset p y.1).mp (Finset.mem_of_mem_erase y.2))
      (Finset.ne_of_mem_erase y.2))).1.2.2
  have hv : (f y).1 = w := congrArg Subtype.val hy
  simpa [hv] using hyw

/-- A chosen supported pole-neighbor is the pole line's unique supported
point. -/
theorem twoPolePotentialSupport_inter_poleLine_eq_singleton_of_card_eq
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
    f2PotentialSupport x ∩ G.neighborFinset pole₁ = {p} := by
  classical
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hwX, hwN⟩
    by_contra hwp
    obtain ⟨y, hyne, hpy, hyw⟩ :=
      exists_nonPole_commonNeighbor_of_minimum_twoPolePotential
        G hfree hreg x pole₁ pole₂ p hcommon hpotential hcard hpX hp₁
        w hwX hwp
    have hpolew : G.Adj pole₁ w :=
      (G.mem_neighborFinset pole₁ w).mp hwN
    exact hyne (commonNeighbor_unique_of_c4Free hfree (Ne.symm hwp)
      hpy hyw.symm hp₁.symm hpolew.symm)
  · rintro rfl
    exact ⟨hpX, (G.mem_neighborFinset pole₁ _).mpr hp₁⟩

/-- **Exact two-pole line singleton (`73rnz_bo`).** -/
theorem exists_twoPolePotentialSupport_poleLine_singletons_of_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (hreg : ∀ u, G.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hcommon : G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ = ∅)
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hcard : (f2PotentialSupport x).card = q) :
    ∃ p r,
      f2PotentialSupport x ∩ G.neighborFinset pole₁ = {p} ∧
      f2PotentialSupport x ∩ G.neighborFinset pole₂ = {r} := by
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
  obtain ⟨p, hp⟩ : (G.neighborFinset pole₁ ∩ X).Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.pos_of_ne_zero (fun hz => by
      rw [hz] at hodd₁
      exact Nat.not_odd_zero hodd₁)
  obtain ⟨r, hr⟩ : (G.neighborFinset pole₂ ∩ X).Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.pos_of_ne_zero (fun hz => by
      rw [hz] at hodd₂
      exact Nat.not_odd_zero hodd₂)
  have hpN := (Finset.mem_inter.mp hp).1
  have hpX := (Finset.mem_inter.mp hp).2
  have hrN := (Finset.mem_inter.mp hr).1
  have hrX := (Finset.mem_inter.mp hr).2
  refine ⟨p, r, ?_, ?_⟩
  · exact twoPolePotentialSupport_inter_poleLine_eq_singleton_of_card_eq
      G hfree hreg x pole₁ pole₂ p hcommon hpotential hcard hpX
        ((G.mem_neighborFinset pole₁ p).mp hpN)
  · exact twoPolePotentialSupport_inter_poleLine_eq_singleton_of_card_eq
      G hfree hreg x pole₂ pole₁ r (by simpa [Finset.inter_comm] using hcommon)
        (by simpa [add_comm] using hpotential) hcard hrX
        ((G.mem_neighborFinset pole₂ r).mp hrN)

end Erdos85

#print axioms Erdos85.exists_nonPole_commonNeighbor_of_minimum_twoPolePotential
#print axioms Erdos85.twoPolePotentialSupport_inter_poleLine_eq_singleton_of_card_eq
#print axioms Erdos85.exists_twoPolePotentialSupport_poleLine_singletons_of_card_eq
