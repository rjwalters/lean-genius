import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementMultiplicityMoment

/-!
# Classification of a single-collision multiplicity vector

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

If a nonnegative multiplicity vector on `n` bins has total mass `n` and
exactly one colliding pair, it consists of one `2`, one `0`, and `1`
everywhere else.  This converts the sharp collision case into the positional
duplicate/missing interface of
`sizeTwoCyclic_singleDuplicateMissing_displacement`.
-/

namespace Erdos85

noncomputable section

private theorem eq_two_of_choose_two_eq_one (n : ℕ)
    (h : n.choose 2 = 1) : n = 2 := by
  by_contra hn
  have hnle : n ≤ 1 ∨ 3 ≤ n := by omega
  rcases hnle with hnle | hnge
  · interval_cases n <;> norm_num at h
  · have hmono := Nat.choose_le_choose 2 hnge
    norm_num at hmono
    omega

private theorem le_one_of_choose_two_eq_zero (n : ℕ)
    (h : n.choose 2 = 0) : n ≤ 1 := by
  by_contra hn
  have hnge : 2 ≤ n := by omega
  have hmono := Nat.choose_le_choose 2 hnge
  norm_num at hmono
  omega

/-- Exact shape of a finite multiplicity vector with one collision and
average one. -/
theorem exists_singleDuplicateMissing_of_sum_choose_two_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ)
    (hmass : (∑ u : α, m u) = Fintype.card α)
    (hcollision : (∑ u : α, (m u).choose 2) = 1) :
    ∃ duplicate missing : α, duplicate ≠ missing ∧
      ∀ u : α, m u =
        if u = duplicate then 2 else if u = missing then 0 else 1 := by
  classical
  have hsum_ne : (∑ u : α, (m u).choose 2) ≠ 0 := by omega
  obtain ⟨duplicate, _, hdupPos⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hdupLe : (m duplicate).choose 2 ≤ 1 := by
    rw [← hcollision]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset α)) (f := fun u => (m u).choose 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ duplicate)
  have hdupChoose : (m duplicate).choose 2 = 1 := by omega
  have hdup : m duplicate = 2 :=
    eq_two_of_choose_two_eq_one _ hdupChoose
  have hrestCollision :
      (∑ u ∈ (Finset.univ : Finset α).erase duplicate,
        (m u).choose 2) = 0 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset α)
      (fun u => (m u).choose 2) (Finset.mem_univ duplicate)
    rw [hdupChoose, hcollision] at hsplit
    omega
  have hotherLe (u : α) (hu : u ≠ duplicate) : m u ≤ 1 := by
    have humem : u ∈ (Finset.univ : Finset α).erase duplicate := by simp [hu]
    have hterm : (m u).choose 2 = 0 := by
      have hle : (m u).choose 2 ≤
          ∑ v ∈ (Finset.univ : Finset α).erase duplicate,
            (m v).choose 2 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset α).erase duplicate)
          (f := fun v => (m v).choose 2)
          (fun _ _ => Nat.zero_le _) humem
      omega
    exact le_one_of_choose_two_eq_zero _ hterm
  let rest := (Finset.univ : Finset α).erase duplicate
  have hrestMass : (∑ u ∈ rest, m u) + 2 = Fintype.card α := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset α) m
      (Finset.mem_univ duplicate)
    rw [hdup, hmass] at hsplit
    simpa [rest] using hsplit
  have hrestCard : rest.card + 1 = Fintype.card α := by
    have hcardPos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨duplicate⟩
    simp [rest]
    omega
  have hpoint (u : α) (hu : u ∈ rest) :
      m u + (1 - m u) = 1 := by
    have := hotherLe u (Finset.mem_erase.mp hu).1
    omega
  have hdefectSum : (∑ u ∈ rest, (1 - m u)) = 1 := by
    have hsumPoint := Finset.sum_congr rfl (fun u hu => hpoint u hu)
    change (∑ u ∈ rest, (m u + (1 - m u))) = ∑ _u ∈ rest, 1 at hsumPoint
    rw [Finset.sum_add_distrib] at hsumPoint
    simp at hsumPoint
    omega
  have hdefectNe : (∑ u ∈ rest, (1 - m u)) ≠ 0 := by omega
  obtain ⟨missing, hmissingMem, hmissingPos⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hdefectNe
  have hmissingNe : missing ≠ duplicate := (Finset.mem_erase.mp hmissingMem).1
  have hmissing : m missing = 0 := by
    have hmle := hotherLe missing hmissingNe
    omega
  refine ⟨duplicate, missing, hmissingNe.symm, ?_⟩
  intro u
  by_cases hud : u = duplicate
  · subst u
    simp [hdup]
  by_cases hum : u = missing
  · subst u
    simp [hud, hmissing]
  simp only [hud, hum, if_false]
  have humem : u ∈ rest := by simp [rest, hud]
  have hdefectZero : 1 - m u = 0 := by
    have hsplit := Finset.sum_erase_add rest (fun v => 1 - m v) hmissingMem
    rw [hdefectSum, hmissing] at hsplit
    have hrestZero : (∑ v ∈ rest.erase missing, (1 - m v)) = 0 := by
      simpa using hsplit
    have humem' : u ∈ rest.erase missing := by simp [humem, hum]
    have hle : 1 - m u ≤ ∑ v ∈ rest.erase missing, (1 - m v) :=
      Finset.single_le_sum
        (s := rest.erase missing) (f := fun v => 1 - m v)
        (fun _ _ => Nat.zero_le _) humem'
    omega
  have hmle := hotherLe u hud
  omega

/-- A cyclic source row with exactly one target-fiber collision has a unique
single-duplicate/single-missing profile, and the displacement between those
two exceptional fibers is prescribed by its source difference. -/
theorem exists_singleDuplicateMissing_displacement_of_collision_eq_one
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hcollision :
      (∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u).choose 2) = 1) :
    ∃ duplicate missing : sizeTwoAllowedDifference q a,
      duplicate ≠ missing ∧
      (∀ u : sizeTwoAllowedDifference q a,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
          if u = duplicate then 2 else if u = missing then 0 else 1) ∧
      duplicate.1 - missing.1 =
        2 * (t.1 + 1) -
          (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1) := by
  classical
  let m := fun u : sizeTwoAllowedDifference q a =>
    sizeTwoCyclicTargetDifferenceMultiplicity code x t u
  have hmass : (∑ u : sizeTwoAllowedDifference q a, m u) =
      Fintype.card (sizeTwoAllowedDifference q a) := by
    rw [sizeTwoCyclicTargetDifferenceMultiplicity_sum]
    rw [sizeTwoAdmissibleTargetRow_card q t.1 hq1,
      sizeTwoAllowedDifference_card q a ha]
  obtain ⟨duplicate, missing, hne, hprofile⟩ :=
    exists_singleDuplicateMissing_of_sum_choose_two_eq_one m hmass hcollision
  refine ⟨duplicate, missing, hne, hprofile, ?_⟩
  exact sizeTwoCyclic_singleDuplicateMissing_displacement
    hq ha code x t duplicate missing hne hprofile

end

end Erdos85

#print axioms Erdos85.exists_singleDuplicateMissing_of_sum_choose_two_eq_one
#print axioms
  Erdos85.exists_singleDuplicateMissing_displacement_of_collision_eq_one
