import Proofs.Erdos85MinimumDefectCutLowSet

/-!
# Coupling the two low sets across a two-pole separator

Adding the two sharp occupancy profiles over complementary shores recovers
the two omitted pole columns.  This is the Boolean indicator identity (27)
in the NONBIP-CONNECTED two-separator argument.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Quotients of two `q-1` residue shores exhausting `q²-2` vertices add
to `q-2`; after restoring their two upper levels, the centers add to `q`. -/
theorem twoSeparator_quotient_add_two_eq
    (q s t : ℕ) (hq : 2 ≤ q)
    (hsum : s + t = q * q - 2)
    (hsmod : s % q = q - 1) (htmod : t % q = q - 1) :
    s / q + t / q + 2 = q := by
  have hsdecomp := (Nat.div_add_mod s q).symm
  have htdecomp := (Nat.div_add_mod t q).symm
  rw [hsmod] at hsdecomp
  rw [htmod] at htdecomp
  have hqone : 1 ≤ q := by omega
  have htwo : 2 ≤ q * q := by nlinarith
  have hqpred : q - 1 + 1 = q := Nat.sub_add_cancel hqone
  have hmul : q * (s / q + t / q + 2) = q * q := by
    calc
      q * (s / q + t / q + 2) =
          (q * (s / q) + (q - 1)) +
            (q * (t / q) + (q - 1)) + 2 := by
        rw [mul_add, mul_add]
        omega
      _ = s + t + 2 := by rw [← hsdecomp, ← htdecomp]
      _ = q * q := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

/-- Pointwise coupling of the two balanced low sets with the two pole
neighborhood indicators. -/
theorem twoSeparator_lowSet_indicator_coupling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S T Z₁ Z₂ : Finset V) (x y : V) (hxy : x ≠ y)
    (hcover : S ∪ T ∪ ({x, y} : Finset V) = Finset.univ)
    (hST : Disjoint S T)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∉ T) (hyT : y ∉ T)
    (hq : 2 ≤ q)
    (hcards : S.card + T.card = q * q - 2)
    (hSmod : S.card % q = q - 1) (hTmod : T.card % q = q - 1)
    (hZ₁ : ∀ v, (v ∈ Z₁ ∧
        (G.neighborFinset v ∩ S).card = S.card / q) ∨
      (v ∉ Z₁ ∧
        (G.neighborFinset v ∩ S).card = S.card / q + 1))
    (hZ₂ : ∀ v, (v ∈ Z₂ ∧
        (G.neighborFinset v ∩ T).card = T.card / q) ∨
      (v ∉ Z₂ ∧
        (G.neighborFinset v ∩ T).card = T.card / q + 1)) :
    ∀ v,
      (if v ∈ Z₁ then 1 else 0) + (if v ∈ Z₂ then 1 else 0) =
        (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0) := by
  have hcenter : S.card / q + T.card / q + 2 = q :=
    twoSeparator_quotient_add_two_eq q S.card T.card hq
      hcards hSmod hTmod
  intro v
  let N := G.neighborFinset v
  have hSW : Disjoint S ({x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    intro z hzS hzW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzW
    rcases hzW with rfl | rfl
    · exact hxS hzS
    · exact hyS hzS
  have hTW : Disjoint T ({x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    intro z hzT hzW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzW
    rcases hzW with rfl | rfl
    · exact hxT hzT
    · exact hyT hzT
  have hpart : N = ((N ∩ S) ∪ (N ∩ T)) ∪
      (N ∩ ({x, y} : Finset V)) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hz
      have hzU : z ∈ S ∪ T ∪ ({x, y} : Finset V) := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hzU with hzST | hzW
      · rcases Finset.mem_union.mp hzST with hzS | hzT
        · exact Or.inl (Or.inl ⟨hz, hzS⟩)
        · exact Or.inl (Or.inr ⟨hz, hzT⟩)
      · exact Or.inr ⟨hz, hzW⟩
    · rintro (⟨⟨hz, _⟩ | ⟨hz, _⟩⟩ | ⟨hz, _⟩) <;> exact hz
  have hdisjST : Disjoint (N ∩ S) (N ∩ T) :=
    hST.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdisjW : Disjoint ((N ∩ S) ∪ (N ∩ T))
      (N ∩ ({x, y} : Finset V)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨
      hSW.mono Finset.inter_subset_right Finset.inter_subset_right,
      hTW.mono Finset.inter_subset_right Finset.inter_subset_right⟩
  have hdegree := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hdisjW,
    Finset.card_union_of_disjoint hdisjST,
    G.card_neighborFinset_eq_degree, hreg v] at hdegree
  have hpair : (N ∩ ({x, y} : Finset V)).card =
      (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0) := by
    by_cases hvx : G.Adj v x <;> by_cases hvy : G.Adj v y <;>
      simp [N, SimpleGraph.mem_neighborFinset, hvx, hvy, hxy]
  have hoccS : (N ∩ S).card + (if v ∈ Z₁ then 1 else 0) =
      S.card / q + 1 := by
    rcases hZ₁ v with ⟨hv, hf⟩ | ⟨hv, hf⟩ <;> simp [hv, N, hf]
  have hoccT : (N ∩ T).card + (if v ∈ Z₂ then 1 else 0) =
      T.card / q + 1 := by
    rcases hZ₂ v with ⟨hv, hf⟩ | ⟨hv, hf⟩ <;> simp [hv, N, hf]
  rw [hpair] at hdegree
  omega

#print axioms twoSeparator_quotient_add_two_eq
#print axioms twoSeparator_lowSet_indicator_coupling

end

end Erdos85
