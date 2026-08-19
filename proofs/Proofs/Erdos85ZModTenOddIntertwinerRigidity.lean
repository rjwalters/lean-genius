import Proofs.Erdos85ZModTenSymmetricOddTwoSupport
import Proofs.Erdos85EvenCycleOrientation

/-!
# Odd-checkerboard rigidity for C10 self-intertwiners

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The possible reverse-circulant phase on the odd checkerboard is incompatible
with vanishing on every ambient-cycle edge.  Hence an odd row degree of two
forces genuine circulant dependence, and the support is `{±3}`.
-/

namespace Erdos85

/-- The odd residue class in `ZMod 10`, written explicitly for finite
classification. -/
def ZModTenOddOffset (z : ZMod 10) : Prop :=
  z = 1 ∨ z = 3 ∨ z = 5 ∨ z = 7 ∨ z = 9

instance (z : ZMod 10) : Decidable (ZModTenOddOffset z) := by
  unfold ZModTenOddOffset
  infer_instance

/-- A loopless symmetric binary C10 self-intertwiner, zero on the two cycle
offsets and of odd-checkerboard row degree two, has odd support exactly
`{±3}`.  In particular the reverse-circulant/Hankel phase cannot occur. -/
theorem zmodTen_selfIntertwiner_odd_degreeTwo_offset_three
    (H : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hcycle : ∀ x, H x (x + 1) = 0 ∧ H x (x - 1) = 0)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenOddOffset (y - x) ∧ H x y = 1).card = 2) :
    ∀ x y, ZModTenOddOffset (y - x) →
      (H x y = 1 ↔ y - x = 3 ∨ y - x = 7) := by
  classical
  have h2r : 2 ∣ 10 := by omega
  let φ : ZMod 10 →+* ZMod 2 :=
    ZMod.castHom (show 2 ∣ 10 from ⟨5, rfl⟩) (ZMod 2)
  have hodd_iff (z : ZMod 10) : ZModTenOddOffset z ↔ φ z ≠ 0 := by
    fin_cases z <;> decide
  have hodd_sum_repr : ∀ z : ZMod 10, ZModTenOddOffset z →
      ∃ w : ZMod 10, z = (w + 1) + w := by
    decide
  have htrans : ∀ x y, H (x + 1) (y + 1) = H x y := by
    by_contra hn
    push Not at hn
    obtain ⟨a, b, hab⟩ := hn
    have hrev : ∀ {x y x' y' : ZMod 10},
        φ (y - x) ≠ 0 → y + x = y' + x' → H x y = H x' y' :=
      binary_evenCycleIntertwiner_reverse_on_odd_checkerboard
        h2r H hinter hbinary hdiag (sub_ne_zero.mpr hab)
    have hzeroOdd : ∀ x y, ZModTenOddOffset (y - x) → H x y = 0 := by
      intro x y hodd
      obtain ⟨w, hw⟩ := hodd_sum_repr (y + x) (by
        apply (hodd_iff (y + x)).2
        have hp := (hodd_iff (y - x)).1 hodd
        intro hz
        apply hp
        change φ (y - x) = 0
        rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
        rw [map_add] at hz
        simpa [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using hz)
      calc
        H x y = H w (w + 1) := hrev ((hodd_iff _).1 hodd) hw
        _ = 0 := (hcycle w).1
    have hc := hdegree 0
    have hempty : ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenOddOffset (y - 0) ∧ H 0 y = 1) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hodd, hone⟩
        rw [hzeroOdd 0 y hodd] at hone
        norm_num at hone
      · intro hy
        simp at hy
    rw [hempty] at hc
    simp at hc
  have hdiff : ∀ {x y x' y' : ZMod 10},
      y - x = y' - x' → H x y = H x' y' := by
    intro x y x' y' hsub
    let t : ZMod 10 := x' - x
    have hiter : ∀ n : ℕ,
        H (x + (n : ZMod 10)) (y + (n : ZMod 10)) = H x y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          simp only [Nat.cast_add, Nat.cast_one]
          rw [show x + ((n : ZMod 10) + 1) = x + (n : ZMod 10) + 1 by ring,
            show y + ((n : ZMod 10) + 1) = y + (n : ZMod 10) + 1 by ring,
            htrans, ih]
    have ht := hiter t.val
    rw [ZMod.natCast_zmod_val] at ht
    have hx : x + t = x' := by dsimp only [t]; ring
    have hy : y + t = y' := by
      dsimp only [t]
      rw [sub_eq_sub_iff_add_eq_add] at hsub
      linear_combination hsub
    rw [hx, hy] at ht
    exact ht.symm
  let f : ZMod 10 → Bool := fun z => decide (ZModTenOddOffset z ∧ H 0 z = 1)
  have hneg : ∀ z, f (-z) = f z := by
    intro z
    apply Bool.eq_iff_iff.mpr
    simp only [f, decide_eq_true_eq]
    have hoddNeg : ZModTenOddOffset (-z) ↔ ZModTenOddOffset z := by
      revert z
      decide
    constructor
    · rintro ⟨ho, hz⟩
      refine ⟨hoddNeg.mp ho, ?_⟩
      calc
        H 0 z = H (-z) 0 := (hdiff (by ring)).symm
        _ = H 0 (-z) := hsymm _ _
        _ = 1 := hz
    · rintro ⟨ho, hz⟩
      refine ⟨hoddNeg.mpr ho, ?_⟩
      calc
        H 0 (-z) = H (-z) 0 := hsymm _ _
        _ = H 0 z := hdiff (by ring)
        _ = 1 := hz
  have hcard : ((Finset.univ : Finset (ZMod 10)).filter fun z => f z).card = 2 := by
    simpa [f] using hdegree 0
  have hallowed : ∀ z, f z = true → z = 3 ∨ z = 5 ∨ z = 7 := by
    intro z hz
    have hz' : ZModTenOddOffset z ∧ H 0 z = 1 := by simpa [f] using hz
    rcases hz'.1 with h1 | h3 | h5 | h7 | h9
    · subst z
      have hc1 := (hcycle 0).1
      norm_num at hc1
      rw [hc1] at hz'
      norm_num at hz'
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h7)
    · subst z
      have hm : (9 : ZMod 10) = 0 - 1 := by decide
      rw [hm, (hcycle 0).2] at hz'
      norm_num at hz'
  have hf := zmodTen_symmetric_odd_two_support_eq_three_seven
    f hneg hcard hallowed
  intro x y hodd
  have hxy0 : H x y = H 0 (y - x) := hdiff (by ring)
  have hf' := hf (y - x)
  simp only [f, decide_eq_true_eq] at hf'
  rw [hxy0]
  simpa [hodd] using hf'

end Erdos85

#print axioms Erdos85.zmodTen_selfIntertwiner_odd_degreeTwo_offset_three
