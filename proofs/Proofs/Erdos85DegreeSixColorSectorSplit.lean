import Proofs.Erdos85ColorSectorPSD
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85DegreeSixTriangleClosure
import Proofs.Erdos85OrientedMassBounds
import Proofs.Erdos85EvenCycleOrientation
import Proofs.Erdos85ZModProjectionFiber
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The degree-six color-sector split

This file connects the component-indexed color sector used by the PSD
argument to the vertex-indexed colored order used by the cubic trace.  The
key point is that triangle-free defect degree two propagates along every
edge, hence throughout every connected component of the second-order defect
graph.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Weighted Cauchy--Schwarz in the exact numerical form needed for the
unique degree-six triangle-free component.  This is stated for an abstract
balanced quotient so the analytic step is independent of graph plumbing. -/
theorem degreeSix_singleton_incidence_cauchy
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hpos : 0 < size c)
    (htotal : (∑ e : C, size e) = 33)
    (hrow : (∑ e : C, Q c e) = 6)
    (hdiag : Q c c = 2)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hsq : (∑ e : C, Q c e * Q e c) = size c + 3) :
    size c * size c + 33 ≤ 18 * size c := by
  let S : Finset C := Finset.univ.erase c
  have hc : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have hsizeS : (∑ e ∈ S, size e) = 33 - size c := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset C) size hc
    dsimp [S]
    omega
  have hrowS : (∑ e ∈ S, Q c e) = 4 := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset C) (fun e => Q c e) hc
    dsimp [S]
    omega
  have hprodS : (∑ e ∈ S, Q c e * Q e c) = size c - 1 := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset C) (fun e => Q c e * Q e c) hc
    rw [hdiag] at hsplit
    dsimp [S]
    omega
  have hl : (size c : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) S
    (r := fun e => (Q c e : ℝ))
    (f := fun e => (size e : ℝ))
    (g := fun e => ((Q c e * Q e c : ℕ) : ℝ) / (size c : ℝ))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (by
      intro e he
      have hb := hbal e
      have hbR : (size c : ℝ) * (Q c e : ℝ) =
          (size e : ℝ) * (Q e c : ℝ) := by exact_mod_cast hb
      apply le_of_eq
      rw [← mul_div_assoc]
      apply (eq_div_iff hl).2
      push_cast
      calc
        (Q c e : ℝ) ^ 2 * size c =
            (Q c e : ℝ) * ((size c : ℝ) * Q c e) := by ring
        _ = (Q c e : ℝ) * ((size e : ℝ) * Q e c) := by rw [hbR]
        _ = (size e : ℝ) * ((Q c e : ℝ) * Q e c) := by ring)
  have hsizeR : (∑ e ∈ S, (size e : ℝ)) = (33 - size c : ℕ) := by
    exact_mod_cast hsizeS
  have hrowR : (∑ e ∈ S, (Q c e : ℝ)) = 4 := by
    exact_mod_cast hrowS
  have hprodR :
      (∑ e ∈ S, (((Q c e * Q e c : ℕ) : ℝ) / (size c : ℝ))) =
        ((size c - 1 : ℕ) : ℝ) / (size c : ℝ) := by
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hprodS
  rw [hsizeR, hrowR, hprodR] at hcs
  have hlR : (0 : ℝ) < size c := by exact_mod_cast hpos
  have hle33 : size c ≤ 33 := by
    have : size c ≤ ∑ e : C, size e := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc
    omega
  have hsub33 : ((33 - size c : ℕ) : ℝ) = 33 - (size c : ℝ) := by
    rw [Nat.cast_sub hle33]
    norm_num
  have hsub1 : ((size c - 1 : ℕ) : ℝ) = (size c : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]
    norm_num
  norm_num [pow_two] at hcs
  rw [hsub33, hsub1] at hcs
  have hcs' := mul_le_mul_of_nonneg_right hcs hlR.le
  have hcs'' : 16 * (size c : ℝ) ≤
      (33 - (size c : ℝ)) * ((size c : ℝ) - 1) := by
    calc
      16 * (size c : ℝ) ≤
          ((33 - (size c : ℝ)) * (((size c : ℝ) - 1) / size c)) * size c :=
        hcs'
      _ = (33 - (size c : ℝ)) * ((size c : ℝ) - 1) := by
        field_simp [hl]
  exact_mod_cast (show ((size c : ℝ) * size c + 33 ≤ 18 * size c) by
    nlinarith [hcs''])

/-- The order-six singleton row has a forced asymmetric contact: one unit
leaves the order-six component and two units return from an order-three
component. -/
theorem degreeSix_orderSix_singleton_contact
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hsize : size c = 6)
    (hrow : (∑ e ∈ (Finset.univ.erase c), Q c e) = 4)
    (hprod : (∑ e ∈ (Finset.univ.erase c), Q c e * Q e c) = 5)
    (hbal : ∀ e, size c * Q c e = size e * Q e c) :
    ∃ e : C, e ≠ c ∧ size e = 3 ∧ Q c e = 1 ∧ Q e c = 2 := by
  let S : Finset C := Finset.univ.erase c
  let f : C → ℕ := fun e ↦ Q c e * (Q e c - 1)
  have hdecomp : ∀ e ∈ S, Q c e * Q e c = Q c e + f e := by
    intro e he
    by_cases hq : Q c e = 0
    · simp [f, hq]
    · have hr : 0 < Q e c := by
        by_contra hr0
        push Not at hr0
        have hrz : Q e c = 0 := by omega
        have hb := hbal e
        rw [hsize, hrz, mul_zero] at hb
        have : Q c e = 0 := by omega
        exact hq this
      calc
        Q c e * Q e c = Q c e * ((Q e c - 1) + 1) := by
          rw [Nat.sub_add_cancel hr]
        _ = Q c e + f e := by simp [f, Nat.mul_add, Nat.add_comm]
  have hfsum : (∑ e ∈ S, f e) = 1 := by
    have hrowS : (∑ e ∈ S, Q c e) = 4 := by simpa [S] using hrow
    have hsum : 5 = 4 + ∑ e ∈ S, f e := by
      calc
        5 = ∑ e ∈ S, Q c e * Q e c := hprod.symm
        _ = ∑ e ∈ S, (Q c e + f e) := Finset.sum_congr rfl hdecomp
        _ = (∑ e ∈ S, Q c e) + ∑ e ∈ S, f e := by
          rw [Finset.sum_add_distrib]
        _ = 4 + ∑ e ∈ S, f e := by rw [hrowS]
    omega
  have hfne : (∑ e ∈ S, f e) ≠ 0 := by omega
  obtain ⟨e, heS, hene⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfne
  have hfle : f e ≤ ∑ x ∈ S, f x :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) heS
  have hfe : f e = 1 := by omega
  have hmul : Q c e * (Q e c - 1) = 1 := by simpa [f] using hfe
  have hq : Q c e = 1 :=
    Nat.dvd_one.mp ⟨Q e c - 1, hmul.symm⟩
  have hrsub : Q e c - 1 = 1 :=
    Nat.dvd_one.mp ⟨Q c e, by simpa [Nat.mul_comm] using hmul.symm⟩
  have hr : Q e c = 2 := by omega
  have hb := hbal e
  rw [hsize, hq, hr] at hb
  have hse : size e = 3 := by omega
  exact ⟨e, (Finset.mem_erase.mp heS).1, hse, hq, hr⟩

/-- An order-fifteen singleton row necessarily contacts an order-three
component.  Periodicity bounds every entry toward a target whose order is
not divisible by fifteen by one; without an order-three target, balance
would make every reverse entry at most three, contradicting the pinned
two-step row sum `14 > 3 * 4`. -/
theorem degreeSix_orderFifteen_singleton_contact
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hsize : size c = 15)
    (htotal : (∑ e : C, size e) = 33)
    (hlower : ∀ e, 3 ≤ size e)
    (hrow : (∑ e ∈ (Finset.univ.erase c), Q c e) = 4)
    (hprod : (∑ e ∈ (Finset.univ.erase c), Q c e * Q e c) = 14)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hperiod : ∀ e, ¬ 15 ∣ size e → Q c e ≤ 1) :
    ∃ e : C, e ≠ c ∧ size e = 3 ∧ Q c e = 1 ∧ Q e c = 5 := by
  let S : Finset C := Finset.univ.erase c
  by_contra hnone
  push Not at hnone
  have hterm : ∀ e ∈ S, Q c e * Q e c ≤ 3 * Q c e := by
    intro e heS
    have hec : e ≠ c := (Finset.mem_erase.mp heS).1
    have hqle : Q c e ≤ 4 := by
      have hsingle : Q c e ≤ ∑ x ∈ S, Q c x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) heS
      simpa [S, hrow] using hsingle
    have hple : Q c e * Q e c ≤ 14 := by
      have hsingle : Q c e * Q e c ≤
        ∑ x ∈ S, Q c x * Q x c :=
        Finset.single_le_sum
          (fun x (_ : x ∈ S) ↦ Nat.zero_le (Q c x * Q x c)) heS
      simpa [S, hprod] using hsingle
    by_cases hqzero : Q c e = 0
    · simp [hqzero]
    · have hqpos : 0 < Q c e := Nat.pos_of_ne_zero hqzero
      have hsizele : size e ≤ 18 := by
        have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
        have heMem : e ∈ (Finset.univ.erase c : Finset C) := heS
        have hsplitc := Finset.sum_erase_add
          (Finset.univ : Finset C) size hcMem
        have hsplite := Finset.sum_erase_add
          (Finset.univ.erase c : Finset C) size heMem
        have hrest : 0 ≤ ∑ x ∈ (Finset.univ.erase c).erase e, size x :=
          Nat.zero_le _
        have htwo : size c + size e ≤ ∑ x : C, size x := by omega
        rw [htotal, hsize] at htwo
        omega
      by_cases hdvd : 15 ∣ size e
      · have hsizee : size e = 15 := by
          obtain ⟨k, hk⟩ := hdvd
          have hkpos : 0 < k := by
            by_contra hk0
            push Not at hk0
            have : k = 0 := by omega
            subst k
            simp at hk
            have := hlower e
            omega
          rw [hk]
          have := hlower e
          omega
        have hb := hbal e
        rw [hsize, hsizee] at hb
        have hrq : Q e c = Q c e := by omega
        rw [hrq] at hple
        have hq3 : Q c e ≤ 3 := by
          by_contra hnot
          have hq4 : Q c e = 4 := by omega
          norm_num [hq4] at hple
        rw [hrq]
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (Q c e) hq3
      · have hqone : Q c e = 1 := by
          have := hperiod e hdvd
          omega
        have hb := hbal e
        rw [hsize, hqone, mul_one] at hb
        have hsizeNe : size e ≠ 3 := by
          intro hthree
          have hreverse : Q e c = 5 := by rw [hthree] at hb; omega
          exact hnone e hec hthree hqone hreverse
        have hsize4 : 4 ≤ size e := by
          have := hlower e
          omega
        have hrle : Q e c ≤ 3 := by nlinarith
        rw [hqone]
        simpa using hrle
  have hsumle : (∑ e ∈ S, Q c e * Q e c) ≤
      ∑ e ∈ S, 3 * Q c e :=
    Finset.sum_le_sum fun e he ↦ hterm e he
  rw [← Finset.mul_sum] at hsumle
  simpa [S, hrow, hprod] using hsumle

/-- Two distinct order-three contacts cannot coexist in an order-fifteen
singleton row.  After deleting the three known components only twelve
vertices remain; weighted Cauchy contradicts the residual row/product pair,
which is `(3,9)` or `(2,4)` according as the second contact is absent or
present in the order-fifteen row. -/
theorem degreeSix_orderFifteen_two_orderThree_contacts_false
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c e f : C)
    (hce : c ≠ e) (hcf : c ≠ f) (hef : e ≠ f)
    (hc15 : size c = 15) (he3 : size e = 3) (hf3 : size f = 3)
    (htotal : (∑ t : C, size t) = 33)
    (hrowc : (∑ t ∈ (Finset.univ.erase c), Q c t) = 4)
    (hprodc : (∑ t ∈ (Finset.univ.erase c), Q c t * Q t c) = 14)
    (hrowAll : ∀ x, (∑ t, Q x t) = 6)
    (hbal : ∀ x y, size x * Q x y = size y * Q y x)
    (hQce : Q c e = 1) (hQec : Q e c = 5) : False := by
  let S : Finset C := ((Finset.univ.erase c).erase e).erase f
  have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have heMem : e ∈ (Finset.univ.erase c : Finset C) :=
    Finset.mem_erase.mpr ⟨hce.symm, Finset.mem_univ e⟩
  have hfMem : f ∈ ((Finset.univ.erase c).erase e : Finset C) :=
    Finset.mem_erase.mpr ⟨hef.symm,
      Finset.mem_erase.mpr ⟨hcf.symm, Finset.mem_univ f⟩⟩
  have hsizeC := Finset.sum_erase_add (Finset.univ : Finset C) size hcMem
  have hsizeE := Finset.sum_erase_add
    (Finset.univ.erase c : Finset C) size heMem
  have hsizeF := Finset.sum_erase_add
    ((Finset.univ.erase c).erase e : Finset C) size hfMem
  have hsizeS : (∑ t ∈ S, size t) = 12 := by
    dsimp [S]
    omega
  have hQfcle : Q f c ≤ 6 := by
    have hcU : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
    have hsingle : Q f c ≤ ∑ t : C, Q f t :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hcU
    rw [hrowAll f] at hsingle
    exact hsingle
  have hbalF := hbal c f
  rw [hc15, hf3] at hbalF
  have hQcfle : Q c f ≤ 1 := by nlinarith
  have hQcfprodle : Q c f * Q f c ≤ 6 := by
    calc
      Q c f * Q f c ≤ 1 * 6 := Nat.mul_le_mul hQcfle hQfcle
      _ = 6 := by norm_num
  have hrowC := Finset.sum_erase_add
    (Finset.univ.erase c : Finset C) (Q c) heMem
  have hrowF := Finset.sum_erase_add
    ((Finset.univ.erase c).erase e : Finset C) (Q c) hfMem
  have hprodC := Finset.sum_erase_add
    (Finset.univ.erase c : Finset C) (fun t ↦ Q c t * Q t c) heMem
  have hprodF := Finset.sum_erase_add
    ((Finset.univ.erase c).erase e : Finset C)
      (fun t ↦ Q c t * Q t c) hfMem
  rw [hQce] at hrowC
  rw [hQce, hQec] at hprodC
  have hrowS : (∑ t ∈ S, Q c t) = 3 - Q c f := by
    dsimp [S]
    omega
  have hprodS : (∑ t ∈ S, Q c t * Q t c) =
      9 - Q c f * Q f c := by
    dsimp [S]
    omega
  have hcR : (15 : ℝ) ≠ 0 := by norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) S
    (r := fun t => (Q c t : ℝ))
    (f := fun t => (size t : ℝ))
    (g := fun t => ((Q c t * Q t c : ℕ) : ℝ) / 15)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (by
      intro t ht
      have hb := hbal c t
      rw [hc15] at hb
      have hbR : (15 : ℝ) * (Q c t : ℝ) =
          (size t : ℝ) * (Q t c : ℝ) := by exact_mod_cast hb
      apply le_of_eq
      rw [← mul_div_assoc]
      apply (eq_div_iff hcR).2
      push_cast
      calc
        (Q c t : ℝ) ^ 2 * 15 =
            (Q c t : ℝ) * ((15 : ℝ) * Q c t) := by ring
        _ = (Q c t : ℝ) * ((size t : ℝ) * Q t c) := by rw [hbR]
        _ = (size t : ℝ) * ((Q c t : ℝ) * Q t c) := by ring)
  have hsizeR : (∑ t ∈ S, (size t : ℝ)) = 12 := by
    exact_mod_cast hsizeS
  have hrowR : (∑ t ∈ S, (Q c t : ℝ)) = (3 - Q c f : ℕ) := by
    exact_mod_cast hrowS
  have hprodR :
      (∑ t ∈ S, (((Q c t * Q t c : ℕ) : ℝ) / 15)) =
        ((9 - Q c f * Q f c : ℕ) : ℝ) / 15 := by
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hprodS
  rw [hsizeR, hrowR, hprodR] at hcs
  rcases Nat.eq_zero_or_pos (Q c f) with hzero | hpos
  · rw [hzero] at hcs
    norm_num at hcs
  · have hone : Q c f = 1 := by omega
    have hfive : Q f c = 5 := by omega
    rw [hone, hfive] at hcs
    norm_num at hcs

/-- The pinned order-nine row has only three possible sources of its excess:
an order-three contact, a single order-eighteen target consuming all four row
units, or two distinct order-nine double contacts. -/
theorem degreeSix_orderNine_singleton_contact_trichotomy
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hsize : size c = 9)
    (htotal : (∑ e : C, size e) = 33)
    (hlower : ∀ e, 3 ≤ size e)
    (hrow : (∑ e ∈ (Finset.univ.erase c), Q c e) = 4)
    (hprod : (∑ e ∈ (Finset.univ.erase c), Q c e * Q e c) = 8)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hperiod : ∀ e, ¬ 9 ∣ size e → Q c e ≤ 1) :
    (∃ e, e ≠ c ∧ size e = 3 ∧ Q c e = 1 ∧ Q e c = 3) ∨
    (∃ e, e ≠ c ∧ size e = 18 ∧ Q c e = 4 ∧ Q e c = 2) ∨
    (∃ e f, e ≠ c ∧ f ≠ c ∧ e ≠ f ∧
      size e = 9 ∧ size f = 9 ∧
      Q c e = 2 ∧ Q e c = 2 ∧ Q c f = 2 ∧ Q f c = 2) := by
  let S : Finset C := Finset.univ.erase c
  by_contra hnone
  push Not at hnone
  have hclass : ∀ e ∈ S, 0 < Q c e →
      (size e = 9 ∧ Q c e = 1 ∧ Q e c = 1) ∨
      (size e = 9 ∧ Q c e = 2 ∧ Q e c = 2) ∨
      (size e = 18 ∧ Q c e = 2 ∧ Q e c = 1) := by
    intro e heS hqpos
    have hec : e ≠ c := (Finset.mem_erase.mp heS).1
    have hqle : Q c e ≤ 4 := by
      have hsingle : Q c e ≤ ∑ x ∈ S, Q c x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) heS
      simpa [S, hrow] using hsingle
    have hple : Q c e * Q e c ≤ 8 := by
      have hsingle : Q c e * Q e c ≤ ∑ x ∈ S, Q c x * Q x c :=
        Finset.single_le_sum
          (fun x (_ : x ∈ S) ↦ Nat.zero_le (Q c x * Q x c)) heS
      simpa [S, hprod] using hsingle
    have hsizele : size e ≤ 24 := by
      have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset C) size hcMem
      have heSingle : size e ≤ ∑ x ∈ Finset.univ.erase c, size x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) heS
      rw [htotal, hsize] at hsplit
      omega
    have hb := hbal e
    rw [hsize] at hb
    by_cases hdvd : 9 ∣ size e
    · obtain ⟨k, hk⟩ := hdvd
      have hkpos : 0 < k := by
        by_contra hk0
        push Not at hk0
        have hkz : k = 0 := by omega
        subst k
        simp at hk
        have := hlower e
        omega
      have hke : k = 1 ∨ k = 2 := by
        rw [hk] at hsizele
        omega
      rcases hke with rfl | rfl
      · have hse : size e = 9 := by omega
        rw [hse] at hb
        have hrq : Q e c = Q c e := by omega
        rw [hrq] at hple
        have hq2 : Q c e ≤ 2 := by
          by_contra hnot
          have hqge : 3 ≤ Q c e := by omega
          nlinarith
        have hqcases : Q c e = 1 ∨ Q c e = 2 := by omega
        rcases hqcases with hq | hq
        · exact Or.inl ⟨hse, hq, by omega⟩
        · exact Or.inr (Or.inl ⟨hse, hq, by omega⟩)
      · have hse : size e = 18 := by omega
        rw [hse] at hb
        have hqeven : Q c e = 2 * Q e c := by omega
        have hqcases : Q c e = 2 ∨ Q c e = 4 := by
          have hrpos : 0 < Q e c := by nlinarith
          omega
        rcases hqcases with hq | hq
        · exact Or.inr (Or.inr ⟨hse, hq, by omega⟩)
        · exfalso
          exact hnone.2.1 e hec hse hq (by omega)
    · have hqone : Q c e = 1 := by
        have := hperiod e hdvd
        omega
      rw [hqone, mul_one] at hb
      have hrpos : 0 < Q e c := by nlinarith
      have hsizeNe : size e ≠ 3 := by
        intro hthree
        have hr : Q e c = 3 := by rw [hthree] at hb; omega
        exact hnone.1 e hec hthree hqone hr
      have hsize4 : 4 ≤ size e := by
        have := hlower e
        omega
      have hrle : Q e c ≤ 2 := by nlinarith
      have hrcases : Q e c = 1 ∨ Q e c = 2 := by omega
      rcases hrcases with hr | hr
      · rw [hr] at hb
        have hse : size e = 9 := by omega
        exact (hdvd (by rw [hse])).elim
      · rw [hr] at hb
        omega
  let excess : C → ℕ := fun e ↦ Q c e * (Q e c - 1)
  have hdecomp : ∀ e ∈ S, Q c e * Q e c = Q c e + excess e := by
    intro e heS
    by_cases hq : Q c e = 0
    · simp [excess, hq]
    · have hcl := hclass e heS (Nat.pos_of_ne_zero hq)
      rcases hcl with hcl | hcl | hcl <;> rcases hcl with ⟨_, hqv, hrv⟩ <;>
        simp [excess, hqv, hrv]
  have hexcessSum : (∑ e ∈ S, excess e) = 4 := by
    have hsum : 8 = 4 + ∑ e ∈ S, excess e := by
      calc
        8 = ∑ e ∈ S, Q c e * Q e c := by simpa [S] using hprod.symm
        _ = ∑ e ∈ S, (Q c e + excess e) := Finset.sum_congr rfl hdecomp
        _ = (∑ e ∈ S, Q c e) + ∑ e ∈ S, excess e := by
          rw [Finset.sum_add_distrib]
        _ = 4 + ∑ e ∈ S, excess e := by simpa [S] using hrow
    omega
  have hexcessNe : (∑ e ∈ S, excess e) ≠ 0 := by omega
  obtain ⟨e, heS, heNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hexcessNe
  have heclass := hclass e heS (by
    by_contra hq0
    push Not at hq0
    have : Q c e = 0 := by omega
    simp [excess, this] at heNe)
  have heDouble : size e = 9 ∧ Q c e = 2 ∧ Q e c = 2 := by
    rcases heclass with h | h | h
    · rcases h with ⟨_, hq, hr⟩
      simp [excess, hq, hr] at heNe
    · exact h
    · rcases h with ⟨_, hq, hr⟩
      simp [excess, hq, hr] at heNe
  have hec : e ≠ c := (Finset.mem_erase.mp heS).1
  have hother : ∀ f ∈ S, f ≠ e → excess f = 0 := by
    intro f hfS hfe
    by_cases hq : Q c f = 0
    · simp [excess, hq]
    · have hfclass := hclass f hfS (Nat.pos_of_ne_zero hq)
      rcases hfclass with h | h | h
      · rcases h with ⟨_, hqv, hrv⟩
        simp [excess, hqv, hrv]
      · rcases h with ⟨hsf, hqf, hrf⟩
        have hfc : f ≠ c := (Finset.mem_erase.mp hfS).1
        exact (hnone.2.2 e f hec hfc hfe.symm heDouble.1 hsf
          heDouble.2.1 heDouble.2.2 hqf hrf).elim
      · rcases h with ⟨_, hqv, hrv⟩
        simp [excess, hqv, hrv]
  have hsumSingle : (∑ f ∈ S, excess f) = excess e := by
    exact Finset.sum_eq_single e (fun f hfS hfe ↦ hother f hfS hfe)
      (fun heNot ↦ (heNot heS).elim)
  rw [hexcessSum] at hsumSingle
  simp [excess, heDouble.2.1, heDouble.2.2] at hsumSingle

/-- Two order-three targets occupy the same nonzero target-length residue in
an order-nine source row, so cycle-block periodicity bounds their combined
quotient multiplicity by one. -/
theorem degreeSix_orderNine_two_orderThree_targets_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc9 : c.supp.ncard = 9) (he3 : e.supp.ncard = 3)
    (hf3 : f.supp.ncard = 3) (hef : e ≠ f) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e +
      componentQuotientMatrix G (secondOrderDefectGraph G) c f ≤ 1 := by
  let D := secondOrderDefectGraph G
  let es : Finset D.ConnectedComponent := {e, f}
  have hs : (3 : ZMod c.supp.ncard) ≠ 0 := by
    intro hz
    have hdvd : c.supp.ncard ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 c.supp.ncard).mp hz
    rw [hc9] at hdvd
    norm_num at hdvd
  have hbound := sum_componentQuotientMatrix_le_one_of_periodic
    G D hfree c (u c) (hu c) (huRange c) (3 : ZMod c.supp.ncard) hs es
  have hperiod : ∀ t ∈ es, ∀ z y,
      D.connectedComponentMk y = t →
        (G.Adj (u c (z + 3)) y ↔ G.Adj (u c z) y) := by
    intro t ht z y hy
    have hyrange : y ∈ Set.range (u t) := by
      rw [huRange t]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff t y).mpr hy
    obtain ⟨j, rfl⟩ := hyrange
    have hc3 : 3 ≤ c.supp.ncard := by rw [hc9]; norm_num
    have ht3 : t.supp.ncard = 3 := by
      simp only [es, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact he3
      · exact hf3
    have htc3 : 3 ≤ t.supp.ncard := by rw [ht3]
    have hupair : ∀ a : ZMod c.supp.ncard,
        u c (a - 1) ≠ u c (a + 1) := by
      intro a
      exact (hu c).ne (zmod_sub_one_ne_add_one_of_three_le hc3 a)
    have hvpair : ∀ b : ZMod t.supp.ncard,
        u t (b - 1) ≠ u t (b + 1) := by
      intro b
      exact (hu t).ne (zmod_sub_one_ne_add_one_of_three_le htc3 b)
    have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D
      (u c) (u t) (1 : ZMod c.supp.ncard) (1 : ZMod t.supp.ncard)
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard))
      (huD c) (huD t) hupair hvpair
    have hp := adj_iff_add_targetOrder_of_entry_cycleIntertwine
      G (u c) (u t) (1 : ZMod c.supp.ncard)
        (1 : ZMod t.supp.ncard) hinter z j
    simp only [ZMod.addOrderOf_one, ht3, nsmul_eq_mul, mul_one] at hp
    have hcast : ((3 : ℕ) : ZMod c.supp.ncard) = 3 := by norm_num
    rw [hcast] at hp
    exact hp
  have := hbound hperiod
  simpa [D, es, hef] using this

/-- Two order-three targets occupy the same nonzero residue in an order-six
source row. -/
theorem degreeSix_orderSix_two_orderThree_targets_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc6 : c.supp.ncard = 6) (he3 : e.supp.ncard = 3)
    (hf3 : f.supp.ncard = 3) (hef : e ≠ f) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e +
      componentQuotientMatrix G (secondOrderDefectGraph G) c f ≤ 1 := by
  let D := secondOrderDefectGraph G
  let es : Finset D.ConnectedComponent := {e, f}
  have hs : (3 : ZMod c.supp.ncard) ≠ 0 := by
    intro hz
    have hdvd : c.supp.ncard ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 c.supp.ncard).mp hz
    rw [hc6] at hdvd
    norm_num at hdvd
  have hbound := sum_componentQuotientMatrix_le_one_of_periodic
    G D hfree c (u c) (hu c) (huRange c) (3 : ZMod c.supp.ncard) hs es
  have hperiod : ∀ t ∈ es, ∀ z y, D.connectedComponentMk y = t →
      (G.Adj (u c (z + 3)) y ↔ G.Adj (u c z) y) := by
    intro t ht z y hy
    have hyrange : y ∈ Set.range (u t) := by
      rw [huRange t]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff t y).mpr hy
    obtain ⟨j, rfl⟩ := hyrange
    have hc3 : 3 ≤ c.supp.ncard := by rw [hc6]; norm_num
    have ht3 : t.supp.ncard = 3 := by
      simp only [es, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact he3
      · exact hf3
    have htc3 : 3 ≤ t.supp.ncard := by rw [ht3]
    have hupair : ∀ a : ZMod c.supp.ncard, u c (a - 1) ≠ u c (a + 1) := by
      intro a
      exact (hu c).ne (zmod_sub_one_ne_add_one_of_three_le hc3 a)
    have hvpair : ∀ b : ZMod t.supp.ncard, u t (b - 1) ≠ u t (b + 1) := by
      intro b
      exact (hu t).ne (zmod_sub_one_ne_add_one_of_three_le htc3 b)
    have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D
      (u c) (u t) (1 : ZMod c.supp.ncard) (1 : ZMod t.supp.ncard)
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard))
      (huD c) (huD t) hupair hvpair
    have hp := adj_iff_add_targetOrder_of_entry_cycleIntertwine
      G (u c) (u t) (1 : ZMod c.supp.ncard)
        (1 : ZMod t.supp.ncard) hinter z j
    simp only [ZMod.addOrderOf_one, ht3, nsmul_eq_mul, mul_one] at hp
    have hcast : ((3 : ℕ) : ZMod c.supp.ncard) = 3 := by norm_num
    rw [hcast] at hp
    exact hp
  have := hbound hperiod
  simpa [D, es, hef] using this

/-- Two order-four targets occupy the same nonzero target-length residue in
an order-twelve source row, so their combined quotient multiplicity is at
most one. -/
theorem degreeSix_orderTwelve_two_orderFour_targets_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc12 : c.supp.ncard = 12) (he4 : e.supp.ncard = 4)
    (hf4 : f.supp.ncard = 4) (hef : e ≠ f) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e +
      componentQuotientMatrix G (secondOrderDefectGraph G) c f ≤ 1 := by
  let D := secondOrderDefectGraph G
  let es : Finset D.ConnectedComponent := {e, f}
  have hs : (4 : ZMod c.supp.ncard) ≠ 0 := by
    intro hz
    have hdvd : c.supp.ncard ∣ 4 :=
      (ZMod.natCast_eq_zero_iff 4 c.supp.ncard).mp hz
    rw [hc12] at hdvd
    norm_num at hdvd
  have hbound := sum_componentQuotientMatrix_le_one_of_periodic
    G D hfree c (u c) (hu c) (huRange c) (4 : ZMod c.supp.ncard) hs es
  have hperiod : ∀ t ∈ es, ∀ z y,
      D.connectedComponentMk y = t →
        (G.Adj (u c (z + 4)) y ↔ G.Adj (u c z) y) := by
    intro t ht z y hy
    have hyrange : y ∈ Set.range (u t) := by
      rw [huRange t]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff t y).mpr hy
    obtain ⟨j, rfl⟩ := hyrange
    have hc3 : 3 ≤ c.supp.ncard := by rw [hc12]; norm_num
    have ht4 : t.supp.ncard = 4 := by
      simp only [es, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact he4
      · exact hf4
    have htc3 : 3 ≤ t.supp.ncard := by rw [ht4]; norm_num
    have hupair : ∀ a : ZMod c.supp.ncard,
        u c (a - 1) ≠ u c (a + 1) := by
      intro a
      exact (hu c).ne (zmod_sub_one_ne_add_one_of_three_le hc3 a)
    have hvpair : ∀ b : ZMod t.supp.ncard,
        u t (b - 1) ≠ u t (b + 1) := by
      intro b
      exact (hu t).ne (zmod_sub_one_ne_add_one_of_three_le htc3 b)
    have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D
      (u c) (u t) (1 : ZMod c.supp.ncard) (1 : ZMod t.supp.ncard)
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard))
      (huD c) (huD t) hupair hvpair
    have hp := adj_iff_add_targetOrder_of_entry_cycleIntertwine
      G (u c) (u t) (1 : ZMod c.supp.ncard)
        (1 : ZMod t.supp.ncard) hinter z j
    simp only [ZMod.addOrderOf_one, ht4, nsmul_eq_mul, mul_one] at hp
    have hcast : ((4 : ℕ) : ZMod c.supp.ncard) = 4 := by norm_num
    rw [hcast] at hp
    exact hp
  have := hbound hperiod
  simpa [D, es, hef] using this

/-- Two order-six targets occupy the same nonzero target-length residue in
an order-twelve source row. -/
theorem degreeSix_orderTwelve_two_orderSix_targets_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc12 : c.supp.ncard = 12) (he6 : e.supp.ncard = 6)
    (hf6 : f.supp.ncard = 6) (hef : e ≠ f) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e +
      componentQuotientMatrix G (secondOrderDefectGraph G) c f ≤ 1 := by
  let D := secondOrderDefectGraph G
  let es : Finset D.ConnectedComponent := {e, f}
  have hs : (6 : ZMod c.supp.ncard) ≠ 0 := by
    intro hz
    have hdvd : c.supp.ncard ∣ 6 :=
      (ZMod.natCast_eq_zero_iff 6 c.supp.ncard).mp hz
    rw [hc12] at hdvd
    norm_num at hdvd
  have hbound := sum_componentQuotientMatrix_le_one_of_periodic
    G D hfree c (u c) (hu c) (huRange c) (6 : ZMod c.supp.ncard) hs es
  have hperiod : ∀ t ∈ es, ∀ z y, D.connectedComponentMk y = t →
      (G.Adj (u c (z + 6)) y ↔ G.Adj (u c z) y) := by
    intro t ht z y hy
    have hyrange : y ∈ Set.range (u t) := by
      rw [huRange t]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff t y).mpr hy
    obtain ⟨j, rfl⟩ := hyrange
    have hc3 : 3 ≤ c.supp.ncard := by rw [hc12]; norm_num
    have ht6 : t.supp.ncard = 6 := by
      simp only [es, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact he6
      · exact hf6
    have htc3 : 3 ≤ t.supp.ncard := by rw [ht6]; norm_num
    have hupair : ∀ a : ZMod c.supp.ncard, u c (a - 1) ≠ u c (a + 1) := by
      intro a
      exact (hu c).ne (zmod_sub_one_ne_add_one_of_three_le hc3 a)
    have hvpair : ∀ b : ZMod t.supp.ncard, u t (b - 1) ≠ u t (b + 1) := by
      intro b
      exact (hu t).ne (zmod_sub_one_ne_add_one_of_three_le htc3 b)
    have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D
      (u c) (u t) (1 : ZMod c.supp.ncard) (1 : ZMod t.supp.ncard)
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard))
      (huD c) (huD t) hupair hvpair
    have hp := adj_iff_add_targetOrder_of_entry_cycleIntertwine
      G (u c) (u t) (1 : ZMod c.supp.ncard)
        (1 : ZMod t.supp.ncard) hinter z j
    simp only [ZMod.addOrderOf_one, ht6, nsmul_eq_mul, mul_one] at hp
    have hcast : ((6 : ℕ) : ZMod c.supp.ncard) = 6 := by norm_num
    rw [hcast] at hp
    exact hp
  have := hbound hperiod
  simpa [D, es, hef] using this

/-- An order-six defect component has diagonal quotient at most three.  In
the forward orientation the Sidon bound gives two; in the reverse orientation
looplessness restricts the zero row to the three opposite-parity phases. -/
theorem degreeSix_orderSix_component_diagonal_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod d.supp.ncard → V) (hu : Function.Injective u)
    (huRange : Set.range u = d.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hd6 : d.supp.ncard = 6) :
    componentQuotientMatrix G (secondOrderDefectGraph G) d d ≤ 3 := by
  letI : NeZero d.supp.ncard := ⟨by rw [hd6]; norm_num⟩
  let D := secondOrderDefectGraph G
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard)
  rcases graph_equalEvenCycle_diagBlock_orientation
      (r := d.supp.ncard) (by rw [hd6]; norm_num) (by rw [hd6]; norm_num)
      G D hfree u hu hcomm huD with hfwd | hrev
  · have hfwdAdj : ∀ x y : ZMod d.supp.ncard,
        G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y) :=
      fun x y ↦ adj_iff_of_adjMatrix_int_eq G (hfwd x y)
    have hle := forwardComponent_diagonalQuotient_le_two
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) d u hu huRange hfwdAdj
    omega
  · have hu0d : u 0 ∈ d.supp := by
      have hmem : u 0 ∈ Set.range u := ⟨0, rfl⟩
      rw [huRange] at hmem
      exact hmem
    have hQ := componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree
        (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard))
      (adjMatrix_comm_secondOrderDefect_of_even_real
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard)) d d hu0d
    rw [hQ]
    have hdiv : 2 ∣ d.supp.ncard := by rw [hd6]; norm_num
    let φ : ZMod d.supp.ncard →+* ZMod 2 := ZMod.castHom hdiv (ZMod 2)
    let O : Finset (ZMod d.supp.ncard) := projectionFiber φ 1
    have hsubset : componentNeighborFinset G D d (u 0) ⊆ O.image u := by
      intro y hy
      have hydata : G.Adj (u 0) y ∧ y ∈ d.supp := by
        simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          and_comm] using hy
      have hyrange : y ∈ Set.range u := by
        rw [huRange]
        exact hydata.2
      obtain ⟨j, rfl⟩ := hyrange
      have hpar : φ j ≠ 0 := by
        intro hz
        have hjrange : j ∈ Set.range (fun k : ZMod d.supp.ncard ↦ 2 * k) :=
          (zmod_mem_range_two_mul_iff_castHom_eq_zero hdiv j).mpr hz
        obtain ⟨k, hk⟩ := hjrange
        have hadd : j + 0 = k + k := by
          rw [← hk]
          ring
        have heq := reverseTranslationInvariant_eq_of_add_eq
          (fun a b ↦ G.adjMatrix ℤ (u a) (u b)) hrev hadd
        have hadjkk : G.Adj (u k) (u k) :=
          (adj_iff_of_adjMatrix_int_eq G heq).mp hydata.1
        exact G.loopless.irrefl _ hadjkk
      have hjone : φ j = 1 := by
        have hvlt : (φ j).val < 2 := ZMod.val_lt _
        have hv : (φ j).val = 0 ∨ (φ j).val = 1 := by omega
        rcases hv with hv | hv
        · exact (hpar ((ZMod.val_eq_zero (φ j)).mp hv)).elim
        · apply ZMod.val_injective 2
          rw [ZMod.val_one'' (by norm_num : (2 : ℕ) ≠ 1)]
          exact hv
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      simp [O, projectionFiber, hjone]
    calc
      (componentNeighborFinset G D d (u 0)).card ≤ (O.image u).card :=
        Finset.card_le_card hsubset
      _ ≤ O.card := Finset.card_image_le
      _ = 3 := by
        rw [show O.card = d.supp.ncard / 2 by
          simpa [O, φ] using card_projectionFiber_zmod_castHom hdiv (1 : ZMod 2)]
        omega

/-- Once one order-three contact is fixed and a second such contact is
excluded, the order-nine row has a unique arithmetic shape: one order-nine
double contact, one order-nine single contact, and exactly one unused
order-three component. -/
theorem degreeSix_orderNine_single_contact_shape
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c e : C)
    (hec : e ≠ c) (hc9 : size c = 9) (he3 : size e = 3)
    (htotal : (∑ t : C, size t) = 33) (hlower : ∀ t, 3 ≤ size t)
    (hrow : (∑ t ∈ Finset.univ.erase c, Q c t) = 4)
    (hprod : (∑ t ∈ Finset.univ.erase c, Q c t * Q t c) = 8)
    (hbal : ∀ t, size c * Q c t = size t * Q t c)
    (hperiod : ∀ t, ¬ 9 ∣ size t → Q c t ≤ 1)
    (hce : Q c e = 1) (hecQ : Q e c = 3)
    (hnoOtherThree : ∀ f, f ≠ c → f ≠ e → size f = 3 → Q c f = 0) :
    ∃ a b f : C,
      a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ b ≠ a ∧
      f ≠ c ∧ f ≠ e ∧ f ≠ a ∧ f ≠ b ∧
      size a = 9 ∧ size b = 9 ∧ size f = 3 ∧
      Q c a = 2 ∧ Q a c = 2 ∧ Q c b = 1 ∧ Q b c = 1 ∧
      Q c f = 0 ∧ ∀ x, x = c ∨ x = e ∨ x = a ∨ x = b ∨ x = f := by
  let S : Finset C := Finset.univ.erase c
  have heS : e ∈ S := Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hclass : ∀ t ∈ S, 0 < Q c t →
      (size t = 3 ∧ Q c t = 1 ∧ Q t c = 3) ∨
      (size t = 9 ∧ Q c t = 1 ∧ Q t c = 1) ∨
      (size t = 9 ∧ Q c t = 2 ∧ Q t c = 2) ∨
      (size t = 18 ∧ Q c t = 2 ∧ Q t c = 1) := by
    intro t htS hqpos
    have htc : t ≠ c := (Finset.mem_erase.mp htS).1
    have hqle : Q c t ≤ 4 := by
      have hsingle : Q c t ≤ ∑ x ∈ S, Q c x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) htS
      simpa [S, hrow] using hsingle
    have hple : Q c t * Q t c ≤ 8 := by
      have hsingle : Q c t * Q t c ≤ ∑ x ∈ S, Q c x * Q x c :=
        Finset.single_le_sum
          (fun x (_ : x ∈ S) ↦ Nat.zero_le (Q c x * Q x c)) htS
      simpa [S, hprod] using hsingle
    have hsizele : size t ≤ 24 := by
      have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset C) size hcMem
      have hsingle : size t ≤ ∑ x ∈ Finset.univ.erase c, size x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) htS
      rw [htotal, hc9] at hsplit
      omega
    have hb := hbal t
    rw [hc9] at hb
    by_cases hdvd : 9 ∣ size t
    · obtain ⟨k, hk⟩ := hdvd
      have hkpos : 0 < k := by
        by_contra hk0
        push Not at hk0
        have hkz : k = 0 := by omega
        subst k
        simp at hk
        have := hlower t
        omega
      have hk12 : k = 1 ∨ k = 2 := by rw [hk] at hsizele; omega
      rcases hk12 with rfl | rfl
      · have hst : size t = 9 := by omega
        rw [hst] at hb
        have hrq : Q t c = Q c t := by omega
        rw [hrq] at hple
        have hq2 : Q c t ≤ 2 := by
          by_contra hnot
          have : 3 ≤ Q c t := by omega
          nlinarith
        rcases (show Q c t = 1 ∨ Q c t = 2 by omega) with hq | hq
        · exact Or.inr (Or.inl ⟨hst, hq, by omega⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hst, hq, by omega⟩))
      · have hst : size t = 18 := by omega
        rw [hst] at hb
        have hqeven : Q c t = 2 * Q t c := by omega
        rcases (show Q c t = 2 ∨ Q c t = 4 by
          have : 0 < Q t c := by nlinarith
          omega) with hq | hq
        · exact Or.inr (Or.inr (Or.inr ⟨hst, hq, by omega⟩))
        · have het : e ≠ t := by
            intro h
            subst t
            omega
          have htErase : t ∈ S.erase e :=
            Finset.mem_erase.mpr ⟨het.symm, htS⟩
          have hsE := Finset.sum_erase_add S (Q c) heS
          have hsT := Finset.sum_erase_add (S.erase e) (Q c) htErase
          have hrowS : (∑ x ∈ S, Q c x) = 4 := by simpa [S] using hrow
          omega
    · have hqone : Q c t = 1 := by
        have := hperiod t hdvd
        omega
      rw [hqone, mul_one] at hb
      have hrtpos : 0 < Q t c := by nlinarith
      have hrtle : Q t c ≤ 3 := by
        have := hlower t
        nlinarith
      rcases (show Q t c = 1 ∨ Q t c = 2 ∨ Q t c = 3 by omega) with hr | hr | hr
      · rw [hr] at hb
        have hst : size t = 9 := by omega
        exact (hdvd (by rw [hst])).elim
      · rw [hr] at hb
        omega
      · rw [hr] at hb
        exact Or.inl ⟨by omega, hqone, hr⟩
  let excess : C → ℕ := fun t ↦ Q c t * (Q t c - 1)
  have hdecomp : ∀ t ∈ S, Q c t * Q t c = Q c t + excess t := by
    intro t htS
    by_cases hq : Q c t = 0
    · simp [excess, hq]
    · have ht := hclass t htS (Nat.pos_of_ne_zero hq)
      rcases ht with h | h | h | h <;> rcases h with ⟨_, hqv, hrv⟩ <;>
        simp [excess, hqv, hrv]
  have hexcessSum : (∑ t ∈ S, excess t) = 4 := by
    have hsum : 8 = 4 + ∑ t ∈ S, excess t := by
      calc
        8 = ∑ t ∈ S, Q c t * Q t c := by simpa [S] using hprod.symm
        _ = ∑ t ∈ S, (Q c t + excess t) := Finset.sum_congr rfl hdecomp
        _ = (∑ t ∈ S, Q c t) + ∑ t ∈ S, excess t := by
          rw [Finset.sum_add_distrib]
        _ = 4 + ∑ t ∈ S, excess t := by simpa [S] using hrow
    omega
  have heExcess : excess e = 2 := by simp [excess, hce, hecQ]
  let T : Finset C := S.erase e
  have hexcessT : (∑ t ∈ T, excess t) = 2 := by
    have hsplit := Finset.sum_erase_add S excess heS
    dsimp [T]
    omega
  have hTne : (∑ t ∈ T, excess t) ≠ 0 := by omega
  obtain ⟨a, haT, haNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hTne
  have haS : a ∈ S := (Finset.mem_erase.mp haT).2
  have hae : a ≠ e := (Finset.mem_erase.mp haT).1
  have hac : a ≠ c := (Finset.mem_erase.mp haS).1
  have haPos : 0 < Q c a := by
    by_contra hq0
    push Not at hq0
    have hqz : Q c a = 0 := by omega
    simp [excess, hqz] at haNe
  have haClass := hclass a haS haPos
  have haData : size a = 9 ∧ Q c a = 2 ∧ Q a c = 2 := by
    rcases haClass with h | h | h | h
    · rcases h with ⟨ha3, _, _⟩
      rw [hnoOtherThree a hac hae ha3] at haPos
      omega
    · rcases h with ⟨_, hq, hrq⟩
      simp [excess, hq, hrq] at haNe
    · exact h
    · rcases h with ⟨_, hq, hrq⟩
      simp [excess, hq, hrq] at haNe
  have haExcess : excess a = 2 := by
    simp [excess, haData.2.1, haData.2.2]
  have hrowT : (∑ t ∈ T, Q c t) = 3 := by
    have hsplit := Finset.sum_erase_add S (Q c) heS
    have hrowS : (∑ t ∈ S, Q c t) = 4 := by simpa [S] using hrow
    dsimp [T]
    omega
  let U : Finset C := T.erase a
  have hrowU : (∑ t ∈ U, Q c t) = 1 := by
    have hsplit := Finset.sum_erase_add T (Q c) haT
    dsimp [U]
    omega
  have hUne : (∑ t ∈ U, Q c t) ≠ 0 := by omega
  obtain ⟨b, hbU, hbNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hUne
  have hbT : b ∈ T := (Finset.mem_erase.mp hbU).2
  have hba : b ≠ a := (Finset.mem_erase.mp hbU).1
  have hbS : b ∈ S := (Finset.mem_erase.mp hbT).2
  have hbe : b ≠ e := (Finset.mem_erase.mp hbT).1
  have hbc : b ≠ c := (Finset.mem_erase.mp hbS).1
  have hbLe : Q c b ≤ ∑ t ∈ U, Q c t :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hbU
  have hqcb : Q c b = 1 := by omega
  have hbClass := hclass b hbS (by omega)
  have hbData : size b = 9 ∧ Q b c = 1 := by
    rcases hbClass with h | h | h | h
    · rcases h with ⟨hb3, _, _⟩
      rw [hnoOtherThree b hbc hbe hb3] at hqcb
      contradiction
    · exact ⟨h.1, h.2.2⟩
    · omega
    · omega
  let R : Finset C := U.erase b
  have hrowR : (∑ t ∈ R, Q c t) = 0 := by
    have hsplit := Finset.sum_erase_add U (Q c) hbU
    dsimp [R]
    omega
  have hsizeKnown : size c + size e + size a + size b = 30 := by
    omega
  have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have hsizeC := Finset.sum_erase_add (Finset.univ : Finset C) size hcMem
  have hsizeE := Finset.sum_erase_add S size heS
  have hsizeA := Finset.sum_erase_add T size haT
  have hsizeB := Finset.sum_erase_add U size hbU
  have hsizeR : (∑ t ∈ R, size t) = 3 := by
    dsimp [S, T, U, R] at *
    omega
  have hRne : (∑ t ∈ R, size t) ≠ 0 := by omega
  obtain ⟨f, hfR, hfNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hRne
  have hfU : f ∈ U := (Finset.mem_erase.mp hfR).2
  have hfb : f ≠ b := (Finset.mem_erase.mp hfR).1
  have hfT : f ∈ T := (Finset.mem_erase.mp hfU).2
  have hfa : f ≠ a := (Finset.mem_erase.mp hfU).1
  have hfS : f ∈ S := (Finset.mem_erase.mp hfT).2
  have hfe : f ≠ e := (Finset.mem_erase.mp hfT).1
  have hfc : f ≠ c := (Finset.mem_erase.mp hfS).1
  have hfLe : size f ≤ ∑ t ∈ R, size t :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hfR
  have hf3 : size f = 3 := by have := hlower f; omega
  have hqcf : Q c f = 0 := hnoOtherThree f hfc hfe hf3
  have hRsingle : ∀ x ∈ R, x = f := by
    intro x hx
    by_contra hxf
    have hfErase : f ∈ R.erase x :=
      Finset.mem_erase.mpr ⟨fun hfx ↦ hxf hfx.symm, hfR⟩
    have hsX := Finset.sum_erase_add R size hx
    have hsF := Finset.sum_erase_add (R.erase x) size hfErase
    have hxLower := hlower x
    have hfLower := hlower f
    omega
  refine ⟨a, b, f, hac, hae, hbc, hbe, hba, hfc, hfe, hfa,
    hfb, haData.1, hbData.1, hf3, haData.2.1, haData.2.2,
    hqcb, hbData.2, hqcf, ?_⟩
  intro x
  by_cases hxc : x = c
  · exact Or.inl hxc
  have hxS : x ∈ S := Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ x⟩
  by_cases hxe : x = e
  · exact Or.inr (Or.inl hxe)
  have hxT : x ∈ T := Finset.mem_erase.mpr ⟨hxe, hxS⟩
  by_cases hxa : x = a
  · exact Or.inr (Or.inr (Or.inl hxa))
  have hxU : x ∈ U := Finset.mem_erase.mpr ⟨hxa, hxT⟩
  by_cases hxb : x = b
  · exact Or.inr (Or.inr (Or.inr (Or.inl hxb)))
  have hxR : x ∈ R := Finset.mem_erase.mpr ⟨hxb, hxU⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (hRsingle x hxR))))

/-- Arithmetic terminal for the surviving order-nine singleton shape. -/
theorem false_of_degreeSix_orderNine_single_contact_shape
    {C : Type*} [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c e a b f : C)
    (hec : e ≠ c) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hba : b ≠ a)
    (hfc : f ≠ c) (hfe : f ≠ e) (hfa : f ≠ a) (hfb : f ≠ b)
    (hc9 : size c = 9) (he3 : size e = 3)
    (ha9 : size a = 9) (hb9 : size b = 9) (hf3 : size f = 3)
    (hcc : Q c c = 2) (hce : Q c e = 1)
    (hca : Q c a = 2) (hcb : Q c b = 1) (hcf : Q c f = 0)
    (hecQ : Q e c = 3) (hee : Q e e = 0)
    (herow : Q e a + Q e b + Q e f = 3)
    (heprofile : ∀ t, 0 < Q e t → Q t e = 1 ∧ size t = 3 * Q e t)
    (hfcQ : Q f c = 0) (hff : Q f f = 0)
    (hfrow : Q f e + Q f a + Q f b = 6)
    (hfprofile : ∀ t, 0 < Q f t → Q t f = 1 ∧ size t = 3 * Q f t)
    (hsqce : Q c c * Q c e + Q c e * Q e e +
        Q c a * Q a e + Q c b * Q b e + Q c f * Q f e = 3)
    (hgroup : Q b e + Q b f ≤ 1) : False := by
  have hea : Q e a = 0 := by
    by_contra hne
    have hpos : 0 < Q e a := Nat.pos_of_ne_zero hne
    have haeQ := (heprofile a hpos).1
    simp [hcc, hce, hca, hcb, hcf, hee, haeQ] at hsqce
    omega
  have heb : Q e b = 3 := by
    by_cases hzero : Q e b = 0
    · have hefQ : Q e f = 3 := by omega
      have hsize := (heprofile f (by omega)).2
      omega
    · have hpos : 0 < Q e b := Nat.pos_of_ne_zero hzero
      have hsize := (heprofile b hpos).2
      omega
  have hbeQ : Q b e = 1 := (heprofile b (by omega)).1
  have hefQ : Q e f = 0 := by omega
  have hfeCases : Q f e = 0 ∨ Q f e = 1 := by
    by_cases hzero : Q f e = 0
    · exact Or.inl hzero
    · have hsize := (hfprofile e (Nat.pos_of_ne_zero hzero)).2
      exact Or.inr (by omega)
  have hfaCases : Q f a = 0 ∨ Q f a = 3 := by
    by_cases hzero : Q f a = 0
    · exact Or.inl hzero
    · have hsize := (hfprofile a (Nat.pos_of_ne_zero hzero)).2
      exact Or.inr (by omega)
  have hfbCases : Q f b = 0 ∨ Q f b = 3 := by
    by_cases hzero : Q f b = 0
    · exact Or.inl hzero
    · have hsize := (hfprofile b (Nat.pos_of_ne_zero hzero)).2
      exact Or.inr (by omega)
  have hfaQ : Q f a = 3 := by
    rcases hfeCases with hfe | hfe <;>
      rcases hfaCases with hfa | hfa <;>
      rcases hfbCases with hfb | hfb <;> omega
  have hfbQ : Q f b = 3 := by
    rcases hfeCases with hfe | hfe <;>
      rcases hfaCases with hfa | hfa <;>
      rcases hfbCases with hfb | hfb <;> omega
  have hbfQ : Q b f = 1 := (hfprofile b (by omega)).1
  omega

/-- In the exhausted order-nine shape, the unused order-three component
cannot have diagonal two: its remaining row mass four would be a sum of
multiples of three by balance with the two order-nine components. -/
theorem degreeSix_orderNine_shape_unused_orderThree_diagonal_zero
    {C : Type*} (Q : C → C → ℕ) (size : C → ℕ)
    (c e a b f : C)
    (he3 : size e = 3) (ha9 : size a = 9) (hb9 : size b = 9) (hf3 : size f = 3)
    (hfc : Q f c = 0) (hfe : Q f e = 0)
    (hfrow : Q f c + Q f e + Q f a + Q f b + Q f f = 6)
    (hbal : ∀ t, size f * Q f t = size t * Q t f)
    (hdiag : Q f f = 0 ∨ Q f f = 2) : Q f f = 0 := by
  rcases hdiag with hzero | htwo
  · exact hzero
  · have hbe := hbal e
    have hba := hbal a
    have hbb := hbal b
    rw [hfc, hfe, htwo] at hfrow
    rw [hf3, he3] at hbe
    rw [hf3, ha9] at hba
    rw [hf3, hb9] at hbb
    omega

/-- The `(12,12,6,3)` order-twelve row shape is incompatible with its two
off-diagonal square equations as soon as the order-six diagonal is at most
three.  The equations otherwise force that diagonal to equal four. -/
theorem false_of_degreeSix_orderTwelve_three_six_twelve_shape
    {C : Type*} (Q : C → C → ℕ) (size : C → ℕ)
    (c a d e : C)
    (hc12 : size c = 12) (ha12 : size a = 12)
    (hd6 : size d = 6) (he3 : size e = 3)
    (hcc : Q c c = 2) (hca : Q c a = 3)
    (hcd : Q c d = 1) (hce : Q c e = 0)
    (hbalDA : size d * Q d a = size a * Q a d)
    (hsqa : Q c c * Q c a + Q c a * Q a a +
        Q c d * Q d a + Q c e * Q e a = 12)
    (hsqd : Q c c * Q c d + Q c a * Q a d +
        Q c d * Q d d + Q c e * Q e d = 6)
    (hdd : Q d d ≤ 3) : False := by
  rw [hd6, ha12] at hbalDA
  rw [hcc, hca, hcd, hce] at hsqa hsqd
  omega

/-- Three-term form of the sparse order-twelve square terminal. -/
theorem false_of_degreeSix_orderTwelve_sparse_square
    {C : Type*} (Q : C → C → ℕ) (size : C → ℕ)
    (c a d : C)
    (hc12 : size c = 12) (ha12 : size a = 12) (hd6 : size d = 6)
    (hcc : Q c c = 2) (hca : Q c a = 3) (hcd : Q c d = 1)
    (hbalDA : size d * Q d a = size a * Q a d)
    (hsqa : Q c c * Q c a + Q c a * Q a a + Q c d * Q d a = 12)
    (hsqd : Q c c * Q c d + Q c a * Q a d + Q c d * Q d d = 6)
    (hdd : Q d d ≤ 3) : False := by
  rw [hd6, ha12] at hbalDA
  rw [hcc, hca, hcd] at hsqa hsqd
  omega

/-- Presburger kernel for the order-twelve contact classifier.  The six
variables count positive contacts of types `(3,1,4)`, `(4,1,3)`, `(6,1,2)`,
and `(12,q,q)` for `q=1,2,3`.  Used support order is either all 21 outside
vertices or at most 18, since every unused component has order at least
three. -/
theorem degreeSix_orderTwelve_contact_count_classifier
    (n3 n4 n6 n121 n122 n123 used : ℕ)
    (hrow : n3 + n4 + n6 + n121 + 2 * n122 + 3 * n123 = 4)
    (hprod : 4 * n3 + 3 * n4 + 2 * n6 + n121 + 4 * n122 +
      9 * n123 = 11)
    (hused : used = 3 * n3 + 4 * n4 + 6 * n6 +
      12 * (n121 + n122 + n123))
    (hgap : used = 21 ∨ used ≤ 18) :
    (n3 = 0 ∧ n4 = 0 ∧ n6 = 1 ∧ n121 = 0 ∧ n122 = 0 ∧
      n123 = 1 ∧ used = 18) ∨
    (n3 = 0 ∧ n4 = 3 ∧ n6 = 1 ∧ n121 = 0 ∧ n122 = 0 ∧
      n123 = 0 ∧ used = 18) := by
  have hn122 : n122 ≤ 2 := by omega
  have hn123 : n123 ≤ 1 := by omega
  interval_cases n123 <;> interval_cases n122 <;> omega

/-- Pointwise classification of a positive off-diagonal entry in an
order-twelve singleton row. -/
theorem degreeSix_orderTwelve_positive_contact_class
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c t : C)
    (hc12 : size c = 12) (htc : t ≠ c)
    (hlower : 3 ≤ size t)
    (hsizele : size t ≤ 21)
    (hqpos : 0 < Q c t) (hqle : Q c t ≤ 4)
    (hprodle : Q c t * Q t c ≤ 11)
    (hbal : size c * Q c t = size t * Q t c)
    (hperiod : ¬ 12 ∣ size t → Q c t ≤ 1) :
    (size t = 3 ∧ Q c t = 1 ∧ Q t c = 4) ∨
    (size t = 4 ∧ Q c t = 1 ∧ Q t c = 3) ∨
    (size t = 6 ∧ Q c t = 1 ∧ Q t c = 2) ∨
    (size t = 12 ∧ Q c t = 1 ∧ Q t c = 1) ∨
    (size t = 12 ∧ Q c t = 2 ∧ Q t c = 2) ∨
    (size t = 12 ∧ Q c t = 3 ∧ Q t c = 3) := by
  rw [hc12] at hbal
  by_cases hdvd : 12 ∣ size t
  · obtain ⟨k, hk⟩ := hdvd
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := by omega
      subst k
      simp at hk
      omega
    have hkone : k = 1 := by rw [hk] at hsizele; nlinarith
    subst k
    have hsize : size t = 12 := by omega
    rw [hsize] at hbal
    have heq : Q t c = Q c t := by omega
    rw [heq] at hprodle
    have hq3 : Q c t ≤ 3 := by nlinarith
    rcases (show Q c t = 1 ∨ Q c t = 2 ∨ Q c t = 3 by omega) with hq | hq | hq
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsize, hq, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hsize, hq, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hsize, hq, by omega⟩))))
  · have hq : Q c t = 1 := by
      have := hperiod hdvd
      omega
    rw [hq, mul_one] at hbal
    have hrpos : 0 < Q t c := by nlinarith
    have hrle : Q t c ≤ 4 := by
      by_contra hnot
      have : 5 ≤ Q t c := by omega
      nlinarith
    rcases (show Q t c = 1 ∨ Q t c = 2 ∨ Q t c = 3 ∨ Q t c = 4 by omega) with
      hr | hr | hr | hr
    · rw [hr] at hbal
      exfalso
      apply hdvd
      use 1
      omega
    · exact Or.inr (Or.inr (Or.inl ⟨by nlinarith [hbal], hq, hr⟩))
    · exact Or.inr (Or.inl ⟨by nlinarith [hbal], hq, hr⟩)
    · exact Or.inl ⟨by nlinarith [hbal], hq, hr⟩

/-- Aggregate the six pointwise order-twelve contact classes into the row,
two-step, and used-order accounting equations consumed by
`degreeSix_orderTwelve_contact_count_classifier`. -/
theorem degreeSix_orderTwelve_contact_aggregate_equations
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (q r size : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 3 ∧ q t = 1 ∧ r t = 4) ∨
      (size t = 4 ∧ q t = 1 ∧ r t = 3) ∨
      (size t = 6 ∧ q t = 1 ∧ r t = 2) ∨
      (size t = 12 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 12 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 12 ∧ q t = 3 ∧ r t = 3)) :
    let n3 := (S.filter fun t ↦ size t = 3 ∧ q t = 1).card
    let n4 := (S.filter fun t ↦ size t = 4 ∧ q t = 1).card
    let n6 := (S.filter fun t ↦ size t = 6 ∧ q t = 1).card
    let n121 := (S.filter fun t ↦ size t = 12 ∧ q t = 1).card
    let n122 := (S.filter fun t ↦ size t = 12 ∧ q t = 2).card
    let n123 := (S.filter fun t ↦ size t = 12 ∧ q t = 3).card
    (∑ t ∈ S, q t) = n3 + n4 + n6 + n121 + 2 * n122 + 3 * n123 ∧
    (∑ t ∈ S, q t * r t) =
      4 * n3 + 3 * n4 + 2 * n6 + n121 + 4 * n122 + 9 * n123 ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      3 * n3 + 4 * n4 + 6 * n6 + 12 * (n121 + n122 + n123) := by
  dsimp
  have hqpoint : ∀ t ∈ S, q t =
      (if size t = 3 ∧ q t = 1 then 1 else 0) +
      (if size t = 4 ∧ q t = 1 then 1 else 0) +
      (if size t = 6 ∧ q t = 1 then 1 else 0) +
      (if size t = 12 ∧ q t = 1 then 1 else 0) +
      (if size t = 12 ∧ q t = 2 then 2 else 0) +
      (if size t = 12 ∧ q t = 3 then 3 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h3 | h4 | h6 | h121 | h122 | h123
    · simp [h0]
    · rcases h3 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h4 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h6 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h121 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h122 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h123 with ⟨hs, hq, hr⟩; simp [hs, hq]
  have hppoint : ∀ t ∈ S, q t * r t =
      (if size t = 3 ∧ q t = 1 then 4 else 0) +
      (if size t = 4 ∧ q t = 1 then 3 else 0) +
      (if size t = 6 ∧ q t = 1 then 2 else 0) +
      (if size t = 12 ∧ q t = 1 then 1 else 0) +
      (if size t = 12 ∧ q t = 2 then 4 else 0) +
      (if size t = 12 ∧ q t = 3 then 9 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h3 | h4 | h6 | h121 | h122 | h123
    · simp [h0]
    · rcases h3 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
    · rcases h4 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
    · rcases h6 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
    · rcases h121 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
    · rcases h122 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
    · rcases h123 with ⟨hs, hq, hr⟩; simp [hs, hq, hr]
  have hspoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if size t = 3 ∧ q t = 1 then 3 else 0) +
      (if size t = 4 ∧ q t = 1 then 4 else 0) +
      (if size t = 6 ∧ q t = 1 then 6 else 0) +
      (if size t = 12 ∧ q t = 1 then 12 else 0) +
      (if size t = 12 ∧ q t = 2 then 12 else 0) +
      (if size t = 12 ∧ q t = 3 then 12 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h3 | h4 | h6 | h121 | h122 | h123
    · simp [h0]
    · rcases h3 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h4 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h6 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h121 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h122 with ⟨hs, hq, hr⟩; simp [hs, hq]
    · rcases h123 with ⟨hs, hq, hr⟩; simp [hs, hq]
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    omega
  · constructor
    · rw [Finset.sum_congr rfl hppoint]
      simp only [Finset.sum_add_distrib]
      repeat' rw [hsumConst]
      omega
    · rw [Finset.sum_congr rfl hspoint]
      simp only [Finset.sum_add_distrib]
      repeat' rw [hsumConst]
      omega

/-- The three units of a residual contact row have only the partitions
`1+1+1`, `1+2`, and `3`. -/
theorem contact_count_partition_of_weight_three
    (n1 n2 n3 : ℕ) (h : n1 + 2 * n2 + 3 * n3 = 3) :
    (n1 = 3 ∧ n2 = 0 ∧ n3 = 0) ∨
    (n1 = 1 ∧ n2 = 1 ∧ n3 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 1) := by
  omega

/-- Finset realization of `contact_count_partition_of_weight_three`. -/
theorem contact_filter_counts_of_sum_three
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (q : C → ℕ) (hsum : (∑ t ∈ S, q t) = 3) :
    let n1 := (S.filter fun t ↦ q t = 1).card
    let n2 := (S.filter fun t ↦ q t = 2).card
    let n3 := (S.filter fun t ↦ q t = 3).card
    (n1 = 3 ∧ n2 = 0 ∧ n3 = 0) ∨
    (n1 = 1 ∧ n2 = 1 ∧ n3 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 1) := by
  dsimp
  have hqle : ∀ t ∈ S, q t ≤ 3 := by
    intro t ht
    have hsingle : q t ≤ ∑ x ∈ S, q x :=
      Finset.single_le_sum (f := q) (fun _ _ ↦ Nat.zero_le _) ht
    omega
  have hpoint : ∀ t ∈ S, q t =
      (if q t = 1 then 1 else 0) +
      (if q t = 2 then 2 else 0) +
      (if q t = 3 then 3 else 0) := by
    intro t ht
    have := hqle t ht
    interval_cases q t <;> simp_all
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hweighted :
      (S.filter fun t ↦ q t = 1).card +
      2 * (S.filter fun t ↦ q t = 2).card +
      3 * (S.filter fun t ↦ q t = 3).card = 3 := by
    have h1 := hsumConst (fun t ↦ q t = 1) 1
    have h2 := hsumConst (fun t ↦ q t = 2) 2
    have h3 := hsumConst (fun t ↦ q t = 3) 3
    have hdecomp := Finset.sum_congr rfl hpoint
    simp only [Finset.sum_add_distrib] at hdecomp
    rw [h1, h2, h3] at hdecomp
    simpa [one_mul] using hdecomp.symm.trans hsum
  exact contact_count_partition_of_weight_three _ _ _ hweighted

/-- Components of order at least three and total order six form either one
order-six component or two order-three components. -/
theorem component_orders_sum_six_classification
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size : C → ℕ)
    (hlower : ∀ t ∈ S, 3 ≤ size t)
    (hsum : (∑ t ∈ S, size t) = 6) :
    (∃ f, S = {f} ∧ size f = 6) ∨
    (∃ f g, f ≠ g ∧ S = {f, g} ∧ size f = 3 ∧ size g = 3) := by
  have hcardPos : 0 < S.card := by
    by_contra hzero
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    simp at hsum
  have hlowerSum : (∑ t ∈ S, 3) ≤ ∑ t ∈ S, size t := by
    exact Finset.sum_le_sum fun t ht ↦ hlower t ht
  have hcardLe : S.card ≤ 2 := by
    simp at hlowerSum
    omega
  rcases (show S.card = 1 ∨ S.card = 2 by omega) with hcard | hcard
  · obtain ⟨f, hS⟩ := Finset.card_eq_one.mp hcard
    exact Or.inl ⟨f, hS, by simpa [hS] using hsum⟩
  · obtain ⟨f, g, hfg, hS⟩ := Finset.card_eq_two.mp hcard
    have hf := hlower f (by simp [hS])
    have hg := hlower g (by simp [hS])
    have hfgsum : size f + size g = 6 := by simpa [hS, hfg] using hsum
    exact Or.inr ⟨f, g, hfg, hS, by omega, by omega⟩

/-- Arithmetic terminal for the order-six residual partition `1+2`.  The
two square equations and the global diagonal budget force the order-twelve
target to contact both distinct order-six components, contradicting grouped
periodicity. -/
theorem false_of_degreeSix_orderSix_one_two_contact
    {C : Type*} (Q : C → C → ℕ) (size : C → ℕ)
    (c e d a : C)
    (hc6 : size c = 6) (he3 : size e = 3)
    (hd6 : size d = 6) (ha12 : size a = 12)
    (hcc : Q c c = 2) (hce : Q c e = 1)
    (hcd : Q c d = 1) (hca : Q c a = 2)
    (hed : Q e d = 2) (hea : Q e a = 0)
    (hbalCA : size c * Q c a = size a * Q a c)
    (hbalDA : size d * Q d a = size a * Q a d)
    (hsqd : Q c c * Q c d + Q c e * Q e d +
      Q c d * Q d d + Q c a * Q a d = 6)
    (hsqa : Q c c * Q c a + Q c e * Q e a +
      Q c d * Q d a + Q c a * Q a a = 12)
    (hdiagBudget : Q d d + Q a a ≤ 4)
    (hgroup : Q a c + Q a d ≤ 1) : False := by
  rw [hc6, ha12, hca] at hbalCA
  rw [hd6, ha12] at hbalDA
  rw [hcc, hce, hcd, hca, hed] at hsqd
  rw [hcc, hce, hcd, hca, hea] at hsqa
  omega

/-- Arithmetic terminal for the residual partition `3`: an order-three row
cannot positively contact the order-eighteen target, so the off-diagonal
square `(c,e)` is one short. -/
theorem false_of_degreeSix_orderSix_three_contact
    {C : Type*} (Q : C → C → ℕ) (size : C → ℕ)
    (c e a : C)
    (hc6 : size c = 6) (he3 : size e = 3) (ha18 : size a = 18)
    (hcc : Q c c = 2) (hce : Q c e = 1) (hca : Q c a = 3)
    (hee : Q e e = 0) (hea : Q e a = 0)
    (hbalEA : size e * Q e a = size a * Q a e)
    (hsqe : Q c c * Q c e + Q c e * Q e e + Q c a * Q a e = 3) : False := by
  rw [he3, ha18, hea] at hbalEA
  rw [hcc, hce, hca, hee, hbalEA] at hsqe
  omega

/-- In the `1+1+1` contact pattern with one unused order-six component, the
three internal contact-row equations sum to an even correction of ten, while
the trace forces their diagonal sum to three. -/
theorem false_of_degreeSix_orderSix_three_single_contacts_unused_six
    {C : Type*} (Q : C → C → ℕ) (d x y : C)
    (hd : Q d d + Q x d + Q y d = 2)
    (hx : Q d x + Q x x + Q y x = 4)
    (hy : Q d y + Q x y + Q y y = 4)
    (hdx : Q d x = Q x d) (hdy : Q d y = Q y d)
    (hxy : Q x y = Q y x)
    (htrace : Q d d + Q x x + Q y y = 3) : False := by
  omega

/-- In the `1+1+1` contact pattern with two unused order-three components,
the first unused row has diagonal zero and mutual quotient one; its square
with the forced order-three component then forces a second order-three target
in the shared order-six row, contradicting grouped periodicity. -/
theorem false_of_degreeSix_orderSix_three_single_contacts_two_unused_three
    {C : Type*} (Q : C → C → ℕ) (d e f g : C)
    (hde : Q d e = 1)
    (hff : Q f f = 0 ∨ Q f f = 2)
    (hfgsymm : Q f g = Q g f)
    (hfrow : Q f f + Q f g = 1)
    (hsqef : 2 * Q d f + Q f f + Q g f = 3)
    (hgroup : Q d e + Q d f ≤ 1) : False := by
  rcases hff with hzero | htwo <;> omega

/-- If every component in `S` has order at least three and total order 21,
the order used by positive contacts is either all 21 or at most 18. -/
theorem contact_used_order_eq_total_or_le_eighteen
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (q size : C → ℕ)
    (htotal : (∑ t ∈ S, size t) = 21)
    (hlower : ∀ t ∈ S, 3 ≤ size t) :
    (∑ t ∈ S, if q t = 0 then 0 else size t) = 21 ∨
      (∑ t ∈ S, if q t = 0 then 0 else size t) ≤ 18 := by
  let used := ∑ t ∈ S, if q t = 0 then 0 else size t
  let unused := ∑ t ∈ S, if q t = 0 then size t else 0
  have hsplit : used + unused = 21 := by
    rw [← htotal]
    dsimp [used, unused]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hq : q t = 0 <;> simp [hq]
  by_cases hu : unused = 0
  · exact Or.inl (by omega)
  · have husum : (∑ t ∈ S, if q t = 0 then size t else 0) ≠ 0 := by
      simpa [unused] using hu
    obtain ⟨t, ht, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero husum
    have hq0 : q t = 0 := by
      by_contra hq
      simp [hq] at htne
    have hterm : 3 ≤ (if q t = 0 then size t else 0) := by
      simpa [hq0] using hlower t ht
    have hle : (if q t = 0 then size t else 0) ≤ unused := by
      dsimp [unused]
      exact Finset.single_le_sum
        (f := fun x ↦ if q x = 0 then size x else 0)
        (fun _ _ ↦ Nat.zero_le _) ht
    exact Or.inr (by omega)

/-- Two distinct nonnegative summands are bounded by the full finite sum. -/
theorem two_distinct_terms_le_sum
    {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → ℕ) {c e : C} (hce : c ≠ e) :
    f c + f e ≤ ∑ x, f x := by
  have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have heMem : e ∈ (Finset.univ.erase c : Finset C) :=
    Finset.mem_erase.mpr ⟨fun h ↦ hce h.symm, Finset.mem_univ e⟩
  have hsplitc := Finset.sum_erase_add (Finset.univ : Finset C) f hcMem
  have hsplite := Finset.sum_erase_add (Finset.univ.erase c : Finset C) f heMem
  omega

/-- Expand a finite sum when five explicitly distinct points exhaust the
index type. -/
theorem sum_eq_five_of_exhaust
    {C : Type*} [Fintype C] [DecidableEq C] (g : C → ℕ)
    (c e a b f : C)
    (hec : e ≠ c) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hba : b ≠ a)
    (hfc : f ≠ c) (hfe : f ≠ e) (hfa : f ≠ a) (hfb : f ≠ b)
    (hexhaust : ∀ x, x = c ∨ x = e ∨ x = a ∨ x = b ∨ x = f) :
    (∑ x, g x) = g c + g e + g a + g b + g f := by
  let S1 : Finset C := Finset.univ.erase c
  let S2 : Finset C := S1.erase e
  let S3 : Finset C := S2.erase a
  let S4 : Finset C := S3.erase b
  let S5 : Finset C := S4.erase f
  have hc : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have he : e ∈ S1 := Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have ha : a ∈ S2 := Finset.mem_erase.mpr ⟨hae,
    Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩⟩
  have hb : b ∈ S3 := Finset.mem_erase.mpr ⟨hba,
    Finset.mem_erase.mpr ⟨hbe,
      Finset.mem_erase.mpr ⟨hbc, Finset.mem_univ b⟩⟩⟩
  have hf : f ∈ S4 := Finset.mem_erase.mpr ⟨hfb,
    Finset.mem_erase.mpr ⟨hfa,
      Finset.mem_erase.mpr ⟨hfe,
        Finset.mem_erase.mpr ⟨hfc, Finset.mem_univ f⟩⟩⟩⟩
  have hzero : (∑ x ∈ S5, g x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hnf : x ≠ f := (Finset.mem_erase.mp hx).1
    have hx4 := (Finset.mem_erase.mp hx).2
    have hnb : x ≠ b := (Finset.mem_erase.mp hx4).1
    have hx3 := (Finset.mem_erase.mp hx4).2
    have hna : x ≠ a := (Finset.mem_erase.mp hx3).1
    have hx2 := (Finset.mem_erase.mp hx3).2
    have hne : x ≠ e := (Finset.mem_erase.mp hx2).1
    have hx1 := (Finset.mem_erase.mp hx2).2
    have hnc : x ≠ c := (Finset.mem_erase.mp hx1).1
    rcases hexhaust x with h | h | h | h | h <;> contradiction
  have hs1 := Finset.sum_erase_add (Finset.univ : Finset C) g hc
  have hs2 := Finset.sum_erase_add S1 g he
  have hs3 := Finset.sum_erase_add S2 g ha
  have hs4 := Finset.sum_erase_add S3 g hb
  have hs5 := Finset.sum_erase_add S4 g hf
  dsimp [S1, S2, S3, S4, S5] at *
  omega

/-- If a balanced nonnegative quotient row has the same ordinary and
two-step sums, every positive outgoing entry has reverse multiplicity one. -/
theorem reverse_eq_one_of_balanced_row_product_eq_row
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hcpos : 0 < size c)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hsum : (∑ e, Q c e * Q e c) = ∑ e, Q c e) :
    ∀ e, 0 < Q c e → Q e c = 1 := by
  have hle : ∀ e : C, Q c e ≤ Q c e * Q e c := by
    intro e
    by_cases hq : Q c e = 0
    · simp [hq]
    · have hqpos : 0 < Q c e := Nat.pos_of_ne_zero hq
      have hrpos : 0 < Q e c := by
        by_contra hr
        push Not at hr
        have hr0 : Q e c = 0 := by omega
        have hb := hbal e
        rw [hr0, mul_zero] at hb
        exact (Nat.mul_pos hcpos hqpos).ne' hb
      calc
        Q c e = Q c e * 1 := by simp
        _ ≤ Q c e * Q e c := Nat.mul_le_mul_left _ hrpos
  intro e hq
  have hrpos : 0 < Q e c := by
    have := hle e
    by_contra hr
    push Not at hr
    have hr0 : Q e c = 0 := by omega
    rw [hr0, mul_zero] at this
    omega
  by_contra hrne
  have hrlt : Q c e < Q c e * Q e c := by
    have hr2 : 1 < Q e c := by omega
    simpa using (Nat.mul_lt_mul_left hq).mpr hr2
  have hstrict := Finset.sum_lt_sum
    (fun t _ ↦ hle t) ⟨e, Finset.mem_univ e, hrlt⟩
  rw [hsum] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Finset-restricted form of `reverse_eq_one_of_balanced_row_product_eq_row`. -/
theorem reverse_eq_one_on_finset_of_balanced_product_eq_row
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hcpos : 0 < size c)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hsum : (∑ e ∈ S, Q c e * Q e c) = ∑ e ∈ S, Q c e) :
    ∀ e ∈ S, 0 < Q c e → Q e c = 1 := by
  have hle : ∀ e : C, Q c e ≤ Q c e * Q e c := by
    intro e
    by_cases hq : Q c e = 0
    · simp [hq]
    · have hqpos : 0 < Q c e := Nat.pos_of_ne_zero hq
      have hrpos : 0 < Q e c := by
        by_contra hr
        have hr0 : Q e c = 0 := by omega
        have hb := hbal e
        rw [hr0, mul_zero] at hb
        exact (Nat.mul_pos hcpos hqpos).ne' hb
      simpa using Nat.mul_le_mul_left (Q c e) hrpos
  intro e he hq
  have hrpos : 0 < Q e c := by
    have := hle e
    by_contra hr
    have hr0 : Q e c = 0 := by omega
    rw [hr0, mul_zero] at this
    omega
  by_contra hrne
  have hrlt : Q c e < Q c e * Q e c := by
    have hr2 : 1 < Q e c := by omega
    simpa using (Nat.mul_lt_mul_left hq).mpr hr2
  have hstrict := Finset.sum_lt_sum
    (fun t _ ↦ hle t) ⟨e, he, hrlt⟩
  rw [hsum] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Every zero-diagonal order-three component at the degree-six boundary has
row sum six and reverse multiplicity one on its positive support. -/
theorem degreeSix_orderThree_zeroDiagonal_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he3 : e.supp.ncard = 3)
    (hee : componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0) :
    (∑ t, componentQuotientMatrix G (secondOrderDefectGraph G) e t) = 6 ∧
      ∀ t, 0 < componentQuotientMatrix G (secondOrderDefectGraph G) e t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t e = 1 ∧
          t.supp.ncard = 3 *
            componentQuotientMatrix G (secondOrderDefectGraph G) e t := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  have hrow : (∑ t, Q e t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e e
  have hprod : (∑ t, Q e t * Q t e) = 6 := by
    simpa [Q, Matrix.mul_apply, he3] using hsq
  have hreverse := reverse_eq_one_of_balanced_row_product_eq_row
    Q (fun t ↦ t.supp.ncard) e (by rw [he3]; norm_num)
      (fun t ↦ secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e t)
      (by rw [hprod, hrow])
  refine ⟨hrow, ?_⟩
  intro t hpos
  have hte := hreverse t hpos
  change componentQuotientMatrix G (secondOrderDefectGraph G) t e = 1 at hte
  refine ⟨hte, ?_⟩
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e t
  rw [he3, hte, mul_one] at hbal
  exact hbal.symm

/-- Triangle-free defect degree two propagates across a second-order defect
edge. -/
theorem triangleFree_degree_two_of_secondOrder_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Adj x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hxmono := secondOrder_defect_local_monochromatic
    G hfree hd heven hmin hcard x
  have hxyT : (triangleFreeEdgeGraph G).Adj x y := by
    rcases hxmono with hxmono | hxmono
    · have hyMem : y ∈ triangleFreeNeighbors G x := by
        have hDmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
          ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hxy
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G x = ∅ :=
          Finset.card_eq_zero.mp hxmono.1
        simpa [hAempty] using hDmem
      simpa [triangleFreeEdgeGraph_adj] using hyMem
    · have hxzero : (triangleFreeEdgeGraph G).degree x = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hxmono.2
      omega
  rcases secondOrder_defect_local_monochromatic
      G hfree hd heven hmin hcard y with hymono | hymono
  · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact hymono.2
  · have hzero : triangleFreeNeighbors G y = ∅ :=
      Finset.card_eq_zero.mp hymono.2
    have hmem : x ∈ triangleFreeNeighbors G y := by
      simpa [triangleFreeEdgeGraph_adj] using hxyT.symm
    rw [hzero] at hmem
    exact (Finset.notMem_empty x hmem).elim

/-- Triangle-free defect degree two is constant on every reachable class of
the second-order defect graph. -/
theorem triangleFree_degree_two_of_secondOrder_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Reachable x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hwalk : Relation.ReflTransGen (secondOrderDefectGraph G).Adj x y :=
    ((secondOrderDefectGraph G).reachable_iff_reflTransGen x y).mp hxy
  have hprop : ∀ {a b : V},
      Relation.ReflTransGen (secondOrderDefectGraph G).Adj a b →
      (triangleFreeEdgeGraph G).degree a = 2 →
      (triangleFreeEdgeGraph G).degree b = 2 := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
        exact triangleFree_degree_two_of_secondOrder_adj
          G hfree hd heven hmin hcard hbc ih
  exact hprop hwalk hx

/-- A cyclic defect component belongs to the triangle-free color sector iff
one (and therefore every) vertex in it has triangle-free defect degree two. -/
theorem mem_triangleFreeCycleSector_iff_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree (u c 0) = 2 := by
  constructor
  · intro hc
    have hG : G.Adj (u c 0) (u c 1) := by
      simpa using (mem_triangleFreeCycleSector_iff G u c).mp hc 0
    have hD : (secondOrderDefectGraph G).Adj (u c 0) (u c 1) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c 0) with hmono | hmono
    · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
      exact hmono.2
    · have hm := secondOrderDefectGraph_incident_edges_monochromatic
        G hfree hd heven hmin hcard hD hD
      rcases hm with hm | hm
      · have hmem := (antipodalGraph_adj G (u c 0) (u c 1)).mp hm.1
        exact ((mem_antipodalNeighbors G (u c 0) (u c 1)).mp hmem).2.1 hG |>.elim
      · have hzero : triangleFreeNeighbors G (u c 0) = ∅ :=
          Finset.card_eq_zero.mp hmono.2
        have hmem : u c 1 ∈ triangleFreeNeighbors G (u c 0) := by
          simpa [triangleFreeEdgeGraph_adj] using hm.1
        rw [hzero] at hmem
        exact (Finset.notMem_empty _ hmem).elim
  · intro hzero
    rw [mem_triangleFreeCycleSector_iff]
    intro x
    have hcx : (secondOrderDefectGraph G).connectedComponentMk (u c x) = c := by
      apply (ConnectedComponent.mem_supp_iff c (u c x)).mp
      rw [← huRange c]
      exact ⟨x, rfl⟩
    have hc0mem : u c 0 ∈ c.supp := by
      have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
      exact heq.mp ⟨0, rfl⟩
    have hc0 : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
      (ConnectedComponent.mem_supp_iff c (u c 0)).mp hc0mem
    have hreach : (secondOrderDefectGraph G).Reachable (u c 0) (u c x) :=
      ConnectedComponent.eq.mp (hc0.trans hcx.symm)
    have hxdeg := triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach hzero
    have hD : (secondOrderDefectGraph G).Adj (u c x) (u c (x + 1)) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c x) with hmono | hmono
    · have hmem : u c (x + 1) ∈ triangleFreeNeighbors G (u c x) := by
        have hDmem : u c (x + 1) ∈
            (secondOrderDefectGraph G).neighborFinset (u c x) :=
          ((secondOrderDefectGraph G).mem_neighborFinset
            (u c x) (u c (x + 1))).mpr hD
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G (u c x) = ∅ :=
          Finset.card_eq_zero.mp hmono.1
        simpa [hAempty] using hDmem
      exact (mem_triangleFreeNeighbors G (u c x) (u c (x + 1))).mp hmem |>.1
    · have hxzero : (triangleFreeEdgeGraph G).degree (u c x) = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hmono.2
      omega

/-- The sector test may be made at any vertex of the component. -/
theorem mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) {v : V}
    (hv : v ∈ c.supp) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree v = 2 := by
  have hvMk : (secondOrderDefectGraph G).connectedComponentMk v = c :=
    (ConnectedComponent.mem_supp_iff c v).mp hv
  have hu0mem : u c 0 ∈ c.supp := by
    have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
    exact heq.mp ⟨0, rfl⟩
  have hu0Mk : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
    (ConnectedComponent.mem_supp_iff c (u c 0)).mp hu0mem
  have hreach : (secondOrderDefectGraph G).Reachable (u c 0) v :=
    ConnectedComponent.eq.mp (hu0Mk.trans hvMk.symm)
  constructor
  · intro hc
    apply triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach
    exact (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mp hc
  · intro hvdeg
    apply (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mpr
    exact triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach.symm hvdeg

/-- The vertex-colored order is exactly the sum of the orders of the
triangle-free cycle components. -/
theorem card_triangleFree_degree_two_eq_sum_sector_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    (Finset.univ.filter fun v : V =>
        (triangleFreeEdgeGraph G).degree v = 2).card =
      ∑ c ∈ triangleFreeCycleSector G u, c.supp.ncard := by
  let S := triangleFreeCycleSector G u
  let U : Finset V := S.biUnion fun c => c.supp.toFinset
  have hsets : (Finset.univ.filter fun v : V =>
      (triangleFreeEdgeGraph G).degree v = 2) = U := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U,
      Finset.mem_biUnion]
    constructor
    · intro hv
      let c := (secondOrderDefectGraph G).connectedComponentMk v
      have hvc : v ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
      refine ⟨c, ?_, Set.mem_toFinset.mpr hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c hvc).mpr hv
    · rintro ⟨c, hc, hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c
        (Set.mem_toFinset.mp hvc)).mp hc
  rw [hsets]
  dsimp [U]
  rw [Finset.card_biUnion]
  · simp [S, Set.ncard_eq_toFinset_card']
  · intro c _ e _ hce
    exact Set.disjoint_toFinset.mpr
      (pairwise_disjoint_supp_connectedComponent (secondOrderDefectGraph G) hce)

/-- At the degree-six exact boundary there are either no triangle-free defect
components or exactly one.  Weighted Cauchy--Schwarz on its quotient row
restricts the latter's order to `3, 6, 9, 12, 15`. -/
theorem degreeSix_triangleFreeCycleSector_empty_or_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard) :
    triangleFreeCycleSector G u = ∅ ∨
      ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
        triangleFreeCycleSector G u = {c} ∧
        (c.supp.ncard = 3 ∨ c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
          c.supp.ncard = 12 ∨ c.supp.ncard = 15) := by
  let S := triangleFreeCycleSector G u
  have hle : S.card ≤ 1 := degreeSix_triangleFreeCycleSector_card_le_one
    G hfree hmin hcard u hu huRange huD hr
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hzero | hone
  · left
    exact Finset.card_eq_zero.mp hzero
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    right
    refine ⟨c, hc, ?_⟩
    have hmod : c.supp.ncard % 3 = 0 := by
      have hcount := card_triangleFree_degree_two_eq_sum_sector_orders
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard
        u hu huRange huD
      have hcolor := degreeSix_secondOrder_colorOrder_mod_three
        G hfree hmin hcard
      rw [hcount] at hcolor
      have hc' : triangleFreeCycleSector G u = {c} := hc
      simpa [hc'] using hcolor
    let D := secondOrderDefectGraph G
    let Q := componentQuotientMatrix G D
    let size : D.ConnectedComponent → ℕ := fun e => e.supp.ncard
    have htotal : (∑ e : D.ConnectedComponent, size e) = 33 := by
      rw [sum_connectedComponent_supp_ncard D]
      norm_num at hcard ⊢
      exact hcard
    have hrow : (∑ e : D.ConnectedComponent, Q c e) = 6 := by
      exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c
    have hdiag : Q c c = 2 :=
      triangleFreeCycleSector_diagonalQuotient_eq_two G hfree
        (d := 6) (by norm_num) (by norm_num) hmin hcard
        u hu huRange huD hr (by
          have hcmem : c ∈ S := by rw [hc]; simp
          simpa [S] using hcmem)
    have hbal : ∀ e : D.ConnectedComponent,
        size c * Q c e = size e * Q e c := by
      intro e
      exact secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c e
    have hsq : (∑ e : D.ConnectedComponent, Q c e * Q e c) = size c + 3 := by
      have h := secondOrder_componentQuotientMatrix_sq_apply
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c c
      simpa [Matrix.mul_apply, Q, size, D, Nat.add_comm] using h
    have hineq := degreeSix_singleton_incidence_cauchy
      Q size c c.nonempty_supp.ncard_pos htotal hrow hdiag hbal hsq
    dsimp [size] at hineq
    have hle : c.supp.ncard ≤ 15 := by nlinarith
    omega

/-- A triangle-free-colored defect component cannot have order three: its
three rim edges would form a triangle in the triangle-free edge graph. -/
theorem triangleFreeCycleSector_component_order_ne_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c ∈ triangleFreeCycleSector G u) :
    c.supp.ncard ≠ 3 := by
  intro hthree
  have hG := (mem_triangleFreeCycleSector_iff G u c).mp hc
  have hTF : ∀ x : ZMod c.supp.ncard,
      (triangleFreeEdgeGraph G).Adj (u c x) (u c (x + 1)) := by
    intro x
    have hD : (secondOrderDefectGraph G).Adj (u c x) (u c (x + 1)) := by
      rw [← SimpleGraph.mem_neighborFinset, huD]
      simp
    rcases hD with hA | hT
    · have hnG := (mem_antipodalNeighbors G (u c x) (u c (x + 1))).mp hA
      exact (hnG.2.1 (hG x)).elim
    · exact hT
  have h01 := hTF (0 : ZMod c.supp.ncard)
  have h1m := hTF (1 : ZMod c.supp.ncard)
  have hm0 := hTF (-1 : ZMod c.supp.ncard)
  have h01' : (triangleFreeEdgeGraph G).Adj (u c 0) (u c 1) := by
    simpa using h01
  have h1m' : (triangleFreeEdgeGraph G).Adj (u c 1) (u c (-1)) := by
    have hind : (1 + 1 : ZMod c.supp.ncard) = -1 := by
      have h3zero : ((3 : ℕ) : ZMod c.supp.ncard) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hthree.symm ▸ dvd_refl 3
      linear_combination h3zero
    rw [hind] at h1m
    exact h1m
  have hm0' : (triangleFreeEdgeGraph G).Adj (u c (-1)) (u c 0) := by
    simpa using hm0
  exact triangleFreeEdgeGraph_not_triangle G h01' h1m' hm0'

/-- In the singleton color-sector branch, its unique component has one of
the four surviving orders and its complete off-diagonal quotient row is
pinned by the degree-six row and square identities. -/
theorem degreeSix_singleton_component_quotient_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c}) :
    (c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨ c.supp.ncard = 12 ∨
      c.supp.ncard = 15) ∧
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 ∧
    (∑ e ∈ (Finset.univ.erase c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 4 ∧
    (∑ e ∈ (Finset.univ.erase c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) =
      c.supp.ncard - 1 ∧
    ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard * componentQuotientMatrix G (secondOrderDefectGraph G) c e =
        e.supp.ncard * componentQuotientMatrix G
          (secondOrderDefectGraph G) e c := by
  have hc : c ∈ triangleFreeCycleSector G u := by rw [hsector]; simp
  have hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 :=
    triangleFreeCycleSector_diagonalQuotient_eq_two G hfree
      (d := 6) (by norm_num) (by norm_num) hmin (by norm_num at hcard ⊢; exact hcard)
      u hu huRange huD hr hc
  have hrow : (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hsq : (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) =
      c.supp.ncard + 3 := by
    have h := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c c
    simpa [Matrix.mul_apply, Nat.add_comm] using h
  have hord := degreeSix_triangleFreeCycleSector_empty_or_singleton
    G hfree hmin (by norm_num at hcard ⊢; exact hcard)
      u hu huRange huD hr
  have hord0 : c.supp.ncard = 3 ∨ c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
      c.supp.ncard = 12 ∨ c.supp.ncard = 15 := by
    rcases hord with hempty | ⟨e, he, heord⟩
    · rw [hsector] at hempty
      simpa using hempty
    · have hec : e = c := by
        have : c = e := by simpa [hsector] using he
        exact this.symm
      simpa [hec] using heord
  have hne3 := triangleFreeCycleSector_component_order_ne_three
    G u huD c hc
  have hordc : c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
      c.supp.ncard = 12 ∨ c.supp.ncard = 15 := by
    omega
  have hcuniv : c ∈ (Finset.univ :
      Finset (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_univ c
  have hrowErase := Finset.sum_erase_add
    (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
      (fun e ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c e) hcuniv
  have hsqErase := Finset.sum_erase_add
    (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
      (fun e ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) hcuniv
  refine ⟨hordc, hdiag, ?_, ?_, ?_⟩
  · omega
  · rw [hdiag] at hsqErase
    omega
  · intro e
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c e

/-- In the order-nine singleton branch the two high-multiplicity alternatives
from the abstract row trichotomy violate an off-diagonal square equation.
Hence an order-three contact is forced. -/
theorem degreeSix_orderNine_singleton_exists_orderThree_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc9 : c.supp.ncard = 9) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 3 := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  obtain ⟨_, hdiag, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  change Q c c = 2 at hdiag
  change (∑ t ∈ (Finset.univ.erase c), Q c t) = 4 at hrow
  have htri := degreeSix_orderNine_singleton_contact_trichotomy
    Q (fun t ↦ t.supp.ncard) c hc9
      (by simpa [hcard] using
        (sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)))
      hr hrow (by simpa [hc9] using hprod) hbal
      (fun e hndvd ↦ secondOrder_componentQuotientMatrix_le_one_of_not_dvd
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) c e
          (by simpa [hc9] using hndvd))
  rcases htri with hcontact | hlarge | hdouble
  · exact hcontact
  · obtain ⟨e, hec, he18, hce, hecQ⟩ := hlarge
    exfalso
    let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
      (Finset.univ.erase c).erase e
    have heMem : e ∈ (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
    have hrowSplit := Finset.sum_erase_add
      (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q c) heMem
    have hrowS : (∑ t ∈ S, Q c t) = 0 := by
      dsimp [S]
      change Q c e = 4 at hce
      omega
    have hzero : ∀ t ∈ S, Q c t = 0 := by
      intro t ht
      have hle : Q c t ≤ ∑ x ∈ S, Q c x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht
      omega
    have hcMem : c ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
    have hsq := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c e
    have hsqSum : (∑ t, Q c t * Q t e) = 18 := by
      simpa [Q, Matrix.mul_apply, hec.symm, he18] using hsq
    have hsqSum' : (∑ t ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent), Q c t * Q t e) = 18 := by
      simpa using hsqSum
    have hsqC := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t e) hcMem
    have hsqE := Finset.sum_erase_add
      (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t e) heMem
    have hrestZero : (∑ t ∈ S, Q c t * Q t e) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [hzero t ht]
    rw [hsqSum'] at hsqC
    rw [hrestZero] at hsqE
    change Q c e = 4 at hce
    rw [hdiag, hce] at hsqC
    rw [hce] at hsqE
    omega
  · obtain ⟨e, f, hec, hfc, hef, he9, hf9,
      hce, hecQ, hcfQ, hfcQ⟩ := hdouble
    exfalso
    let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
      ((Finset.univ.erase c).erase e).erase f
    have heMem : e ∈ (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
    have hfMem : f ∈ ((Finset.univ.erase c).erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hef.symm,
        Finset.mem_erase.mpr ⟨hfc, Finset.mem_univ f⟩⟩
    have hrowE := Finset.sum_erase_add
      (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q c) heMem
    have hrowF := Finset.sum_erase_add
      ((Finset.univ.erase c).erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q c) hfMem
    have hrowS : (∑ t ∈ S, Q c t) = 0 := by
      dsimp [S]
      change Q c e = 2 at hce
      change Q c f = 2 at hcfQ
      omega
    have hzero : ∀ t ∈ S, Q c t = 0 := by
      intro t ht
      have hle : Q c t ≤ ∑ x ∈ S, Q c x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht
      omega
    have hcMem : c ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
    have hsq := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c e
    have hsqSum : (∑ t, Q c t * Q t e) = 9 := by
      simpa [Q, Matrix.mul_apply, hec.symm, he9] using hsq
    have hsqSum' : (∑ t ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent), Q c t * Q t e) = 9 := by
      simpa using hsqSum
    have hsqC := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t e) hcMem
    have hsqE := Finset.sum_erase_add
      (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t e) heMem
    have hsqF := Finset.sum_erase_add
      ((Finset.univ.erase c).erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t e) hfMem
    have hrestZero : (∑ t ∈ S, Q c t * Q t e) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [hzero t ht]
    rw [hsqSum'] at hsqC
    rw [hrestZero] at hsqF
    change Q c e = 2 at hce
    change Q c f = 2 at hcfQ
    rw [hdiag, hce] at hsqC
    rw [hce] at hsqE
    rw [hcfQ] at hsqF
    omega

/-- The forced order-three contact in the order-nine branch has zero
diagonal and a completely pinned residual row of mass three. -/
theorem degreeSix_orderNine_singleton_orderThree_contact_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc9 : c.supp.ncard = 9) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0 ∧
      (∑ t ∈ (Finset.univ.erase e).erase c,
        componentQuotientMatrix G (secondOrderDefectGraph G) e t) = 3 ∧
      ∀ t : (secondOrderDefectGraph G).ConnectedComponent,
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) e t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t e = 1 ∧
          t.supp.ncard = 3 *
            componentQuotientMatrix G (secondOrderDefectGraph G) e t := by
  obtain ⟨e, hec, he3, hce, hecQ⟩ :=
    degreeSix_orderNine_singleton_exists_orderThree_contact
      G hfree hmin hcard u hu huRange huD hr c hsector hc9
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  have hdiagc : Q c c = 2 := by
    obtain ⟨_, hdiag, _, _, _⟩ := degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
    exact hdiag
  have hediag : Q e e = 0 := by
    rcases oddComponent_diagonalQuotient_eq_zero_or_two
      G hfree (d := 6) (r := e.supp.ncard)
        (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) (hr e)
        (by rw [he3]; norm_num) e (u e) (hu e) (huRange e) (huD e) with
      hzero | htwo
    · exact hzero
    · have hsq := secondOrder_componentQuotientMatrix_sq_apply
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) c e
      have hsum : (∑ t, Q c t * Q t e) = 3 := by
        simpa [Q, Matrix.mul_apply, hec.symm, he3] using hsq
      have hlower := two_distinct_terms_le_sum
        (fun t ↦ Q c t * Q t e) hec.symm
      change Q c e = 1 at hce
      change Q e c = 3 at hecQ
      change Q e e = 2 at htwo
      rw [hdiagc, hce, htwo, hsum] at hlower
      omega
  have hrowe : (∑ t, Q e t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e
  have hremaining : (∑ t ∈ (Finset.univ.erase e).erase c, Q e t) = 3 := by
    have heMem : e ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ e
    have hcMem : c ∈ (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hec.symm, Finset.mem_univ c⟩
    have hsplitE := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q e) heMem
    have hsplitC := Finset.sum_erase_add
      (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q e) hcMem
    have hrowe' : (∑ t ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent), Q e t) = 6 := by
      simpa using hrowe
    change Q e c = 3 at hecQ
    omega
  have hsqe := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e e
  have hprode : (∑ t, Q e t * Q t e) = 6 := by
    simpa [Q, Matrix.mul_apply, he3] using hsqe
  have hreverse := reverse_eq_one_of_balanced_row_product_eq_row
    Q (fun t ↦ t.supp.ncard) e (by rw [he3]; norm_num)
      (fun t ↦ secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e t)
      (by rw [hprode, hrowe])
  refine ⟨e, hec, he3, hce, hecQ, hediag, hremaining, ?_⟩
  intro t hpos
  have hte := hreverse t hpos
  refine ⟨hte, ?_⟩
  have hbt := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e t
  change e.supp.ncard * Q e t = t.supp.ncard * Q t e at hbt
  rw [he3, hte, mul_one] at hbt
  exact hbt.symm

/-- The order-nine singleton branch is impossible. -/
theorem false_of_degreeSix_orderNine_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc9 : c.supp.ncard = 9) : False := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  obtain ⟨e, hec, he3, hce, hecQ, hee, herem, heprofile⟩ :=
    degreeSix_orderNine_singleton_orderThree_contact_profile
      G hfree hmin hcard u hu huRange huD hr c hsector hc9
  by_cases hother : ∃ f, f ≠ c ∧ f ≠ e ∧ f.supp.ncard = 3 ∧ Q c f ≠ 0
  · obtain ⟨f, hfc, hfe, hf3, hqf⟩ := hother
    have hbound := degreeSix_orderNine_two_orderThree_targets_le_one
      G hfree hmin hcard u hu huRange huD c e f hc9 he3 hf3
        hfe.symm
    change Q c e + Q c f ≤ 1 at hbound
    change Q c e = 1 at hce
    omega
  have hnoOther : ∀ f, f ≠ c → f ≠ e → f.supp.ncard = 3 → Q c f = 0 := by
    intro f hfc hfe hf3
    by_contra hq
    exact hother ⟨f, hfc, hfe, hf3, hq⟩
  obtain ⟨_, hcc, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  have hperiod : ∀ t, ¬ 9 ∣ t.supp.ncard → Q c t ≤ 1 := by
    intro t hndvd
    exact secondOrder_componentQuotientMatrix_le_one_of_not_dvd
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c t (by simpa [hc9] using hndvd)
  obtain ⟨a, b, f, hac, hae, hbc, hbe, hba, hfc, hfe, hfa, hfb,
      ha9, hb9, hf3, hca, hacQ, hcb, hbcQ, hcf, hexhaust⟩ :=
    degreeSix_orderNine_single_contact_shape Q (fun t ↦ t.supp.ncard) c e
      hec hc9 he3
      (by simpa [hcard] using
        (sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)))
      hr hrow (by simpa [hc9] using hprod) hbal hperiod hce hecQ hnoOther
  have hsumE := sum_eq_five_of_exhaust (Q e) c e a b f
    hec hac hae hbc hbe hba hfc hfe hfa hfb hexhaust
  have hrowE : (∑ t, Q e t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e
  have herow : Q e a + Q e b + Q e f = 3 := by
    change Q e c = 3 at hecQ
    change Q e e = 0 at hee
    omega
  have hsqGraph := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) c e
  have hsqSum : (∑ t, Q c t * Q t e) = 3 := by
    have hceNe : c ≠ e := fun h ↦ hec h.symm
    simpa [Q, Matrix.mul_apply, hceNe, he3] using hsqGraph
  have hsqExpand := sum_eq_five_of_exhaust (fun t ↦ Q c t * Q t e)
    c e a b f hec hac hae hbc hbe hba hfc hfe hfa hfb hexhaust
  have hsqce : Q c c * Q c e + Q c e * Q e e +
      Q c a * Q a e + Q c b * Q b e + Q c f * Q f e = 3 := by omega
  have hea : Q e a = 0 := by
    by_contra hne
    have haeQ := (heprofile a (Nat.pos_of_ne_zero hne)).1
    change Q a e = 1 at haeQ
    change Q c c = 2 at hcc
    change Q c e = 1 at hce
    change Q e e = 0 at hee
    change Q c a = 2 at hca
    change Q c b = 1 at hcb
    change Q c f = 0 at hcf
    rw [hcc, hce, hee, hca, hcb, hcf, haeQ] at hsqce
    omega
  have heb : Q e b = 3 := by
    by_cases hzero : Q e b = 0
    · have hefQ : Q e f = 3 := by omega
      have hpos : 0 < Q e f := by rw [hefQ]; norm_num
      have hpos' : 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) e f := by exact hpos
      have hsize := (heprofile f hpos').2
      change f.supp.ncard = 3 * Q e f at hsize
      rw [hf3, hefQ] at hsize
      norm_num at hsize
    · have hsize := (heprofile b (Nat.pos_of_ne_zero hzero)).2
      change b.supp.ncard = 3 * Q e b at hsize
      rw [hb9] at hsize
      omega
  have hef : Q e f = 0 := by omega
  have hfeQ : Q f e = 0 := by
    have hbale := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e f
    change e.supp.ncard * Q e f = f.supp.ncard * Q f e at hbale
    rw [he3, hf3, hef] at hbale
    omega
  have hsumF := sum_eq_five_of_exhaust (Q f) c e a b f
    hec hac hae hbc hbe hba hfc hfe hfa hfb hexhaust
  have hrowF : (∑ t, Q f t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) f
  have hfrowFull : Q f c + Q f e + Q f a + Q f b + Q f f = 6 := by omega
  have hdiagCases := oddComponent_diagonalQuotient_eq_zero_or_two
    G hfree (d := 6) (r := f.supp.ncard)
      (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (hr f)
      (by rw [hf3]; norm_num) f (u f) (hu f) (huRange f) (huD f)
  have hbalF : ∀ t, f.supp.ncard * Q f t = t.supp.ncard * Q t f := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) f t
  have hfcQ : Q f c = 0 := by
    have hb := hbalF c
    change Q c f = 0 at hcf
    rw [hf3, hc9, hcf] at hb
    omega
  have hff : Q f f = 0 :=
    degreeSix_orderNine_shape_unused_orderThree_diagonal_zero
      Q (fun t ↦ t.supp.ncard) c e a b f he3 ha9 hb9 hf3 hfcQ hfeQ
        hfrowFull hbalF hdiagCases
  obtain ⟨_, hfprofile⟩ := degreeSix_orderThree_zeroDiagonal_profile
    G hfree hmin hcard f hf3 hff
  have hfrow : Q f e + Q f a + Q f b = 6 := by
    rw [hfcQ, hfeQ, hff] at hfrowFull
    omega
  have hgroup := degreeSix_orderNine_two_orderThree_targets_le_one
    G hfree hmin hcard u hu huRange huD b e f hb9 he3 hf3
      hfe.symm
  exact false_of_degreeSix_orderNine_single_contact_shape
    Q (fun t ↦ t.supp.ncard) c e a b f hec hac hae hbc hbe hba
      hfc hfe hfa hfb hc9 he3 ha9 hb9 hf3 hcc hce hca hcb hcf
      hecQ hee herow heprofile hfcQ hff hfrow hfprofile hsqce hgroup

/-- Graph wrapper for the pointwise order-twelve positive-contact class. -/
theorem degreeSix_orderTwelve_singleton_positive_contact_class
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c t : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc12 : c.supp.ncard = 12) (htc : t ≠ c)
    (hqpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c t) :
    (t.supp.ncard = 3 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 4) ∨
    (t.supp.ncard = 4 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 3) ∨
    (t.supp.ncard = 6 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 2) ∨
    (t.supp.ncard = 12 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 1) ∨
    (t.supp.ncard = 12 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 2) ∨
    (t.supp.ncard = 12 ∧ componentQuotientMatrix G (secondOrderDefectGraph G) c t = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) t c = 3) := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent := Finset.univ.erase c
  have htS : t ∈ S := Finset.mem_erase.mpr ⟨htc, Finset.mem_univ t⟩
  obtain ⟨_, _, hrow, hprod, hbal⟩ := degreeSix_singleton_component_quotient_row
    G hfree hmin hcard u hu huRange huD hr c hsector
  have hqle : Q c t ≤ 4 := by
    have hsingle : Q c t ≤ ∑ x ∈ S, Q c x :=
      Finset.single_le_sum (f := Q c) (fun _ _ ↦ Nat.zero_le _) htS
    simpa [S] using hsingle.trans_eq hrow
  have hprodle : Q c t * Q t c ≤ 11 := by
    have hsingle : Q c t * Q t c ≤ ∑ x ∈ S, Q c x * Q x c :=
      Finset.single_le_sum (f := fun x ↦ Q c x * Q x c)
        (fun _ _ ↦ Nat.zero_le _) htS
    have hp : (∑ x ∈ S, Q c x * Q x c) = 11 := by
      simpa [S, hc12] using hprod
    omega
  have htotalS : (∑ x ∈ S, x.supp.ncard) = 21 := by
    have htotal : (∑ x : (secondOrderDefectGraph G).ConnectedComponent,
        x.supp.ncard) = 33 := by
      simpa [hcard] using sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
    have hcMem : c ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
        (fun x ↦ x.supp.ncard) hcMem
    dsimp [S]
    omega
  have hsizele : t.supp.ncard ≤ 21 := by
    have hsingle : t.supp.ncard ≤ ∑ x ∈ S, x.supp.ncard :=
      Finset.single_le_sum (f := fun x ↦ x.supp.ncard)
        (fun _ _ ↦ Nat.zero_le _) htS
    omega
  exact degreeSix_orderTwelve_positive_contact_class Q (fun x ↦ x.supp.ncard)
    c t hc12 htc (hr t) hsizele hqpos hqle hprodle (hbal t)
      (fun hndvd ↦ secondOrder_componentQuotientMatrix_le_one_of_not_dvd
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) c t
          (by simpa [hc12] using hndvd))

set_option maxHeartbeats 2000000 in
/-- The order-twelve singleton row has exactly one of its two feasible
contact-count patterns. -/
theorem degreeSix_orderTwelve_singleton_contact_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc12 : c.supp.ncard = 12) :
    let S := Finset.univ.erase c
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let n3 := (S.filter fun t ↦ t.supp.ncard = 3 ∧ Q c t = 1).card
    let n4 := (S.filter fun t ↦ t.supp.ncard = 4 ∧ Q c t = 1).card
    let n6 := (S.filter fun t ↦ t.supp.ncard = 6 ∧ Q c t = 1).card
    let n121 := (S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 1).card
    let n122 := (S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 2).card
    let n123 := (S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 3).card
    (n3 = 0 ∧ n4 = 0 ∧ n6 = 1 ∧ n121 = 0 ∧ n122 = 0 ∧ n123 = 1) ∨
    (n3 = 0 ∧ n4 = 3 ∧ n6 = 1 ∧ n121 = 0 ∧ n122 = 0 ∧ n123 = 0) := by
  dsimp
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent := Finset.univ.erase c
  obtain ⟨_, _, hrow, hprod, hbal⟩ := degreeSix_singleton_component_quotient_row
    G hfree hmin hcard u hu huRange huD hr c hsector
  have htotalAll : (∑ t : (secondOrderDefectGraph G).ConnectedComponent,
      t.supp.ncard) = 33 := by
    simpa [hcard] using sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
  have hcMem : c ∈ (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
  have hsplitSize := Finset.sum_erase_add
    (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ t.supp.ncard) hcMem
  have htotalS : (∑ t ∈ S, t.supp.ncard) = 21 := by
    dsimp [S]
    omega
  have hclass : ∀ t ∈ S, Q c t = 0 ∨
      (t.supp.ncard = 3 ∧ Q c t = 1 ∧ Q t c = 4) ∨
      (t.supp.ncard = 4 ∧ Q c t = 1 ∧ Q t c = 3) ∨
      (t.supp.ncard = 6 ∧ Q c t = 1 ∧ Q t c = 2) ∨
      (t.supp.ncard = 12 ∧ Q c t = 1 ∧ Q t c = 1) ∨
      (t.supp.ncard = 12 ∧ Q c t = 2 ∧ Q t c = 2) ∨
      (t.supp.ncard = 12 ∧ Q c t = 3 ∧ Q t c = 3) := by
    intro t ht
    by_cases hq : Q c t = 0
    · exact Or.inl hq
    · have htc : t ≠ c := (Finset.mem_erase.mp ht).1
      have hqpos : 0 < Q c t := Nat.pos_of_ne_zero hq
      have hqle : Q c t ≤ 4 := by
        have hsingle : Q c t ≤ ∑ x ∈ S, Q c x :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht
        simpa [S] using hsingle.trans_eq hrow
      have hprodle : Q c t * Q t c ≤ 11 := by
        have hsingle : Q c t * Q t c ≤ ∑ x ∈ S, Q c x * Q x c :=
          Finset.single_le_sum (f := fun x ↦ Q c x * Q x c)
            (fun _ _ ↦ Nat.zero_le _) ht
        have hp : (∑ x ∈ S, Q c x * Q x c) = 11 := by
          simpa [S, hc12] using hprod
        omega
      have hsizele : t.supp.ncard ≤ 21 := by
        have hsingle : t.supp.ncard ≤ ∑ x ∈ S, x.supp.ncard :=
          Finset.single_le_sum (f := fun x ↦ x.supp.ncard)
            (fun _ _ ↦ Nat.zero_le _) ht
        omega
      exact Or.inr (degreeSix_orderTwelve_positive_contact_class
        Q (fun x ↦ x.supp.ncard) c t hc12 htc (hr t) hsizele hqpos hqle
          hprodle (hbal t) (fun hndvd ↦
            secondOrder_componentQuotientMatrix_le_one_of_not_dvd
              G hfree (d := 6) (by norm_num) (by norm_num) hmin
                (by norm_num at hcard ⊢; exact hcard) c t
                (by simpa [hc12] using hndvd)))
  have hagg := degreeSix_orderTwelve_contact_aggregate_equations
    S (Q c) (fun t ↦ Q t c) (fun t ↦ t.supp.ncard) hclass
  have hgap := contact_used_order_eq_total_or_le_eighteen
    S (Q c) (fun t ↦ t.supp.ncard) htotalS (fun t _ ↦ hr t)
  have hcounts := degreeSix_orderTwelve_contact_count_classifier
    ((S.filter fun t ↦ t.supp.ncard = 3 ∧ Q c t = 1).card)
    ((S.filter fun t ↦ t.supp.ncard = 4 ∧ Q c t = 1).card)
    ((S.filter fun t ↦ t.supp.ncard = 6 ∧ Q c t = 1).card)
    ((S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 1).card)
    ((S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 2).card)
    ((S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 3).card)
    (∑ t ∈ S, if Q c t = 0 then 0 else t.supp.ncard)
    (by simpa [Q, S] using hagg.1.symm.trans hrow)
    (by
      have hp : (∑ t ∈ S, Q c t * Q t c) = 11 := by
        simpa [S, hc12] using hprod
      exact hagg.2.1.symm.trans hp)
    hagg.2.2 hgap
  rcases hcounts with h | h
  · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · exact Or.inr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Three order-four contacts in an order-twelve row contradict grouped
periodicity. -/
theorem false_of_degreeSix_orderTwelve_three_orderFour_contacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc12 : c.supp.ncard = 12)
    (hthree : ((Finset.univ.erase c).filter fun t ↦
      t.supp.ncard = 4 ∧
        componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1).card = 3) : False := by
  let A := (Finset.univ.erase c).filter fun t ↦
    t.supp.ncard = 4 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1
  have hcardA : A.card = 3 := hthree
  have hlt : 1 < A.card := by omega
  obtain ⟨e, heA, f, hfA, hef⟩ := Finset.one_lt_card.mp hlt
  have heData := (Finset.mem_filter.mp heA).2
  have hfData := (Finset.mem_filter.mp hfA).2
  have hbound := degreeSix_orderTwelve_two_orderFour_targets_le_one
    G hfree hmin hcard u hu huRange huD c e f hc12
      heData.1 hfData.1 hef
  rw [heData.2, hfData.2] at hbound
  omega

set_option maxHeartbeats 2000000 in
/-- The order-twelve singleton branch is impossible. -/
theorem false_of_degreeSix_orderTwelve_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc12 : c.supp.ncard = 12) : False := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent := Finset.univ.erase c
  have hcounts := degreeSix_orderTwelve_singleton_contact_counts
    G hfree hmin hcard u hu huRange huD hr c hsector hc12
  dsimp at hcounts
  rcases hcounts with hsparse | hdense
  · rcases hsparse with ⟨hn3, hn4, hn6, hn121, hn122, hn123⟩
    let A := S.filter fun t ↦ t.supp.ncard = 12 ∧ Q c t = 3
    let D := S.filter fun t ↦ t.supp.ncard = 6 ∧ Q c t = 1
    have hAcard : A.card = 1 := by simpa [A, S, Q] using hn123
    have hDcard : D.card = 1 := by simpa [D, S, Q] using hn6
    obtain ⟨a, haSet⟩ := Finset.card_eq_one.mp hAcard
    obtain ⟨d, hdSet⟩ := Finset.card_eq_one.mp hDcard
    have haMem : a ∈ A := by rw [haSet]; simp
    have hdMem : d ∈ D := by rw [hdSet]; simp
    have haFilter := Finset.mem_filter.mp haMem
    have hdFilter := Finset.mem_filter.mp hdMem
    have hac : a ≠ c := (Finset.mem_erase.mp haFilter.1).1
    have hdc : d ≠ c := (Finset.mem_erase.mp hdFilter.1).1
    have ha12 : a.supp.ncard = 12 := haFilter.2.1
    have hca : Q c a = 3 := haFilter.2.2
    have hd6 : d.supp.ncard = 6 := hdFilter.2.1
    have hcd : Q c d = 1 := hdFilter.2.2
    have had : a ≠ d := by intro h; subst d; omega
    have hsupport : ∀ t, t ≠ c → t ≠ a → t ≠ d → Q c t = 0 := by
      intro t htc hta htd
      by_contra hq
      have hclass := degreeSix_orderTwelve_singleton_positive_contact_class
        G hfree hmin hcard u hu huRange huD hr c t hsector hc12 htc
          (Nat.pos_of_ne_zero hq)
      have htS : t ∈ S := Finset.mem_erase.mpr ⟨htc, Finset.mem_univ t⟩
      rcases hclass with h3 | h4 | h6 | h121 | h122 | h123
      · have hm : t ∈ S.filter (fun x ↦ x.supp.ncard = 3 ∧ Q c x = 1) :=
          Finset.mem_filter.mpr ⟨htS, h3.1, h3.2.1⟩
        have hp := Finset.card_pos.mpr ⟨t, hm⟩
        have hz : (S.filter fun x ↦ x.supp.ncard = 3 ∧ Q c x = 1).card = 0 := by
          simpa [S, Q] using hn3
        omega
      · have hm : t ∈ S.filter (fun x ↦ x.supp.ncard = 4 ∧ Q c x = 1) :=
          Finset.mem_filter.mpr ⟨htS, h4.1, h4.2.1⟩
        have hp := Finset.card_pos.mpr ⟨t, hm⟩
        have hz : (S.filter fun x ↦ x.supp.ncard = 4 ∧ Q c x = 1).card = 0 := by
          simpa [S, Q] using hn4
        omega
      · have hm : t ∈ D := Finset.mem_filter.mpr ⟨htS, h6.1, h6.2.1⟩
        rw [hdSet] at hm
        simp at hm
        exact htd hm
      · have hm : t ∈ S.filter (fun x ↦ x.supp.ncard = 12 ∧ Q c x = 1) :=
          Finset.mem_filter.mpr ⟨htS, h121.1, h121.2.1⟩
        have hp := Finset.card_pos.mpr ⟨t, hm⟩
        have hz : (S.filter fun x ↦ x.supp.ncard = 12 ∧ Q c x = 1).card = 0 := by
          simpa [S, Q] using hn121
        omega
      · have hm : t ∈ S.filter (fun x ↦ x.supp.ncard = 12 ∧ Q c x = 2) :=
          Finset.mem_filter.mpr ⟨htS, h122.1, h122.2.1⟩
        have hp := Finset.card_pos.mpr ⟨t, hm⟩
        have hz : (S.filter fun x ↦ x.supp.ncard = 12 ∧ Q c x = 2).card = 0 := by
          simpa [S, Q] using hn122
        omega
      · have hm : t ∈ A := Finset.mem_filter.mpr ⟨htS, h123.1, h123.2.1⟩
        rw [haSet] at hm
        simp at hm
        exact hta hm
    obtain ⟨_, hcc, _, _, _⟩ := degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
    let R : Finset (secondOrderDefectGraph G).ConnectedComponent :=
      ((Finset.univ.erase c).erase a).erase d
    have haIn : a ∈ (Finset.univ.erase c : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩
    have hdIn : d ∈ ((Finset.univ.erase c).erase a : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨had.symm,
        Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩⟩
    have hcIn : c ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
    have hsqAgraph := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c a
    have hsqA : (∑ t, Q c t * Q t a) = 12 := by
      simpa [Q, Matrix.mul_apply, hac.symm, ha12] using hsqAgraph
    have hsqDgraph := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c d
    have hsqD : (∑ t, Q c t * Q t d) = 6 := by
      simpa [Q, Matrix.mul_apply, hdc.symm, hd6] using hsqDgraph
    have hzeroA : (∑ t ∈ R, Q c t * Q t a) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have htd' := (Finset.mem_erase.mp ht).1
      have ht2 := (Finset.mem_erase.mp ht).2
      have hta' := (Finset.mem_erase.mp ht2).1
      have htc' := (Finset.mem_erase.mp (Finset.mem_erase.mp ht2).2).1
      simp [hsupport t htc' hta' htd']
    have hzeroD : (∑ t ∈ R, Q c t * Q t d) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have htd' := (Finset.mem_erase.mp ht).1
      have ht2 := (Finset.mem_erase.mp ht).2
      have hta' := (Finset.mem_erase.mp ht2).1
      have htc' := (Finset.mem_erase.mp (Finset.mem_erase.mp ht2).2).1
      simp [hsupport t htc' hta' htd']
    have hsAc := Finset.sum_erase_add (Finset.univ : Finset _)
      (fun t ↦ Q c t * Q t a) hcIn
    have hsAa := Finset.sum_erase_add (Finset.univ.erase c)
      (fun t ↦ Q c t * Q t a) haIn
    have hsAd := Finset.sum_erase_add ((Finset.univ.erase c).erase a)
      (fun t ↦ Q c t * Q t a) hdIn
    have hsDc := Finset.sum_erase_add (Finset.univ : Finset _)
      (fun t ↦ Q c t * Q t d) hcIn
    have hsDa := Finset.sum_erase_add (Finset.univ.erase c)
      (fun t ↦ Q c t * Q t d) haIn
    have hsDd := Finset.sum_erase_add ((Finset.univ.erase c).erase a)
      (fun t ↦ Q c t * Q t d) hdIn
    have hsqa : Q c c * Q c a + Q c a * Q a a + Q c d * Q d a = 12 := by
      dsimp [R] at hzeroA
      omega
    have hsqd : Q c c * Q c d + Q c a * Q a d + Q c d * Q d d = 6 := by
      dsimp [R] at hzeroD
      omega
    have hbalDA := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) d a
    have hdd := degreeSix_orderSix_component_diagonal_le_three
      G hfree hmin hcard d (u d) (hu d) (huRange d) (huD d) hd6
    exact false_of_degreeSix_orderTwelve_sparse_square Q
      (fun t ↦ t.supp.ncard) c a d hc12 ha12 hd6 hcc hca hcd
        hbalDA hsqa hsqd hdd
  · exact false_of_degreeSix_orderTwelve_three_orderFour_contacts
      G hfree hmin hcard u hu huRange huD c hc12 hdense.2.1

/-- Graph instantiation of the forced order-three contact in the
order-fifteen singleton branch. -/
theorem degreeSix_orderFifteen_singleton_exists_orderThree_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc15 : c.supp.ncard = 15) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 5 := by
  obtain ⟨_, _, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  apply degreeSix_orderFifteen_singleton_contact
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun e ↦ e.supp.ncard) c hc15
  · simpa [hcard] using
      (sum_connectedComponent_supp_ncard (secondOrderDefectGraph G))
  · exact hr
  · exact hrow
  · simpa [hc15] using hprod
  · exact hbal
  · intro e hndvd
    exact secondOrder_componentQuotientMatrix_le_one_of_not_dvd
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c e (by simpa [hc15] using hndvd)

/-- The order-three target forced by an order-fifteen singleton spends five
of its six row units back toward the singleton.  Its diagonal is therefore
zero and its final row unit forces a second, distinct order-three target. -/
theorem degreeSix_orderFifteen_singleton_exists_two_orderThree_contacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc15 : c.supp.ncard = 15) :
    ∃ e f : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ f ≠ c ∧ f ≠ e ∧ e.supp.ncard = 3 ∧ f.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 5 := by
  obtain ⟨e, hec, he3, hce, hecQ⟩ :=
    degreeSix_orderFifteen_singleton_exists_orderThree_contact
      G hfree hmin hcard u hu huRange huD hr c hsector hc15
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  have hrowe : (∑ t, Q e t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e
  have hediag : Q e e = 0 := by
    rcases oddComponent_diagonalQuotient_eq_zero_or_two
      G hfree (d := 6) (r := e.supp.ncard)
        (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) (hr e)
        (by rw [he3]; norm_num) e (u e) (hu e) (huRange e) (huD e) with
      hzero | htwo
    · exact hzero
    · have heMem : e ∈ (Finset.univ : Finset
          (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ e
      have hcMem : c ∈ (Finset.univ.erase e : Finset
          (secondOrderDefectGraph G).ConnectedComponent) :=
        Finset.mem_erase.mpr ⟨hec.symm, Finset.mem_univ c⟩
      have hsplitE := Finset.sum_erase_add
        (Finset.univ : Finset
          (secondOrderDefectGraph G).ConnectedComponent) (Q e) heMem
      have hsplitC := Finset.sum_erase_add
        (Finset.univ.erase e : Finset
          (secondOrderDefectGraph G).ConnectedComponent) (Q e) hcMem
      have hrowe' : (∑ t ∈ (Finset.univ : Finset
          (secondOrderDefectGraph G).ConnectedComponent), Q e t) = 6 := by
        simpa using hrowe
      change Q e e = 2 at htwo
      change Q e c = 5 at hecQ
      omega
  have hremaining : (∑ t ∈ (Finset.univ.erase e).erase c, Q e t) = 1 := by
    have heMem : e ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ e
    have hcMem : c ∈ (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hec.symm, Finset.mem_univ c⟩
    have hsplitE := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q e) heMem
    have hsplitC := Finset.sum_erase_add
      (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent) (Q e) hcMem
    have hrowe' : (∑ t ∈ (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent), Q e t) = 6 := by
      simpa using hrowe
    change Q e c = 5 at hecQ
    omega
  have hsqe := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e e
  have hprode : (∑ t, Q e t * Q t e) = 6 := by
    simpa [Q, Matrix.mul_apply, he3] using hsqe
  have hreverse := reverse_eq_one_of_balanced_row_product_eq_row
    Q (fun t ↦ t.supp.ncard) e (by rw [he3]; norm_num)
      (fun t ↦ secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e t)
      (by rw [hprode, hrowe])
  have hnezero : (∑ t ∈ (Finset.univ.erase e).erase c, Q e t) ≠ 0 := by
    omega
  obtain ⟨f, hfmem, hqfne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnezero
  have hqfle : Q e f ≤ ∑ t ∈ (Finset.univ.erase e).erase c, Q e t :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hfmem
  have hqef : Q e f = 1 := by omega
  have hfe : f ≠ e := (Finset.mem_erase.mp
    (Finset.mem_erase.mp hfmem).2).1
  have hfc : f ≠ c := (Finset.mem_erase.mp hfmem).1
  have hfeQ : Q f e = 1 := hreverse f (by omega)
  have hbalF := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e f
  change e.supp.ncard * Q e f = f.supp.ncard * Q f e at hbalF
  rw [he3, hqef, hfeQ] at hbalF
  refine ⟨e, f, hec, hfc, hfe, he3, by omega, hce, hecQ⟩

/-- The order-fifteen singleton branch is impossible. -/
theorem false_of_degreeSix_orderFifteen_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc15 : c.supp.ncard = 15) : False := by
  obtain ⟨e, f, hec, hfc, hfe, he3, hf3, hce, hecQ⟩ :=
    degreeSix_orderFifteen_singleton_exists_two_orderThree_contacts
      G hfree hmin hcard u hu huRange huD hr c hsector hc15
  obtain ⟨_, _, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  apply degreeSix_orderFifteen_two_orderThree_contacts_false
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun t ↦ t.supp.ncard) c e f hec.symm hfc.symm hfe.symm
      hc15 he3 hf3
  · simpa [hcard] using
      (sum_connectedComponent_supp_ncard (secondOrderDefectGraph G))
  · exact hrow
  · simpa [hc15] using hprod
  · intro x
    exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) x
  · intro x y
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) x y
  · exact hce
  · exact hecQ

/-- Graph instantiation of the forced contact in the order-six singleton
branch.  The contact target is a distinct order-three component with quotient
entries `1` forward and `2` backward. -/
theorem degreeSix_orderSix_singleton_exists_orderThree_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc6 : c.supp.ncard = 6) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0 ∧
      (∑ t ∈ (Finset.univ.erase e).erase c,
        componentQuotientMatrix G (secondOrderDefectGraph G) e t) = 4 ∧
      ∀ t : (secondOrderDefectGraph G).ConnectedComponent,
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) e t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t e = 1 ∧
          t.supp.ncard = 3 *
            componentQuotientMatrix G (secondOrderDefectGraph G) e t := by
  obtain ⟨_, hdiag, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  obtain ⟨e, hne, he3, hce, hec⟩ := degreeSix_orderSix_singleton_contact
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun e ↦ e.supp.ncard) c hc6 hrow
      (by simpa [hc6] using hprod) hbal
  have hediag : componentQuotientMatrix G
      (secondOrderDefectGraph G) e e = 0 := by
    rcases oddComponent_diagonalQuotient_eq_zero_or_two
      G hfree (d := 6) (r := e.supp.ncard)
        (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) (hr e)
        (by rw [he3]; norm_num) e (u e) (hu e) (huRange e) (huD e) with
      hzero | htwo
    · exact hzero
    · have hcen : c ≠ e := fun h ↦ hne h.symm
      have hsq := secondOrder_componentQuotientMatrix_sq_apply
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) c e
      have hsum : (∑ t,
          componentQuotientMatrix G (secondOrderDefectGraph G) c t *
            componentQuotientMatrix G (secondOrderDefectGraph G) t e) = 3 := by
        simpa [Matrix.mul_apply, hcen, he3] using hsq
      have hlower := two_distinct_terms_le_sum
        (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c t *
          componentQuotientMatrix G (secondOrderDefectGraph G) t e) hcen
      rw [hdiag, hce, htwo, hsum] at hlower
      omega
  have hrowe := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e
  refine ⟨e, hne, he3, hce, hec, hediag, ?_, ?_⟩
  · have heMem : e ∈ (Finset.univ :
        Finset (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_univ e
    have hcMem : c ∈ (Finset.univ.erase e :
        Finset (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c⟩
    have hsplitE := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) e t) heMem
    have hsplitC := Finset.sum_erase_add
      (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) e t) hcMem
    omega
  have hsqe := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e e
  have hprode : (∑ t,
      componentQuotientMatrix G (secondOrderDefectGraph G) e t *
        componentQuotientMatrix G (secondOrderDefectGraph G) t e) = 6 := by
    simpa [Matrix.mul_apply, he3] using hsqe
  have hreverse := reverse_eq_one_of_balanced_row_product_eq_row
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun t ↦ t.supp.ncard) e (by rw [he3]; norm_num)
      (fun t ↦ secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e t)
      (by rw [hprode, hrowe])
  intro t hpos
  have hte := hreverse t hpos
  refine ⟨hte, ?_⟩
  have hbt := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e t
  rw [he3, hte, mul_one] at hbt
  exact hbt.symm

/-- After removing the forced order-three contact, the remaining order-six
singleton row has ordinary and two-step mass three.  Hence every positive
remaining contact has reverse multiplicity one and target order `6q`. -/
theorem degreeSix_orderSix_singleton_remaining_contact_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc6 : c.supp.ncard = 6) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0 ∧
      (∑ t ∈ (Finset.univ.erase c).erase e,
        componentQuotientMatrix G (secondOrderDefectGraph G) c t) = 3 ∧
      (∀ t ∈ (Finset.univ.erase c).erase e,
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) c t →
          componentQuotientMatrix G (secondOrderDefectGraph G) t c = 1 ∧
          t.supp.ncard = 6 *
            componentQuotientMatrix G (secondOrderDefectGraph G) c t) := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  obtain ⟨e, hec, he3, hce, hecQ, hee, _, _⟩ :=
    degreeSix_orderSix_singleton_exists_orderThree_contact
      G hfree hmin hcard u hu huRange huD hr c hsector hc6
  obtain ⟨_, _, hrow, hprod, hbal⟩ := degreeSix_singleton_component_quotient_row
    G hfree hmin hcard u hu huRange huD hr c hsector
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    (Finset.univ.erase c).erase e
  have heIn : e ∈ (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hsplitRow := Finset.sum_erase_add
    (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent) (Q c) heIn
  have hsplitProd := Finset.sum_erase_add
    (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ Q c t * Q t c) heIn
  have hrowS : (∑ t ∈ S, Q c t) = 3 := by
    change Q c e = 1 at hce
    change (∑ t ∈ Finset.univ.erase c, Q c t) = 4 at hrow
    dsimp [S]
    omega
  have hprodS : (∑ t ∈ S, Q c t * Q t c) = 3 := by
    have hp : (∑ t ∈ Finset.univ.erase c, Q c t * Q t c) = 5 := by
      simpa [hc6] using hprod
    change Q c e = 1 at hce
    change Q e c = 2 at hecQ
    change (∑ x ∈ (Finset.univ.erase c).erase e, Q c x * Q x c) +
      Q c e * Q e c = ∑ x ∈ Finset.univ.erase c, Q c x * Q x c at hsplitProd
    rw [hce, hecQ] at hsplitProd
    dsimp [S]
    omega
  have hreverse := reverse_eq_one_on_finset_of_balanced_product_eq_row
    S Q (fun t ↦ t.supp.ncard) c (by rw [hc6]; norm_num) hbal
      (by rw [hprodS, hrowS])
  refine ⟨e, hec, he3, hce, hecQ, hee, hrowS, ?_⟩
  intro t ht hpos
  have htcQ := hreverse t ht hpos
  refine ⟨htcQ, ?_⟩
  have hb := hbal t
  change c.supp.ncard * Q c t = t.supp.ncard * Q t c at hb
  rw [hc6, htcQ, mul_one] at hb
  exact hb.symm

/-- In the residual `1+1+1` branch, the three contacts are distinct
order-six components.  After removing them together with the singleton and
its forced order-three contact, the remaining components have total order
six, hence are either one order-six component or two order-three components. -/
theorem degreeSix_orderSix_three_single_contact_shape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hc6 : c.supp.ncard = 6) (hec : e ≠ c) (he3 : e.supp.ncard = 3)
    (hcprofile : ∀ t ∈ (Finset.univ.erase c).erase e,
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) c t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t c = 1 ∧
        t.supp.ncard = 6 *
          componentQuotientMatrix G (secondOrderDefectGraph G) c t)
    (hq1card : (((Finset.univ.erase c).erase e).filter fun t ↦
      componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1).card = 3) :
    ∃ d x y : (secondOrderDefectGraph G).ConnectedComponent,
      d ≠ x ∧ d ≠ y ∧ x ≠ y ∧
      d ≠ c ∧ d ≠ e ∧ x ≠ c ∧ x ≠ e ∧ y ≠ c ∧ y ≠ e ∧
      d.supp.ncard = 6 ∧ x.supp.ncard = 6 ∧ y.supp.ncard = 6 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c d = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c x = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c y = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) d c = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) x c = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) y c = 1 ∧
      (let U := ((((Finset.univ.erase c).erase e).erase d).erase x).erase y
       (∃ f, U = {f} ∧ f.supp.ncard = 6) ∨
       (∃ f g, f ≠ g ∧ U = {f, g} ∧
         f.supp.ncard = 3 ∧ g.supp.ncard = 3)) := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    (Finset.univ.erase c).erase e
  let A := S.filter fun t ↦ Q c t = 1
  have hAcard : A.card = 3 := by simpa [A, S, Q] using hq1card
  obtain ⟨d, x, y, hdx, hdy, hxy, hA⟩ := Finset.card_eq_three.mp hAcard
  have hdA : d ∈ A := by rw [hA]; simp
  have hxA : x ∈ A := by rw [hA]; simp [hdx]
  have hyA : y ∈ A := by rw [hA]; simp [hdy, hxy]
  have hdData := Finset.mem_filter.mp hdA
  have hxData := Finset.mem_filter.mp hxA
  have hyData := Finset.mem_filter.mp hyA
  have hdS : d ∈ S := hdData.1
  have hxS : x ∈ S := hxData.1
  have hyS : y ∈ S := hyData.1
  have hcd : Q c d = 1 := hdData.2
  have hcx : Q c x = 1 := hxData.2
  have hcy : Q c y = 1 := hyData.2
  have hdc : d ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hdS).2).1
  have hde : d ≠ e := (Finset.mem_erase.mp hdS).1
  have hxc : x ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1
  have hxe : x ≠ e := (Finset.mem_erase.mp hxS).1
  have hyc : y ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hyS).2).1
  have hye : y ≠ e := (Finset.mem_erase.mp hyS).1
  have hdPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c d := by
    simpa [Q] using (show 0 < Q c d by omega)
  have hxPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c x := by
    simpa [Q] using (show 0 < Q c x by omega)
  have hyPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c y := by
    simpa [Q] using (show 0 < Q c y by omega)
  have hdProfile := hcprofile d hdS hdPos
  have hxProfile := hcprofile x hxS hxPos
  have hyProfile := hcprofile y hyS hyPos
  have hd6 : d.supp.ncard = 6 := by simpa [Q, hcd] using hdProfile.2
  have hx6 : x.supp.ncard = 6 := by simpa [Q, hcx] using hxProfile.2
  have hy6 : y.supp.ncard = 6 := by simpa [Q, hcy] using hyProfile.2
  let U : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    ((((Finset.univ.erase c).erase e).erase d).erase x).erase y
  have hcIn : c ∈ (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
  have heIn : e ∈ (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hdIn : d ∈ (Finset.univ.erase c).erase e := hdS
  have hxIn : x ∈ ((Finset.univ.erase c).erase e).erase d :=
    Finset.mem_erase.mpr ⟨hdx.symm, hxS⟩
  have hyIn : y ∈ (((Finset.univ.erase c).erase e).erase d).erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_erase.mpr ⟨hdy.symm, hyS⟩⟩
  have htC := Finset.sum_erase_add (Finset.univ : Finset _)
    (fun t ↦ t.supp.ncard) hcIn
  have htE := Finset.sum_erase_add (Finset.univ.erase c)
    (fun t ↦ t.supp.ncard) heIn
  have htD := Finset.sum_erase_add ((Finset.univ.erase c).erase e)
    (fun t ↦ t.supp.ncard) hdIn
  have htX := Finset.sum_erase_add (((Finset.univ.erase c).erase e).erase d)
    (fun t ↦ t.supp.ncard) hxIn
  have htY := Finset.sum_erase_add
    ((((Finset.univ.erase c).erase e).erase d).erase x)
    (fun t ↦ t.supp.ncard) hyIn
  have htotal : (∑ t : (secondOrderDefectGraph G).ConnectedComponent,
      t.supp.ncard) = 33 := by
    simpa [hcard] using
      (sum_connectedComponent_supp_ncard (secondOrderDefectGraph G))
  have hUsum : (∑ t ∈ U, t.supp.ncard) = 6 := by
    dsimp [U]
    omega
  have hUclass := component_orders_sum_six_classification U
    (fun t ↦ t.supp.ncard) (fun t ht ↦ hr t) hUsum
  exact ⟨d, x, y, hdx, hdy, hxy, hdc, hde, hxc, hxe, hyc, hye,
    hd6, hx6, hy6, hcd, hcx, hcy, hdProfile.1, hxProfile.1,
    hyProfile.1, by simpa [U] using hUclass⟩

set_option maxHeartbeats 2000000 in
/-- The `1+1+1` branch with one unused order-six component contradicts the
three contact-square equations and the global trace. -/
theorem false_of_degreeSix_orderSix_three_single_contacts_unused_six_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (c e d x y f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc6 : c.supp.ncard = 6) (he3 : e.supp.ncard = 3)
    (hd6 : d.supp.ncard = 6) (hx6 : x.supp.ncard = 6)
    (hy6 : y.supp.ncard = 6) (hf6 : f.supp.ncard = 6)
    (hec : e ≠ c) (hdc : d ≠ c) (hde : d ≠ e)
    (hxc : x ≠ c) (hxe : x ≠ e) (hyc : y ≠ c) (hye : y ≠ e)
    (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y)
    (hcc : componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2)
    (hce : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1)
    (hecQ : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2)
    (hee : componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0)
    (hcd : componentQuotientMatrix G (secondOrderDefectGraph G) c d = 1)
    (hcx : componentQuotientMatrix G (secondOrderDefectGraph G) c x = 1)
    (hcy : componentQuotientMatrix G (secondOrderDefectGraph G) c y = 1)
    (hU : (((((Finset.univ.erase c).erase e).erase d).erase x).erase y :
      Finset (secondOrderDefectGraph G).ConnectedComponent) = {f}) : False := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let U : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    ((((Finset.univ.erase c).erase e).erase d).erase x).erase y
  have hfU : f ∈ U := by rw [hU]; simp
  have hfy : f ≠ y := (Finset.mem_erase.mp hfU).1
  have hfx : f ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hfU).2).1
  have hfd : f ≠ d := (Finset.mem_erase.mp
    (Finset.mem_erase.mp (Finset.mem_erase.mp hfU).2).2).1
  have hfe : f ≠ e := (Finset.mem_erase.mp
    (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hfU).2).2).2).1
  have hfc : f ≠ c := (Finset.mem_erase.mp
    (Finset.mem_erase.mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hfU).2).2).2).2).1
  have hcIn : c ∈ (Finset.univ : Finset _) := Finset.mem_univ c
  have heIn : e ∈ (Finset.univ.erase c : Finset _) :=
    Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hdIn : d ∈ (Finset.univ.erase c).erase e :=
    Finset.mem_erase.mpr ⟨hde, Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩⟩
  have hxIn : x ∈ ((Finset.univ.erase c).erase e).erase d :=
    Finset.mem_erase.mpr ⟨hdx.symm,
      Finset.mem_erase.mpr ⟨hxe, Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ x⟩⟩⟩
  have hyIn : y ∈ (((Finset.univ.erase c).erase e).erase d).erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_erase.mpr ⟨hdy.symm,
      Finset.mem_erase.mpr ⟨hye, Finset.mem_erase.mpr ⟨hyc, Finset.mem_univ y⟩⟩⟩⟩
  have expand (F : (secondOrderDefectGraph G).ConnectedComponent → ℕ) :
      (∑ t, F t) = F c + F e + F d + F x + F y + F f := by
    have hC := Finset.sum_erase_add (Finset.univ : Finset _) F hcIn
    have hE := Finset.sum_erase_add (Finset.univ.erase c) F heIn
    have hD := Finset.sum_erase_add ((Finset.univ.erase c).erase e) F hdIn
    have hX := Finset.sum_erase_add (((Finset.univ.erase c).erase e).erase d) F hxIn
    have hY := Finset.sum_erase_add
      ((((Finset.univ.erase c).erase e).erase d).erase x) F hyIn
    have hlast : (∑ t ∈ U, F t) = F f := by simp [hU]
    dsimp [U] at hlast
    omega
  have hrow (z : _) : (∑ t, Q z t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) z
  have hbal (a b : _) : a.supp.ncard * Q a b = b.supp.ncard * Q b a :=
    secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
  have hsq (a b : _) (hab : a ≠ b) : (∑ t, Q a t * Q t b) = b.supp.ncard := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    simpa [Q, Matrix.mul_apply, hab] using hs
  have hcf : Q c f = 0 := by
    have hcRow := hrow c
    rw [expand (Q c), hcc, hce, hcd, hcx, hcy] at hcRow
    omega
  have hfcQ : Q f c = 0 := by
    have hb := hbal c f
    rw [hc6, hf6, hcf] at hb
    omega
  have hsumZE : Q d e + Q x e + Q y e = 1 := by
    have hs := hsq c e hec.symm
    rw [expand (fun t ↦ Q c t * Q t e), hcc, hce, hcd, hcx, hcy, hcf,
      hee, he3] at hs
    omega
  have hed : Q e d = 2 * Q d e := by
    have hb := hbal e d
    rw [he3, hd6] at hb
    omega
  have hex : Q e x = 2 * Q x e := by
    have hb := hbal e x
    rw [he3, hx6] at hb
    omega
  have hey : Q e y = 2 * Q y e := by
    have hb := hbal e y
    rw [he3, hy6] at hb
    omega
  have hef : Q e f = 2 := by
    have heRow := hrow e
    rw [expand (Q e), hecQ, hee, hed, hex, hey] at heRow
    omega
  have hfeQ : Q f e = 1 := by
    have hb := hbal e f
    rw [he3, hf6, hef] at hb
    omega
  have hdf : Q d f = Q f d := by
    have hb := hbal d f
    rw [hd6, hf6] at hb
    omega
  have hxf : Q x f = Q f x := by
    have hb := hbal x f
    rw [hx6, hf6] at hb
    omega
  have hyf : Q y f = Q f y := by
    have hb := hbal y f
    rw [hy6, hf6] at hb
    omega
  have hcontactF : Q d f + Q x f + Q y f = 4 := by
    have hs := hsq c f hfc.symm
    rw [expand (fun t ↦ Q c t * Q t f), hcc, hce, hcd, hcx, hcy, hcf,
      hfcQ, hef, hf6] at hs
    omega
  have hff : Q f f = 1 := by
    have hfRow := hrow f
    rw [expand (Q f), hfcQ, hfeQ, ← hdf, ← hxf, ← hyf] at hfRow
    omega
  have hdxSymm : Q d x = Q x d := by
    have hb := hbal d x
    rw [hd6, hx6] at hb
    omega
  have hdySymm : Q d y = Q y d := by
    have hb := hbal d y
    rw [hd6, hy6] at hb
    omega
  have hxySymm : Q x y = Q y x := by
    have hb := hbal x y
    rw [hx6, hy6] at hb
    omega
  have contactSquare (z : _) (hzc : z ≠ c) (hz6 : z.supp.ncard = 6) :
      Q d z + Q x z + Q y z = 4 - Q e z := by
    have hs := hsq c z hzc
    rw [expand (fun t ↦ Q c t * Q t z), hcc, hce, hcd, hcx, hcy, hcf,
      hz6] at hs
    omega
  have hsd := contactSquare d hdc hd6
  have hsx := contactSquare x hxc hx6
  have hsy := contactSquare y hyc hy6
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by norm_num)
  have hdiag : Q d d + Q x x + Q y y = 3 := by
    change (∑ t, Q t t) = 6 at htrace
    rw [expand (fun t ↦ Q t t), hcc, hee, hff] at htrace
    omega
  rcases (show (Q d e = 1 ∧ Q x e = 0 ∧ Q y e = 0) ∨
      (Q d e = 0 ∧ Q x e = 1 ∧ Q y e = 0) ∨
      (Q d e = 0 ∧ Q x e = 0 ∧ Q y e = 1) by omega) with hd | hx | hy
  · apply false_of_degreeSix_orderSix_three_single_contacts_unused_six Q d x y
      (by rw [hed, hd.1] at hsd; omega)
      (by rw [hex, hd.2.1] at hsx; omega)
      (by rw [hey, hd.2.2] at hsy; omega)
      hdxSymm hdySymm hxySymm hdiag
  · apply false_of_degreeSix_orderSix_three_single_contacts_unused_six Q x d y
      (by rw [hex, hx.2.1] at hsx; omega)
      (by rw [hed, hx.1] at hsd; omega)
      (by rw [hey, hx.2.2] at hsy; omega)
      hdxSymm.symm hxySymm hdySymm hdiag
  · apply false_of_degreeSix_orderSix_three_single_contacts_unused_six Q y d x
      (by rw [hey, hy.2.2] at hsy; omega)
      (by rw [hed, hy.1] at hsd; omega)
      (by rw [hex, hy.2.1] at hsx; omega)
      hdySymm.symm hxySymm.symm hdxSymm hdiag

/-- The residual single quotient-three contact branch is impossible. -/
theorem false_of_degreeSix_orderSix_three_contact_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc6 : c.supp.ncard = 6) (hec : e ≠ c) (he3 : e.supp.ncard = 3)
    (hce : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1)
    (hecQ : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2)
    (hee : componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0)
    (hrowS : (∑ t ∈ (Finset.univ.erase c).erase e,
      componentQuotientMatrix G (secondOrderDefectGraph G) c t) = 3)
    (hcprofile : ∀ t ∈ (Finset.univ.erase c).erase e,
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) c t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t c = 1 ∧
        t.supp.ncard = 6 *
          componentQuotientMatrix G (secondOrderDefectGraph G) c t)
    (hq3card : (((Finset.univ.erase c).erase e).filter fun t ↦
      componentQuotientMatrix G (secondOrderDefectGraph G) c t = 3).card = 1) : False := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    (Finset.univ.erase c).erase e
  let A := S.filter fun t ↦ Q c t = 3
  have hAcard : A.card = 1 := by simpa [A, S, Q] using hq3card
  obtain ⟨a, haSet⟩ := Finset.card_eq_one.mp hAcard
  have haMem : a ∈ A := by rw [haSet]; simp
  have haFilter := Finset.mem_filter.mp haMem
  have haS : a ∈ S := haFilter.1
  have hca : Q c a = 3 := haFilter.2
  have hac : a ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp haS).2).1
  have hae : a ≠ e := (Finset.mem_erase.mp haS).1
  have hcaPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c a := by
    simpa [Q] using (show 0 < Q c a by omega)
  have haData := hcprofile a haS hcaPos
  have ha18 : a.supp.ncard = 18 := by
    simpa [Q, hca] using haData.2
  have hrowE : (∑ t, Q e t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e
  have hea : Q e a = 0 := by
    by_contra hq
    have hqpos : 0 < Q e a := Nat.pos_of_ne_zero hq
    obtain ⟨_, heprof⟩ := degreeSix_orderThree_zeroDiagonal_profile
      G hfree hmin hcard e he3 hee
    have hsize := (heprof a hqpos).2
    change a.supp.ncard = 3 * Q e a at hsize
    have hlower := two_distinct_terms_le_sum (Q e) (show c ≠ a from hac.symm)
    change Q e c = 2 at hecQ
    change (∑ t, Q e t) = 6 at hrowE
    rw [hrowE, hecQ] at hlower
    nlinarith
  let R : Finset (secondOrderDefectGraph G).ConnectedComponent := S.erase a
  have haIn : a ∈ S := haS
  have hsplit := Finset.sum_erase_add S (Q c) haIn
  have hrowR : (∑ t ∈ R, Q c t) = 0 := by
    change (∑ t ∈ S, Q c t) = 3 at hrowS
    dsimp [R]
    omega
  have hzero : ∀ t ∈ R, Q c t = 0 := by
    intro t ht
    have hle : Q c t ≤ ∑ x ∈ R, Q c x :=
      Finset.single_le_sum (f := Q c) (fun _ _ ↦ Nat.zero_le _) ht
    omega
  have hcIn : c ∈ (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
  have heIn : e ∈ (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hsqGraph := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) c e
  have hsq : (∑ t, Q c t * Q t e) = 3 := by
    simpa [Q, Matrix.mul_apply, hec.symm, he3] using hsqGraph
  have hsC := Finset.sum_erase_add (Finset.univ : Finset _)
    (fun t ↦ Q c t * Q t e) hcIn
  have hsE := Finset.sum_erase_add (Finset.univ.erase c)
    (fun t ↦ Q c t * Q t e) heIn
  have hsA := Finset.sum_erase_add S (fun t ↦ Q c t * Q t e) haIn
  have hrest : (∑ t ∈ R, Q c t * Q t e) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [hzero t ht]
  obtain ⟨_, hcc, _, _, hbal⟩ := degreeSix_singleton_component_quotient_row
    G hfree hmin hcard u hu huRange huD hr c hsector
  have hbalEA := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e a
  have hsqe : Q c c * Q c e + Q c e * Q e e + Q c a * Q a e = 3 := by
    change (∑ t, Q c t * Q t e) = 3 at hsq
    change Q c e = 1 at hce
    change Q e e = 0 at hee
    dsimp [R, S] at hrest hsA
    omega
  exact false_of_degreeSix_orderSix_three_contact Q (fun t ↦ t.supp.ncard)
    c e a hc6 he3 ha18 hcc hce hca hee hea hbalEA hsqe

set_option maxHeartbeats 2000000 in
/-- The residual `1+2` contact branch is impossible. -/
theorem false_of_degreeSix_orderSix_one_two_contact_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc6 : c.supp.ncard = 6) (hec : e ≠ c) (he3 : e.supp.ncard = 3)
    (hce : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1)
    (hecQ : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2)
    (hee : componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0)
    (hrowS : (∑ t ∈ (Finset.univ.erase c).erase e,
      componentQuotientMatrix G (secondOrderDefectGraph G) c t) = 3)
    (hcprofile : ∀ t ∈ (Finset.univ.erase c).erase e,
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) c t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t c = 1 ∧
        t.supp.ncard = 6 * componentQuotientMatrix G (secondOrderDefectGraph G) c t)
    (hq1card : (((Finset.univ.erase c).erase e).filter fun t ↦
      componentQuotientMatrix G (secondOrderDefectGraph G) c t = 1).card = 1)
    (hq2card : (((Finset.univ.erase c).erase e).filter fun t ↦
      componentQuotientMatrix G (secondOrderDefectGraph G) c t = 2).card = 1) : False := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    (Finset.univ.erase c).erase e
  let D := S.filter fun t ↦ Q c t = 1
  let A := S.filter fun t ↦ Q c t = 2
  have hDcard : D.card = 1 := by simpa [D, S, Q] using hq1card
  have hAcard : A.card = 1 := by simpa [A, S, Q] using hq2card
  obtain ⟨d, hdSet⟩ := Finset.card_eq_one.mp hDcard
  obtain ⟨a, haSet⟩ := Finset.card_eq_one.mp hAcard
  have hdMem : d ∈ D := by rw [hdSet]; simp
  have haMem : a ∈ A := by rw [haSet]; simp
  have hdFilter := Finset.mem_filter.mp hdMem
  have haFilter := Finset.mem_filter.mp haMem
  have hdS : d ∈ S := hdFilter.1
  have haS : a ∈ S := haFilter.1
  have hcd : Q c d = 1 := hdFilter.2
  have hca : Q c a = 2 := haFilter.2
  have hdc : d ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hdS).2).1
  have hde : d ≠ e := (Finset.mem_erase.mp hdS).1
  have hac : a ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp haS).2).1
  have hae : a ≠ e := (Finset.mem_erase.mp haS).1
  have hda : d ≠ a := by intro h; subst a; omega
  have hcdPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c d := by
    simpa [Q] using (show 0 < Q c d by omega)
  have hcaPos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c a := by
    simpa [Q] using (show 0 < Q c a by omega)
  have hdData := hcprofile d hdS hcdPos
  have haData := hcprofile a haS hcaPos
  have hd6 : d.supp.ncard = 6 := by simpa [Q, hcd] using hdData.2
  have ha12 : a.supp.ncard = 12 := by simpa [Q, hca] using haData.2
  obtain ⟨hrowE, heprofile⟩ := degreeSix_orderThree_zeroDiagonal_profile
    G hfree hmin hcard e he3 hee
  have hdeCases : Q d e = 0 ∨ Q d e = 1 := by
    by_cases hz : Q d e = 0
    · exact Or.inl hz
    · have hbal := secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e d
      have hpos : 0 < Q e d := by
        change e.supp.ncard * Q e d = d.supp.ncard * Q d e at hbal
        rw [he3, hd6] at hbal
        have hzpos : 0 < Q d e := Nat.pos_of_ne_zero hz
        nlinarith
      exact Or.inr (heprofile d hpos).1
  have haeCases : Q a e = 0 ∨ Q a e = 1 := by
    by_cases hz : Q a e = 0
    · exact Or.inl hz
    · have hbal := secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e a
      have hpos : 0 < Q e a := by
        change e.supp.ncard * Q e a = a.supp.ncard * Q a e at hbal
        rw [he3, ha12] at hbal
        have hzpos : 0 < Q a e := Nat.pos_of_ne_zero hz
        nlinarith
      exact Or.inr (heprofile a hpos).1
  let R : Finset (secondOrderDefectGraph G).ConnectedComponent := (S.erase d).erase a
  have hdIn : d ∈ S := hdS
  have haIn : a ∈ S.erase d := Finset.mem_erase.mpr ⟨hda.symm, haS⟩
  have hsD := Finset.sum_erase_add S (Q c) hdIn
  have hsA := Finset.sum_erase_add (S.erase d) (Q c) haIn
  have hrowR : (∑ t ∈ R, Q c t) = 0 := by
    change (∑ t ∈ S, Q c t) = 3 at hrowS
    dsimp [R]
    omega
  have hzero : ∀ t ∈ R, Q c t = 0 := by
    intro t ht
    have hle : Q c t ≤ ∑ x ∈ R, Q c x :=
      Finset.single_le_sum (f := Q c) (fun _ _ ↦ Nat.zero_le _) ht
    omega
  have hcIn : c ∈ (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
  have heIn : e ∈ (Finset.univ.erase c : Finset
      (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_erase.mpr ⟨hec, Finset.mem_univ e⟩
  have hsqEgraph := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) c e
  have hsqE : (∑ t, Q c t * Q t e) = 3 := by
    simpa [Q, Matrix.mul_apply, hec.symm, he3] using hsqEgraph
  have hsEc := Finset.sum_erase_add (Finset.univ : Finset _)
    (fun t ↦ Q c t * Q t e) hcIn
  have hsEe := Finset.sum_erase_add (Finset.univ.erase c)
    (fun t ↦ Q c t * Q t e) heIn
  have hsEd := Finset.sum_erase_add S (fun t ↦ Q c t * Q t e) hdIn
  have hsEa := Finset.sum_erase_add (S.erase d)
    (fun t ↦ Q c t * Q t e) haIn
  have hrestE : (∑ t ∈ R, Q c t * Q t e) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [hzero t ht]
  obtain ⟨_, hcc, _, _, _⟩ := degreeSix_singleton_component_quotient_row
    G hfree hmin hcard u hu huRange huD hr c hsector
  change Q c c = 2 at hcc
  change Q c e = 1 at hce
  change Q e e = 0 at hee
  have hsqEexpand : Q c c * Q c e + Q c e * Q e e +
      Q c d * Q d e + Q c a * Q a e = 3 := by
    change (∑ t, Q c t * Q t e) = 3 at hsqE
    dsimp [R, S] at hrestE hsEc hsEe hsEd hsEa
    omega
  have hcontactE : Q d e + 2 * Q a e = 1 := by
    have hh : 2 + Q d e + 2 * Q a e = 3 := by
      simpa [hcc, hce, hee, hcd, hca] using hsqEexpand
    omega
  have hdeQ : Q d e = 1 := by
    rcases hdeCases with hz | ho <;> rcases haeCases with ha0 | ha1
    all_goals try exact ho
    all_goals omega
  have haeQ : Q a e = 0 := by
    rcases haeCases with hz | ho
    · exact hz
    · omega
  have hed : Q e d = 2 := by
    have hb := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e d
    change e.supp.ncard * Q e d = d.supp.ncard * Q d e at hb
    rw [he3, hd6, hdeQ] at hb
    omega
  have hea : Q e a = 0 := by
    have hb := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) e a
    change e.supp.ncard * Q e a = a.supp.ncard * Q a e at hb
    rw [he3, ha12, haeQ] at hb
    omega
  have squareThree (z : _) (hzc : z ≠ c) (hzsize : z.supp.ncard = 6 ∨ z.supp.ncard = 12) :
      (∑ t, Q c t * Q t z) = z.supp.ncard := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c z
    simpa [Q, Matrix.mul_apply, hzc.symm] using hs
  have hsqD := squareThree d hdc (Or.inl hd6)
  have hsqA := squareThree a hac (Or.inr ha12)
  have expandSquare (z : _) :
      (∑ t, Q c t * Q t z) = Q c c * Q c z + Q c e * Q e z +
        Q c d * Q d z + Q c a * Q a z := by
    have hsC := Finset.sum_erase_add (Finset.univ : Finset _)
      (fun t ↦ Q c t * Q t z) hcIn
    have hsE := Finset.sum_erase_add (Finset.univ.erase c)
      (fun t ↦ Q c t * Q t z) heIn
    have hsD := Finset.sum_erase_add S (fun t ↦ Q c t * Q t z) hdIn
    have hsA := Finset.sum_erase_add (S.erase d)
      (fun t ↦ Q c t * Q t z) haIn
    have hrest : (∑ t ∈ R, Q c t * Q t z) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [hzero t ht]
    dsimp [R, S] at hrest hsC hsE hsD hsA
    omega
  have hsqd : Q c c * Q c d + Q c e * Q e d +
      Q c d * Q d d + Q c a * Q a d = 6 := by
    rw [expandSquare d] at hsqD
    simpa [hd6] using hsqD
  have hsqa : Q c c * Q c a + Q c e * Q e a +
      Q c d * Q d a + Q c a * Q a a = 12 := by
    rw [expandSquare a] at hsqA
    simpa [ha12] using hsqA
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by norm_num)
  have hdDiagIn : d ∈ (Finset.univ.erase c : Finset _) :=
    Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩
  have haDiagIn : a ∈ (Finset.univ.erase c).erase d :=
    Finset.mem_erase.mpr ⟨hda.symm,
      Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩⟩
  have htC := Finset.sum_erase_add (Finset.univ : Finset _) (fun t ↦ Q t t) hcIn
  have htD := Finset.sum_erase_add (Finset.univ.erase c) (fun t ↦ Q t t) hdDiagIn
  have htA := Finset.sum_erase_add ((Finset.univ.erase c).erase d)
    (fun t ↦ Q t t) haDiagIn
  have hdiagBudget : Q d d + Q a a ≤ 4 := by
    change (∑ t, Q t t) = 6 at htrace
    change Q c c = 2 at hcc
    omega
  have hbalCA := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) c a
  have hbalDA := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) d a
  have hgroup := degreeSix_orderTwelve_two_orderSix_targets_le_one
    G hfree hmin hcard u hu huRange huD a c d ha12 hc6 hd6 hdc.symm
  exact false_of_degreeSix_orderSix_one_two_contact Q (fun t ↦ t.supp.ncard)
    c e d a hc6 he3 hd6 ha12 hcc hce hcd hca hed hea hbalCA hbalDA
      hsqd hsqa hdiagBudget hgroup

/-- In the empty color-sector branch, the all-triangle defect decomposition
is impossible; hence an antipodal-colored defect cycle of order at least four
exists. -/
theorem degreeSix_exists_large_antipodal_component_of_sector_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hempty : triangleFreeCycleSector G u = ∅) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      4 ≤ c.supp.ncard ∧ c ∉ triangleFreeCycleSector G u := by
  by_contra hnone
  push Not at hnone
  have hthree : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3 := by
    intro c
    have hcnot : c ∉ triangleFreeCycleSector G u := by rw [hempty]; simp
    have hlt : ¬ 4 ≤ c.supp.ncard := fun hfour => hcnot (hnone c hfour)
    have hlower := hr c
    omega
  exact no_degreeSix_boundary_of_secondOrder_all_triangles
    G hfree hmin hcard hthree

end

end Erdos85
