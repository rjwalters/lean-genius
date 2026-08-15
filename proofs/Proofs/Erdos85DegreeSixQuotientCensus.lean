import Mathlib
import Proofs.Erdos85KernelBVDecide

/-!
# Verified finite quotient census for the degree-six boundary

These certificates classify the component-order profiles of five- and
seven-dimensional balanced quotient matrices.  Eight-bit arithmetic is
wide enough for every expression under the explicit bounds.  The finite
checkpoints currently use `bv_decide`; `Erdos85KernelBVDecide` provides an
experimental typed-LRAT replay path for replacing their native-evaluation
axioms once large certificates can be checked in bounded kernel stack space.
-/

namespace Erdos85

set_option maxHeartbeats 1000000000

abbrev DegreeSixCensusWord := BitVec 8

/-- Kernel-clean structural reduction at an order-three, zero-diagonal base
row.  Equality of its ordinary and two-step row masses forces every positive
reverse quotient to be one; detailed balance then reads off the target order
as three times the forward quotient.  This is the common first step in the
five- and seven-component census branches. -/
theorem degreeSixQuotient_orderThree_zeroDiagonal_profile_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (_hcc : q c c = 0) :
    ∀ j, 0 < q c j → q j c = 1 ∧ s j = 3 * q c j := by
  have hprod : (∑ j, q c j * q j c) = 6 := by
    rw [hsq c c, hc3]
    simp
  have hle : ∀ j, q c j ≤ q c j * q j c := by
    intro j
    by_cases hq : q c j = 0
    · simp [hq]
    · have hqpos : 0 < q c j := Nat.pos_of_ne_zero hq
      have hrpos : 0 < q j c := by
        by_contra hr
        push Not at hr
        have hr0 : q j c = 0 := by omega
        have hb := hbal c j
        rw [hr0, mul_zero] at hb
        exact (Nat.mul_pos (hspos c) hqpos).ne' hb
      calc
        q c j = q c j * 1 := by simp
        _ ≤ q c j * q j c := Nat.mul_le_mul_left _ hrpos
  have hsum : (∑ j, q c j * q j c) = ∑ j, q c j := by
    rw [hprod, hrow c]
  intro j hqpos
  have hr : q j c = 1 := by
    have hrpos : 0 < q j c := by
      have hj := hle j
      by_contra hn
      push Not at hn
      have hz : q j c = 0 := by omega
      rw [hz, mul_zero] at hj
      omega
    by_contra hrne
    have hrlt : q c j < q c j * q j c := by
      have hr2 : 1 < q j c := by omega
      simpa using (Nat.mul_lt_mul_left hqpos).mpr hr2
    have hstrict := Finset.sum_lt_sum
      (fun k _ ↦ hle k) ⟨j, Finset.mem_univ j, hrlt⟩
    rw [hsum] at hstrict
    exact (lt_irrefl _ hstrict)
  refine ⟨hr, ?_⟩
  have hb := hbal c j
  rw [hc3, hr, mul_one] at hb
  exact hb.symm

/-- The order-three base profile splits every finite quotient census into
positive support of total order eighteen and invisible support of total order
twelve.  This packages the exact mass equations used by both remaining
five- and seven-component branch classifications. -/
theorem degreeSixQuotient_orderThree_support_partition_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    let R := (Finset.univ.erase c) \ P
    (∑ j ∈ P, s j) = 18 ∧ (∑ j ∈ R, s j) = 12 := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  let R : Finset C := (Finset.univ.erase c) \ P
  have hprofile := degreeSixQuotient_orderThree_zeroDiagonal_profile_nat
    s q c hspos hrow hbal hsq hc3 hcc
  have hcnotP : c ∉ P := by simp [P, hcc]
  have hqsum : (∑ j ∈ P, q c j) = 6 := by
    calc
      (∑ j ∈ P, q c j) = ∑ j, q c j := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hz : q c j = 0 := by
          by_contra hn
          exact hj (by simp [Nat.pos_of_ne_zero hn])
        simp [hz]
      _ = 6 := hrow c
  have hPmass : (∑ j ∈ P, s j) = 18 := by
    calc
      (∑ j ∈ P, s j) = ∑ j ∈ P, 3 * q c j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hprofile j (by simpa [P] using
          (Finset.mem_filter.mp hj).2)).2
      _ = 3 * ∑ j ∈ P, q c j := by rw [Finset.mul_sum]
      _ = 18 := by rw [hqsum]
  have hPsub : P ⊆ Finset.univ.erase c := by
    intro j hj
    exact Finset.mem_erase.mpr
      ⟨fun hjc ↦ hcnotP (hjc ▸ hj), Finset.mem_univ j⟩
  have hcuniv : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have houtside := Finset.sum_erase_add
    (Finset.univ : Finset C) s hcuniv
  change (∑ j ∈ (Finset.univ : Finset C), s j) = 33 at htotal
  rw [htotal, hc3] at houtside
  have hsplit : (∑ j ∈ (Finset.univ.erase c) \ P, s j) +
      (∑ j ∈ P, s j) = ∑ j ∈ Finset.univ.erase c, s j :=
    Finset.sum_sdiff hPsub
  have houtside30 : (∑ j ∈ Finset.univ.erase c, s j) = 30 := by
    omega
  rw [hPmass, houtside30] at hsplit
  refine ⟨hPmass, ?_⟩
  change (∑ j ∈ (Finset.univ.erase c) \ P, s j) = 12
  omega

def degreeSixQuotientModel5
    (s : Fin 5 → DegreeSixCensusWord)
    (q : Fin 5 → Fin 5 → DegreeSixCensusWord) : Prop :=
  (∀ i, ((3 : DegreeSixCensusWord).ule (s i)) = true ∧ (s i).ult 34 = true) ∧
  (∀ i j, (q i j).ult 7 = true) ∧
  (∑ i, s i) = 33 ∧
  (∀ i, (∑ j, q i j) = 6) ∧
  (∀ i j, s i * q i j = s j * q j i) ∧
  (∀ i j, (∑ k, q i k * q k j) =
    (if i = j then 3 else 0) + s j) ∧
  (∀ i, (q i i).ule 2 = true) ∧
  (∑ i, q i i) = 6 ∧ (∃ i, s i = 3 ∧ q i i = 0) ∧
  (∀ i, s i = 3 → q i i = 0)

theorem degreeSixQuotientModel5_reindex
    (s : Fin 5 → DegreeSixCensusWord)
    (q : Fin 5 → Fin 5 → DegreeSixCensusWord)
    (e : Equiv.Perm (Fin 5)) (h : degreeSixQuotientModel5 s q) :
    degreeSixQuotientModel5 (fun i => s (e i)) (fun i j => q (e i) (e j)) := by
  rcases h with ⟨hs, hq, htotal, hrow, hbal, hsq, hdiag, htrace,
    hbase, hthree⟩
  refine ⟨fun i => hs (e i), fun i j => hq (e i) (e j), ?_, ?_,
    fun i j => hbal (e i) (e j), ?_, fun i => hdiag (e i), ?_, ?_, ?_⟩
  · exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans htotal
  · intro i
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans (hrow (e i))
  · intro i j
    change (∑ k, q (e i) (e k) * q (e k) (e j)) =
      (if i = j then 3 else 0) + s (e j)
    calc
      _ = ∑ k, q (e i) k * q k (e j) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by simpa only [e.injective.eq_iff] using hsq (e i) (e j)
  · change (∑ i, q (e i) (e i)) = 6
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans htrace
  · obtain ⟨i, hsi, hqi⟩ := hbase
    exact ⟨e.symm i, by simpa, by simpa⟩
  · intro i hi
    exact hthree (e i) hi

/-- Every five-component degree-six quotient model has component orders
`3,3,9,9,9`.  The total-order equation supplies the multiplicities once
each entry is known to be three or nine. -/
theorem degreeSixQuotientModel5_profile_zero
    (s : Fin 5 → DegreeSixCensusWord)
    (q : Fin 5 → Fin 5 → DegreeSixCensusWord)
    (h : degreeSixQuotientModel5 s q) : s 0 = 3 ∨ s 0 = 9 := by
  simp [degreeSixQuotientModel5, Fin.forall_fin_succ, Fin.exists_fin_succ,
    Fin.sum_univ_succ] at h ⊢
  generalize s 0 = s0 at h ⊢
  generalize s 1 = s1 at h ⊢
  generalize s 2 = s2 at h ⊢
  generalize s 3 = s3 at h ⊢
  generalize s 4 = s4 at h ⊢
  generalize q 0 0 = q00 at h ⊢
  generalize q 0 1 = q01 at h ⊢
  generalize q 0 2 = q02 at h ⊢
  generalize q 0 3 = q03 at h ⊢
  generalize q 0 4 = q04 at h ⊢
  generalize q 1 0 = q10 at h ⊢
  generalize q 1 1 = q11 at h ⊢
  generalize q 1 2 = q12 at h ⊢
  generalize q 1 3 = q13 at h ⊢
  generalize q 1 4 = q14 at h ⊢
  generalize q 2 0 = q20 at h ⊢
  generalize q 2 1 = q21 at h ⊢
  generalize q 2 2 = q22 at h ⊢
  generalize q 2 3 = q23 at h ⊢
  generalize q 2 4 = q24 at h ⊢
  generalize q 3 0 = q30 at h ⊢
  generalize q 3 1 = q31 at h ⊢
  generalize q 3 2 = q32 at h ⊢
  generalize q 3 3 = q33 at h ⊢
  generalize q 3 4 = q34 at h ⊢
  generalize q 4 0 = q40 at h ⊢
  generalize q 4 1 = q41 at h ⊢
  generalize q 4 2 = q42 at h ⊢
  generalize q 4 3 = q43 at h ⊢
  generalize q 4 4 = q44 at h ⊢
  bv_decide (config := { timeout := 600 })

theorem degreeSixQuotientModel5_profile
    (s : Fin 5 → DegreeSixCensusWord)
    (q : Fin 5 → Fin 5 → DegreeSixCensusWord)
    (h : degreeSixQuotientModel5 s q) : ∀ i, s i = 3 ∨ s i = 9 := by
  intro i
  let e : Equiv.Perm (Fin 5) := Equiv.swap 0 i
  have h' := degreeSixQuotientModel5_profile_zero
    (fun j => s (e j)) (fun j k => q (e j) (e k))
      (degreeSixQuotientModel5_reindex s q e h)
  simpa [e] using h'

def degreeSixQuotientModel7
    (s : Fin 7 → DegreeSixCensusWord)
    (q : Fin 7 → Fin 7 → DegreeSixCensusWord) : Prop :=
  (∀ i, ((3 : DegreeSixCensusWord).ule (s i)) = true ∧ (s i).ult 34 = true) ∧
  (∀ i j, (q i j).ult 7 = true) ∧
  (∑ i, s i) = 33 ∧
  (∀ i, (∑ j, q i j) = 6) ∧
  (∀ i j, s i * q i j = s j * q j i) ∧
  (∀ i j, (∑ k, q i k * q k j) =
    (if i = j then 3 else 0) + s j) ∧
  (∀ i, (q i i).ule 2 = true) ∧
  (∑ i, q i i) = 6 ∧ (∃ i, s i = 3 ∧ q i i = 0) ∧
  (∀ i, s i = 3 → q i i = 0)

theorem degreeSixQuotientModel7_reindex
    (s : Fin 7 → DegreeSixCensusWord)
    (q : Fin 7 → Fin 7 → DegreeSixCensusWord)
    (e : Equiv.Perm (Fin 7)) (h : degreeSixQuotientModel7 s q) :
    degreeSixQuotientModel7 (fun i => s (e i)) (fun i j => q (e i) (e j)) := by
  rcases h with ⟨hs, hq, htotal, hrow, hbal, hsq, hdiag, htrace,
    hbase, hthree⟩
  refine ⟨fun i => hs (e i), fun i j => hq (e i) (e j), ?_, ?_,
    fun i j => hbal (e i) (e j), ?_, fun i => hdiag (e i), ?_, ?_, ?_⟩
  · exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans htotal
  · intro i
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans (hrow (e i))
  · intro i j
    change (∑ k, q (e i) (e k) * q (e k) (e j)) =
      (if i = j then 3 else 0) + s (e j)
    calc
      _ = ∑ k, q (e i) k * q k (e j) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by simpa only [e.injective.eq_iff] using hsq (e i) (e j)
  · change (∑ i, q (e i) (e i)) = 6
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans htrace
  · obtain ⟨i, hsi, hqi⟩ := hbase
    exact ⟨e.symm i, by simpa, by simpa⟩
  · intro i hi
    exact hthree (e i) hi

/-- Every seven-component degree-six quotient model has component orders
`3,3,3,6,6,6,6`. -/
theorem degreeSixQuotientModel7_profile_zero
    (s : Fin 7 → DegreeSixCensusWord)
    (q : Fin 7 → Fin 7 → DegreeSixCensusWord)
    (h : degreeSixQuotientModel7 s q) : s 0 = 3 ∨ s 0 = 6 := by
  simp [degreeSixQuotientModel7, Fin.forall_fin_succ, Fin.exists_fin_succ,
    Fin.sum_univ_succ] at h ⊢
  generalize s 0 = s0 at h ⊢
  generalize s 1 = s1 at h ⊢
  generalize s 2 = s2 at h ⊢
  generalize s 3 = s3 at h ⊢
  generalize s 4 = s4 at h ⊢
  generalize s 5 = s5 at h ⊢
  generalize s 6 = s6 at h ⊢
  generalize q 0 0 = q00 at h ⊢
  generalize q 0 1 = q01 at h ⊢
  generalize q 0 2 = q02 at h ⊢
  generalize q 0 3 = q03 at h ⊢
  generalize q 0 4 = q04 at h ⊢
  generalize q 0 5 = q05 at h ⊢
  generalize q 0 6 = q06 at h ⊢
  generalize q 1 0 = q10 at h ⊢
  generalize q 1 1 = q11 at h ⊢
  generalize q 1 2 = q12 at h ⊢
  generalize q 1 3 = q13 at h ⊢
  generalize q 1 4 = q14 at h ⊢
  generalize q 1 5 = q15 at h ⊢
  generalize q 1 6 = q16 at h ⊢
  generalize q 2 0 = q20 at h ⊢
  generalize q 2 1 = q21 at h ⊢
  generalize q 2 2 = q22 at h ⊢
  generalize q 2 3 = q23 at h ⊢
  generalize q 2 4 = q24 at h ⊢
  generalize q 2 5 = q25 at h ⊢
  generalize q 2 6 = q26 at h ⊢
  generalize q 3 0 = q30 at h ⊢
  generalize q 3 1 = q31 at h ⊢
  generalize q 3 2 = q32 at h ⊢
  generalize q 3 3 = q33 at h ⊢
  generalize q 3 4 = q34 at h ⊢
  generalize q 3 5 = q35 at h ⊢
  generalize q 3 6 = q36 at h ⊢
  generalize q 4 0 = q40 at h ⊢
  generalize q 4 1 = q41 at h ⊢
  generalize q 4 2 = q42 at h ⊢
  generalize q 4 3 = q43 at h ⊢
  generalize q 4 4 = q44 at h ⊢
  generalize q 4 5 = q45 at h ⊢
  generalize q 4 6 = q46 at h ⊢
  generalize q 5 0 = q50 at h ⊢
  generalize q 5 1 = q51 at h ⊢
  generalize q 5 2 = q52 at h ⊢
  generalize q 5 3 = q53 at h ⊢
  generalize q 5 4 = q54 at h ⊢
  generalize q 5 5 = q55 at h ⊢
  generalize q 5 6 = q56 at h ⊢
  generalize q 6 0 = q60 at h ⊢
  generalize q 6 1 = q61 at h ⊢
  generalize q 6 2 = q62 at h ⊢
  generalize q 6 3 = q63 at h ⊢
  generalize q 6 4 = q64 at h ⊢
  generalize q 6 5 = q65 at h ⊢
  generalize q 6 6 = q66 at h ⊢
  bv_decide (config := { timeout := 600 })

theorem degreeSixQuotientModel7_profile
    (s : Fin 7 → DegreeSixCensusWord)
    (q : Fin 7 → Fin 7 → DegreeSixCensusWord)
    (h : degreeSixQuotientModel7 s q) : ∀ i, s i = 3 ∨ s i = 6 := by
  intro i
  let e : Equiv.Perm (Fin 7) := Equiv.swap 0 i
  have h' := degreeSixQuotientModel7_profile_zero
    (fun j => s (e j)) (fun j k => q (e j) (e k))
      (degreeSixQuotientModel7_reindex s q e h)
  simpa [e] using h'

/-- Natural-number interface to the five-component finite certificate. -/
theorem degreeSixQuotientModel5_profile_nat
    (s : Fin 5 → ℕ) (q : Fin 5 → Fin 5 → ℕ)
    (hslo : ∀ i, 3 ≤ s i) (hshi : ∀ i, s i < 34)
    (hq : ∀ i j, q i j < 7)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2) (htrace : (∑ i, q i i) = 6)
    (hbase : ∃ i, s i = 3 ∧ q i i = 0)
    (hthree : ∀ i, s i = 3 → q i i = 0) :
    ∀ i, s i = 3 ∨ s i = 9 := by
  let sb : Fin 5 → DegreeSixCensusWord := fun i => s i
  let qb : Fin 5 → Fin 5 → DegreeSixCensusWord := fun i j => q i j
  have hmodel : degreeSixQuotientModel5 sb qb := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · rw [BitVec.ule_iff_toNat_le]
        have hi : s i < 2 ^ 8 := lt_trans (hshi i) (by norm_num)
        simp [sb, Nat.mod_eq_of_lt hi]
        have := hslo i
        omega
      · rw [BitVec.ult_iff_toNat_lt]
        simp [sb]
        have := hshi i
        omega
    · intro i j
      rw [BitVec.ult_iff_toNat_lt]
      simp [qb]
      have := hq i j
      omega
    · change (∑ i, (s i : DegreeSixCensusWord)) = 33
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) htotal
    · intro i
      change (∑ j, (q i j : DegreeSixCensusWord)) = 6
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hrow i)
    · intro i j
      change (s i : DegreeSixCensusWord) * (q i j : DegreeSixCensusWord) =
        (s j : DegreeSixCensusWord) * (q j i : DegreeSixCensusWord)
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hbal i j)
    · intro i j
      change (∑ k, (q i k : DegreeSixCensusWord) *
        (q k j : DegreeSixCensusWord)) =
          (if i = j then 3 else 0) + (s j : DegreeSixCensusWord)
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hsq i j)
    · intro i
      rw [BitVec.ule_iff_toNat_le]
      simp [qb]
      have := hdiag i
      omega
    · change (∑ i, (q i i : DegreeSixCensusWord)) = 6
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) htrace
    · obtain ⟨i, hsi, hqi⟩ := hbase
      exact ⟨i, by simp [sb, hsi], by simp [qb, hqi]⟩
    · intro i hi
      apply congrArg (fun n : ℕ => (n : DegreeSixCensusWord))
      apply hthree i
      have ht := congrArg BitVec.toNat hi
      simp [sb] at ht
      have := hshi i
      omega
  have hp := degreeSixQuotientModel5_profile sb qb hmodel
  intro i
  rcases hp i with hi | hi
  · left
    have ht := congrArg BitVec.toNat hi
    simp [sb] at ht
    have := hshi i
    omega
  · right
    have ht := congrArg BitVec.toNat hi
    simp [sb] at ht
    have := hshi i
    omega

/-- Natural-number interface to the seven-component finite certificate. -/
theorem degreeSixQuotientModel7_profile_nat
    (s : Fin 7 → ℕ) (q : Fin 7 → Fin 7 → ℕ)
    (hslo : ∀ i, 3 ≤ s i) (hshi : ∀ i, s i < 34)
    (hq : ∀ i j, q i j < 7)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2) (htrace : (∑ i, q i i) = 6)
    (hbase : ∃ i, s i = 3 ∧ q i i = 0)
    (hthree : ∀ i, s i = 3 → q i i = 0) :
    ∀ i, s i = 3 ∨ s i = 6 := by
  let sb : Fin 7 → DegreeSixCensusWord := fun i => s i
  let qb : Fin 7 → Fin 7 → DegreeSixCensusWord := fun i j => q i j
  have hmodel : degreeSixQuotientModel7 sb qb := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · rw [BitVec.ule_iff_toNat_le]
        have hi : s i < 2 ^ 8 := lt_trans (hshi i) (by norm_num)
        simp [sb, Nat.mod_eq_of_lt hi]
        have := hslo i
        omega
      · rw [BitVec.ult_iff_toNat_lt]
        simp [sb]
        have := hshi i
        omega
    · intro i j
      rw [BitVec.ult_iff_toNat_lt]
      simp [qb]
      have := hq i j
      omega
    · change (∑ i, (s i : DegreeSixCensusWord)) = 33
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) htotal
    · intro i
      change (∑ j, (q i j : DegreeSixCensusWord)) = 6
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hrow i)
    · intro i j
      change (s i : DegreeSixCensusWord) * (q i j : DegreeSixCensusWord) =
        (s j : DegreeSixCensusWord) * (q j i : DegreeSixCensusWord)
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hbal i j)
    · intro i j
      change (∑ k, (q i k : DegreeSixCensusWord) *
        (q k j : DegreeSixCensusWord)) =
          (if i = j then 3 else 0) + (s j : DegreeSixCensusWord)
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) (hsq i j)
    · intro i
      rw [BitVec.ule_iff_toNat_le]
      simp [qb]
      have := hdiag i
      omega
    · change (∑ i, (q i i : DegreeSixCensusWord)) = 6
      norm_cast
      exact congrArg (fun n : ℕ => (n : DegreeSixCensusWord)) htrace
    · obtain ⟨i, hsi, hqi⟩ := hbase
      exact ⟨i, by simp [sb, hsi], by simp [qb, hqi]⟩
    · intro i hi
      apply congrArg (fun n : ℕ => (n : DegreeSixCensusWord))
      apply hthree i
      have ht := congrArg BitVec.toNat hi
      simp [sb] at ht
      have := hshi i
      omega
  have hp := degreeSixQuotientModel7_profile sb qb hmodel
  intro i
  rcases hp i with hi | hi
  · left
    have ht := congrArg BitVec.toNat hi
    simp [sb] at ht
    have := hshi i
    omega
  · right
    have ht := congrArg BitVec.toNat hi
    simp [sb] at ht
    have := hshi i
    omega

/-- Transport the five-component certificate across an arbitrary finite
index type. -/
theorem degreeSixQuotientProfile5_of_fintype
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ)
    (hcard : Fintype.card C = 5)
    (hslo : ∀ i, 3 ≤ s i) (hshi : ∀ i, s i < 34)
    (hq : ∀ i j, q i j < 7)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2) (htrace : (∑ i, q i i) = 6)
    (hbase : ∃ i, s i = 3 ∧ q i i = 0)
    (hthree : ∀ i, s i = 3 → q i i = 0) :
    ∀ i, s i = 3 ∨ s i = 9 := by
  let e : C ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let sf : Fin 5 → ℕ := fun i => s (e.symm i)
  let qf : Fin 5 → Fin 5 → ℕ := fun i j => q (e.symm i) (e.symm j)
  have hp := degreeSixQuotientModel5_profile_nat sf qf
    (fun i => hslo (e.symm i)) (fun i => hshi (e.symm i))
    (fun i j => hq (e.symm i) (e.symm j))
    (by change (∑ i, s (e.symm i)) = 33
        simpa only [e.symm.sum_comp] using htotal)
    (fun i => by change (∑ j, q (e.symm i) (e.symm j)) = 6
                 simpa only [e.symm.sum_comp] using hrow (e.symm i))
    (fun i j => hbal (e.symm i) (e.symm j))
    (fun i j => by
      change (∑ k, q (e.symm i) (e.symm k) * q (e.symm k) (e.symm j)) =
        (if i = j then 3 else 0) + s (e.symm j)
      rw [e.symm.sum_comp
        (fun k => q (e.symm i) k * q k (e.symm j))]
      simpa using hsq (e.symm i) (e.symm j))
    (fun i => hdiag (e.symm i))
    (by change (∑ i, q (e.symm i) (e.symm i)) = 6
        rw [e.symm.sum_comp (fun i => q i i)]
        exact htrace)
    (by obtain ⟨i, hsi, hqi⟩ := hbase
        exact ⟨e i, by simpa [sf], by simpa [qf]⟩)
    (fun i hi => hthree (e.symm i) hi)
  intro i
  simpa [sf] using hp (e i)

/-- Transport the seven-component certificate across an arbitrary finite
index type. -/
theorem degreeSixQuotientProfile7_of_fintype
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ)
    (hcard : Fintype.card C = 7)
    (hslo : ∀ i, 3 ≤ s i) (hshi : ∀ i, s i < 34)
    (hq : ∀ i j, q i j < 7)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2) (htrace : (∑ i, q i i) = 6)
    (hbase : ∃ i, s i = 3 ∧ q i i = 0)
    (hthree : ∀ i, s i = 3 → q i i = 0) :
    ∀ i, s i = 3 ∨ s i = 6 := by
  let e : C ≃ Fin 7 := Fintype.equivFinOfCardEq hcard
  let sf : Fin 7 → ℕ := fun i => s (e.symm i)
  let qf : Fin 7 → Fin 7 → ℕ := fun i j => q (e.symm i) (e.symm j)
  have hp := degreeSixQuotientModel7_profile_nat sf qf
    (fun i => hslo (e.symm i)) (fun i => hshi (e.symm i))
    (fun i j => hq (e.symm i) (e.symm j))
    (by change (∑ i, s (e.symm i)) = 33
        simpa only [e.symm.sum_comp] using htotal)
    (fun i => by change (∑ j, q (e.symm i) (e.symm j)) = 6
                 simpa only [e.symm.sum_comp] using hrow (e.symm i))
    (fun i j => hbal (e.symm i) (e.symm j))
    (fun i j => by
      change (∑ k, q (e.symm i) (e.symm k) * q (e.symm k) (e.symm j)) =
        (if i = j then 3 else 0) + s (e.symm j)
      rw [e.symm.sum_comp
        (fun k => q (e.symm i) k * q k (e.symm j))]
      simpa using hsq (e.symm i) (e.symm j))
    (fun i => hdiag (e.symm i))
    (by change (∑ i, q (e.symm i) (e.symm i)) = 6
        rw [e.symm.sum_comp (fun i => q i i)]
        exact htrace)
    (by obtain ⟨i, hsi, hqi⟩ := hbase
        exact ⟨e i, by simpa [sf], by simpa [qf]⟩)
    (fun i hi => hthree (e.symm i) hi)
  intro i
  simpa [sf] using hp (e i)

end Erdos85
