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

/-- Restrict the base row and every base-started two-step sum to its positive
support.  This is the algebraic router used by the branchwise Model5 proof:
once the support Finset is named, the full quotient-square equations expand
over only one, two, or three terms. -/
theorem degreeSixQuotient_orderThree_support_equations_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    (∑ j ∈ P, q c j) = 6 ∧
      ∀ j, (∑ k ∈ P, q c k * q k j) =
        (if c = j then 3 else 0) + s j := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  have hsupport (f : C → ℕ) :
      (∑ j ∈ P, q c j * f j) = ∑ j, q c j * f j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : q c j = 0 := by
      by_contra hn
      exact hj (by simp [Nat.pos_of_ne_zero hn])
    simp [hz]
  constructor
  · calc
      (∑ j ∈ P, q c j) = ∑ j ∈ P, q c j * 1 := by simp
      _ = ∑ j, q c j * 1 := hsupport (fun _ ↦ 1)
      _ = 6 := by simpa using hrow c
  · intro j
    calc
      (∑ k ∈ P, q c k * q k j) = ∑ k, q c k * q k j :=
        hsupport (fun k ↦ q k j)
      _ = (if c = j then 3 else 0) + s j := hsq c j

/-- Cardinality form of the base support partition.  Positive and invisible
support are both nonempty and together contain every component except the
base. -/
theorem degreeSixQuotient_orderThree_support_card_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C) (n : ℕ)
    (hspos : ∀ i, 0 < s i)
    (hcard : Fintype.card C = n)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    let R := (Finset.univ.erase c) \ P
    P.card + R.card = n - 1 ∧ 0 < P.card ∧ 0 < R.card := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  let R : Finset C := (Finset.univ.erase c) \ P
  obtain ⟨hPmass, hRmass⟩ :=
    degreeSixQuotient_orderThree_support_partition_nat
      s q c hspos htotal hrow hbal hsq hc3 hcc
  change (∑ j ∈ P, s j) = 18 at hPmass
  change (∑ j ∈ R, s j) = 12 at hRmass
  have hcnotP : c ∉ P := by simp [P, hcc]
  have hPsub : P ⊆ Finset.univ.erase c := by
    intro j hj
    exact Finset.mem_erase.mpr
      ⟨fun hjc ↦ hcnotP (hjc ▸ hj), Finset.mem_univ j⟩
  have hparts : P.card + R.card = n - 1 := by
    have herase : (Finset.univ.erase c : Finset C).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
        hcard]
    have hpCard : P.card ≤ n - 1 := by
      rw [← herase]
      exact Finset.card_le_card hPsub
    dsimp [R]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub, herase]
    omega
  have hPpos : 0 < P.card := by
    by_contra hn
    push Not at hn
    have hz : P = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz] at hPmass
    simp at hPmass
  have hRpos : 0 < R.card := by
    by_contra hn
    push Not at hn
    have hz : R = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz] at hRmass
    simp at hRmass
  exact ⟨hparts, hPpos, hRpos⟩

/-- At five components the positive/invisible support split is `1+3`,
`2+2`, or `3+1`. -/
theorem degreeSixQuotient_orderThree_support_card_five_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (hcard : Fintype.card C = 5)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    let R := (Finset.univ.erase c) \ P
    (P.card = 1 ∧ R.card = 3) ∨
      (P.card = 2 ∧ R.card = 2) ∨
      (P.card = 3 ∧ R.card = 1) := by
  have h := degreeSixQuotient_orderThree_support_card_nat
    s q c 5 hspos hcard htotal hrow hbal hsq hc3 hcc
  dsimp only at h ⊢
  omega

/-- At seven components the positive/invisible support split is `2+4`,
`3+3`, `4+2`, or `5+1`; later trace and square constraints remove the two
outer cases. -/
theorem degreeSixQuotient_orderThree_support_card_seven_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hslo : ∀ i, 3 ≤ s i)
    (hcard : Fintype.card C = 7)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    let R := (Finset.univ.erase c) \ P
    (P.card = 2 ∧ R.card = 4) ∨
      (P.card = 3 ∧ R.card = 3) ∨
      (P.card = 4 ∧ R.card = 2) ∨
      (P.card = 5 ∧ R.card = 1) := by
  let P := Finset.univ.filter fun j ↦ 0 < q c j
  let R := (Finset.univ.erase c) \ P
  have hspos : ∀ i, 0 < s i := fun i ↦ by have := hslo i; omega
  have h := degreeSixQuotient_orderThree_support_card_nat
    s q c 7 hspos hcard htotal hrow hbal hsq hc3 hcc
  change P.card + R.card = 7 - 1 ∧ 0 < P.card ∧ 0 < R.card at h
  have hPle : P.card ≤ 6 := by
    have hmass := (degreeSixQuotient_orderThree_support_partition_nat
      s q c hspos htotal hrow hbal hsq hc3 hcc).1
    change (∑ j ∈ P, s j) = 18 at hmass
    have hlo : 3 * P.card ≤ ∑ j ∈ P, s j := by
      calc
        3 * P.card = ∑ _j ∈ P, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ j ∈ P, s j := Finset.sum_le_sum fun j _ ↦ hslo j
    omega
  have hRle : R.card ≤ 4 := by
    have hmass := (degreeSixQuotient_orderThree_support_partition_nat
      s q c hspos htotal hrow hbal hsq hc3 hcc).2
    change (∑ j ∈ R, s j) = 12 at hmass
    have hlo : 3 * R.card ≤ ∑ j ∈ R, s j := by
      calc
        3 * R.card = ∑ _j ∈ R, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ j ∈ R, s j := Finset.sum_le_sum fun j _ ↦ hslo j
    omega
  change (P.card = 2 ∧ R.card = 4) ∨
    (P.card = 3 ∧ R.card = 3) ∨
    (P.card = 4 ∧ R.card = 2) ∨
    (P.card = 5 ∧ R.card = 1)
  omega

/-- A Model5 base triangle cannot have one-element positive support.  The
unique target would have order eighteen and forward quotient six; its
off-diagonal square equation would then force diagonal quotient three. -/
theorem false_of_degreeSixQuotient_orderThree_support_card_one_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2)
    (hc3 : s c = 3) (hcc : q c c = 0)
    (hPcard : (Finset.univ.filter fun j ↦ 0 < q c j).card = 1) : False := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  have hPcard' : P.card = 1 := by simpa [P] using hPcard
  obtain ⟨a, hPa⟩ := Finset.card_eq_one.mp hPcard'
  have hmass := (degreeSixQuotient_orderThree_support_partition_nat
    s q c hspos htotal hrow hbal hsq hc3 hcc).1
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  change (∑ j ∈ P, s j) = 18 at hmass
  change (∑ j ∈ P, q c j) = 6 ∧
    ∀ j, (∑ k ∈ P, q c k * q k j) =
      (if c = j then 3 else 0) + s j at heqs
  have hac : a ≠ c := by
    intro h
    subst a
    have hcP : c ∈ P := by rw [hPa]; simp
    exact (by simpa [P, hcc] using hcP)
  rw [hPa] at hmass heqs
  simp only [Finset.sum_singleton] at hmass heqs
  have hqca : q c a = 6 := heqs.1
  have hsqA := heqs.2 a
  simp [Ne.symm hac] at hsqA
  rw [hqca, hmass] at hsqA
  have hdiagA := hdiag a
  omega

/-- A Model5 base triangle cannot have three-element positive support and a
singleton invisible support.  Summed detailed balance turns the base-to-
invisible square equation into invisible-to-support row mass three; the
singleton complement then forces diagonal quotient three. -/
theorem false_of_degreeSixQuotient_orderThree_support_card_three_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2)
    (hc3 : s c = 3) (hcc : q c c = 0)
    (hPcard : (Finset.univ.filter fun j ↦ 0 < q c j).card = 3)
    (hRcard : ((Finset.univ.erase c) \
      (Finset.univ.filter fun j ↦ 0 < q c j)).card = 1) : False := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  let R : Finset C := (Finset.univ.erase c) \ P
  have hPcard' : P.card = 3 := by simpa [P] using hPcard
  have hRcard' : R.card = 1 := by simpa [P, R] using hRcard
  obtain ⟨r, hRr⟩ := Finset.card_eq_one.mp hRcard'
  have hrR : r ∈ R := by rw [hRr]; simp
  have hrc : r ≠ c := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hrR).1).1
  have hrnotP : r ∉ P := (Finset.mem_sdiff.mp hrR).2
  have hqcr : q c r = 0 := by
    by_contra hn
    exact hrnotP (by simp [P, Nat.pos_of_ne_zero hn])
  have hqrc : q r c = 0 := by
    have hb := hbal c r
    rw [hqcr, mul_zero] at hb
    exact (Nat.mul_eq_zero.mp hb.symm).resolve_left
      (Nat.ne_of_gt (hspos r))
  have hprofile := degreeSixQuotient_orderThree_zeroDiagonal_profile_nat
    s q c hspos hrow hbal hsq hc3 hcc
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  change (∑ j ∈ P, q c j) = 6 ∧
    ∀ j, (∑ k ∈ P, q c k * q k j) =
      (if c = j then 3 else 0) + s j at heqs
  have hsqR := heqs.2 r
  simp [Ne.symm hrc] at hsqR
  have hweighted :
      3 * (∑ p ∈ P, q c p * q p r) =
        s r * (∑ p ∈ P, q r p) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPos : 0 < q c p := by simpa [P] using
      (Finset.mem_filter.mp hp).2
    have hpSize := (hprofile p hpPos).2
    calc
      3 * (q c p * q p r) = (3 * q c p) * q p r := by
        rw [Nat.mul_assoc]
      _ = s p * q p r := by rw [← hpSize]
      _ = s r * q r p := hbal p r
  rw [hsqR] at hweighted
  have hsupportR : (∑ p ∈ P, q r p) = 3 := by
    have hcancel : 3 = ∑ p ∈ P, q r p := by
      apply Nat.eq_of_mul_eq_mul_left (hspos r)
      simpa [Nat.mul_comm] using hweighted
    exact hcancel.symm
  have hcnotP : c ∉ P := by simp [P, hcc]
  have hPsub : P ⊆ Finset.univ.erase c := by
    intro p hp
    exact Finset.mem_erase.mpr
      ⟨fun hpc ↦ hcnotP (hpc ▸ hp), Finset.mem_univ p⟩
  have hsplit : (∑ j ∈ R, q r j) + (∑ j ∈ P, q r j) =
      ∑ j ∈ Finset.univ.erase c, q r j := by
    exact Finset.sum_sdiff hPsub
  have houtside := Finset.sum_erase_add
    (Finset.univ : Finset C) (q r) (Finset.mem_univ c)
  rw [hRr] at hsplit
  simp only [Finset.sum_singleton] at hsplit
  have hrowR := hrow r
  change (∑ j ∈ (Finset.univ : Finset C), q r j) = 6 at hrowR
  have hdiagR := hdiag r
  omega

/-- Name the two positive targets of an order-three base row.  Their forward
weights are positive and sum to six, their reverse quotients are one, and
their orders are three times those weights. -/
theorem degreeSixQuotient_orderThree_support_two_names_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hspos : ∀ i, 0 < s i)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0)
    (hPcard : (Finset.univ.filter fun j ↦ 0 < q c j).card = 2) :
    ∃ a b, a ≠ b ∧
      (Finset.univ.filter fun j ↦ 0 < q c j) = {a, b} ∧
      0 < q c a ∧ 0 < q c b ∧ q c a + q c b = 6 ∧
      q a c = 1 ∧ q b c = 1 ∧
      s a = 3 * q c a ∧ s b = 3 * q c b := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  have hPcard' : P.card = 2 := by simpa [P] using hPcard
  obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp hPcard'
  have haP : a ∈ P := by rw [hP]; simp
  have hbP : b ∈ P := by rw [hP]; simp
  have haPos : 0 < q c a := by simpa [P] using
    (Finset.mem_filter.mp haP).2
  have hbPos : 0 < q c b := by simpa [P] using
    (Finset.mem_filter.mp hbP).2
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  change (∑ j ∈ P, q c j) = 6 ∧
    ∀ j, (∑ k ∈ P, q c k * q k j) =
      (if c = j then 3 else 0) + s j at heqs
  have hweights : q c a + q c b = 6 := by
    rw [hP] at heqs
    simpa [hab] using heqs.1
  have hprofile := degreeSixQuotient_orderThree_zeroDiagonal_profile_nat
    s q c hspos hrow hbal hsq hc3 hcc
  have haData := hprofile a haPos
  have hbData := hprofile b hbPos
  refine ⟨a, b, hab, ?_, haPos, hbPos, hweights,
    haData.1, hbData.1, haData.2, hbData.2⟩
  simpa [P] using hP

/-- The two positive base weights are `2+4`, `3+3`, or `4+2`.  The square
equations restricted to the named support, combined with detailed balance,
force `qaa + qab = qbb + qba = 3`; this excludes the extreme `1+5` and
`5+1` splits under the diagonal bound. -/
theorem degreeSixQuotient_orderThree_support_two_weight_cases_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c a b : C)
    (hab : a ≠ b)
    (hP : (Finset.univ.filter fun j ↦ 0 < q c j) = {a, b})
    (haPos : 0 < q c a) (hbPos : 0 < q c b)
    (hweights : q c a + q c b = 6)
    (haSize : s a = 3 * q c a) (hbSize : s b = 3 * q c b)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2) (hcc : q c c = 0) :
    (q c a = 2 ∧ q c b = 4) ∨
      (q c a = 3 ∧ q c b = 3) ∨
      (q c a = 4 ∧ q c b = 2) := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  have hP' : P = {a, b} := by simpa [P] using hP
  have hca : c ≠ a := by
    intro h
    subst a
    rw [hcc] at haPos
    omega
  have hcb : c ≠ b := by
    intro h
    subst b
    rw [hcc] at hbPos
    omega
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  change (∑ j ∈ P, q c j) = 6 ∧
    ∀ j, (∑ k ∈ P, q c k * q k j) =
      (if c = j then 3 else 0) + s j at heqs
  have hsqA := heqs.2 a
  have hsqB := heqs.2 b
  rw [hP'] at hsqA hsqB
  simp [hab, hca, hcb] at hsqA hsqB
  rw [haSize] at hsqA
  rw [hbSize] at hsqB
  have hbalAB := hbal a b
  rw [haSize, hbSize] at hbalAB
  have hcross : q c a * q a b = q c b * q b a := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    simpa [Nat.mul_assoc] using hbalAB
  have hrowA : q a a + q a b = 3 := by
    apply Nat.eq_of_mul_eq_mul_left haPos
    calc
      q c a * (q a a + q a b) =
          q c a * q a a + q c a * q a b := Nat.mul_add _ _ _
      _ = q c a * q a a + q c b * q b a := by rw [hcross]
      _ = 3 * q c a := hsqA
      _ = q c a * 3 := Nat.mul_comm _ _
  have hrowB : q b b + q b a = 3 := by
    apply Nat.eq_of_mul_eq_mul_left hbPos
    calc
      q c b * (q b b + q b a) =
          q c b * q b b + q c b * q b a := Nat.mul_add _ _ _
      _ = q c b * q b b + q c a * q a b := by rw [hcross]
      _ = 3 * q c b := by omega
      _ = q c b * 3 := Nat.mul_comm _ _
  have haDiag := hdiag a
  have hbDiag := hdiag b
  have hcases : q c a = 1 ∨ q c a = 2 ∨ q c a = 3 ∨
      q c a = 4 ∨ q c a = 5 := by omega
  rcases hcases with h | h | h | h | h
  · exfalso
    rw [h] at hweights hcross
    have hb : q c b = 5 := by omega
    rw [hb] at hcross
    omega
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl ⟨h, by omega⟩)
  · exact Or.inr (Or.inr ⟨h, by omega⟩)
  · exfalso
    rw [h] at hweights hcross
    have hb : q c b = 1 := by omega
    rw [hb] at hcross
    omega

/-- Once the two positive Model5 weights are `3+3`, name the two invisible
components.  Each invisible order is a threefold base-started two-step sum,
while their total order is twelve, leaving exactly `3+9`, `6+6`, or `9+3`. -/
theorem degreeSixQuotient_model5_invisible_order_cases_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c a b r t : C)
    (hslo : ∀ i, 3 ≤ s i)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hc3 : s c = 3) (hcc : q c c = 0)
    (hP : (Finset.univ.filter fun j ↦ 0 < q c j) = {a, b})
    (hR : ((Finset.univ.erase c) \
      (Finset.univ.filter fun j ↦ 0 < q c j)) = {r, t})
    (hab : a ≠ b) (hrt : r ≠ t)
    (hca : q c a = 3) (hcb : q c b = 3) :
    (s r = 3 ∧ s t = 9) ∨ (s r = 6 ∧ s t = 6) ∨
      (s r = 9 ∧ s t = 3) := by
  have hspos : ∀ i, 0 < s i := fun i ↦ by have := hslo i; omega
  have hmass := (degreeSixQuotient_orderThree_support_partition_nat
    s q c hspos htotal hrow hbal hsq hc3 hcc).2
  rw [hR] at hmass
  simp [hrt] at hmass
  have hrMem : r ∈ ((Finset.univ.erase c) \
      (Finset.univ.filter fun j ↦ 0 < q c j)) := by rw [hR]; simp
  have hrc : r ≠ c :=
    (Finset.mem_erase.mp (Finset.mem_sdiff.mp hrMem).1).1
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  have hsqR := heqs.2 r
  rw [hP] at hsqR
  rw [Finset.sum_pair hab] at hsqR
  simp [Ne.symm hrc, hca, hcb] at hsqR
  have hrlo := hslo r
  have htlo := hslo t
  omega

/-- Under the full Model5 incidence hypotheses, a chosen order-three base
has exactly two positive and two invisible targets.  This composes the
support-cardinality census with the kernel-clean contradictions for the
`1+3` and `3+1` branches. -/
theorem degreeSixQuotient_model5_support_card_two_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hslo : ∀ i, 3 ≤ s i)
    (hcard : Fintype.card C = 5)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    let P := Finset.univ.filter fun j ↦ 0 < q c j
    let R := (Finset.univ.erase c) \ P
    P.card = 2 ∧ R.card = 2 := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  let R : Finset C := (Finset.univ.erase c) \ P
  have hspos : ∀ i, 0 < s i := fun i ↦ by have := hslo i; omega
  have hcases := degreeSixQuotient_orderThree_support_card_five_nat
    s q c hspos hcard htotal hrow hbal hsq hc3 hcc
  change (P.card = 1 ∧ R.card = 3) ∨
    (P.card = 2 ∧ R.card = 2) ∨
    (P.card = 3 ∧ R.card = 1) at hcases
  rcases hcases with h | h | h
  · exact (false_of_degreeSixQuotient_orderThree_support_card_one_nat
      s q c hspos htotal hrow hbal hsq hdiag hc3 hcc
        (by simpa [P] using h.1)).elim
  · exact h
  · exact (false_of_degreeSixQuotient_orderThree_support_card_three_nat
      s q c hspos hrow hbal hsq hdiag hc3 hcc
        (by simpa [P] using h.1) (by simpa [P, R] using h.2)).elim

/-- Name both halves of the forced Model5 `2+2` support split and expose the
positive weights, reverse quotients, and orders. -/
theorem degreeSixQuotient_model5_support_names_nat
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (q : C → C → ℕ) (c : C)
    (hslo : ∀ i, 3 ≤ s i)
    (hcard : Fintype.card C = 5)
    (htotal : (∑ i, s i) = 33)
    (hrow : ∀ i, (∑ j, q i j) = 6)
    (hbal : ∀ i j, s i * q i j = s j * q j i)
    (hsq : ∀ i j, (∑ k, q i k * q k j) =
      (if i = j then 3 else 0) + s j)
    (hdiag : ∀ i, q i i ≤ 2)
    (hc3 : s c = 3) (hcc : q c c = 0) :
    ∃ a b r t, a ≠ b ∧ r ≠ t ∧
      (Finset.univ.filter fun j ↦ 0 < q c j) = {a, b} ∧
      ((Finset.univ.erase c) \
        (Finset.univ.filter fun j ↦ 0 < q c j)) = {r, t} ∧
      0 < q c a ∧ 0 < q c b ∧ q c a + q c b = 6 ∧
      q a c = 1 ∧ q b c = 1 ∧
      s a = 3 * q c a ∧ s b = 3 * q c b := by
  let P : Finset C := Finset.univ.filter fun j ↦ 0 < q c j
  let R : Finset C := (Finset.univ.erase c) \ P
  have hspos : ∀ i, 0 < s i := fun i ↦ by have := hslo i; omega
  have hcards := degreeSixQuotient_model5_support_card_two_nat
    s q c hslo hcard htotal hrow hbal hsq hdiag hc3 hcc
  change P.card = 2 ∧ R.card = 2 at hcards
  obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp hcards.1
  obtain ⟨r, t, hrt, hR⟩ := Finset.card_eq_two.mp hcards.2
  have haP : a ∈ P := by rw [hP]; simp
  have hbP : b ∈ P := by rw [hP]; simp
  have haPos : 0 < q c a := by simpa [P] using
    (Finset.mem_filter.mp haP).2
  have hbPos : 0 < q c b := by simpa [P] using
    (Finset.mem_filter.mp hbP).2
  have heqs := degreeSixQuotient_orderThree_support_equations_nat
    s q c hrow hsq
  change (∑ j ∈ P, q c j) = 6 ∧
    ∀ j, (∑ k ∈ P, q c k * q k j) =
      (if c = j then 3 else 0) + s j at heqs
  have hweights : q c a + q c b = 6 := by
    rw [hP, Finset.sum_pair hab] at heqs
    exact heqs.1
  have hprofile := degreeSixQuotient_orderThree_zeroDiagonal_profile_nat
    s q c hspos hrow hbal hsq hc3 hcc
  have haData := hprofile a haPos
  have hbData := hprofile b hbPos
  exact ⟨a, b, r, t, hab, hrt, by simpa [P] using hP,
    by simpa [P, R] using hR, haPos, hbPos, hweights,
    haData.1, hbData.1, haData.2, hbData.2⟩

/-- Arithmetic endpoint for the only nontrivial competing Model5 support
weights.  After a base triangle has positive-support weights `2+4`, name the
two invisible component orders `x,y`, their contacts with the two positive
components, and their residual `2×2` quotient block.  Balance, row sum,
trace, and one diagonal square equation are already inconsistent. -/
theorem false_of_degreeSixQuotient_model5_two_four_split
    (x y u v ra rb ta tb rr rt tr tt : ℕ)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hxy : x + y = 12)
    (hu : u ≤ 2) (hv : v ≤ 2)
    (hcx : 2 * u + 4 * v = x)
    (hrau : 6 * u = x * ra) (hrbv : 12 * v = x * rb)
    (htau : 6 * (2 - u) = y * ta)
    (htbv : 12 * (2 - v) = y * tb)
    (hrowr : ra + rb + rr + rt = 6)
    (hrowt : ta + tb + tr + tt = 6)
    (hrtb : x * rt = y * tr)
    (htrace : rr + tt = 3)
    (hsqr : ra * u + rb * v + rr * rr + rt * tr = x + 3) : False := by
  have hcases :
      (x = 4 ∧ y = 8 ∧ u = 0 ∧ v = 1) ∨
      (x = 8 ∧ y = 4 ∧ u = 0 ∧ v = 2) ∨
      (x = 6 ∧ y = 6 ∧ u = 1 ∧ v = 1) ∨
      (x = 4 ∧ y = 8 ∧ u = 2 ∧ v = 0) ∨
      (x = 8 ∧ y = 4 ∧ u = 2 ∧ v = 1) := by
    clear hrau hrbv htau htbv hrowr hrowt hrtb htrace hsqr
    interval_cases u <;> interval_cases v <;> omega
  rcases hcases with h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at htau
    omega
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at hrau hrbv htau htbv
    have hra : ra = 0 := by omega
    have hrb : rb = 3 := by omega
    have hta : ta = 3 := by omega
    have htb : tb = 0 := by omega
    subst ra; subst rb; subst ta; subst tb
    norm_num at hrowr hrowt hrtb htrace hsqr
    nlinarith
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at hrau hrbv htau htbv
    have hra : ra = 1 := by omega
    have hrb : rb = 2 := by omega
    have hta : ta = 1 := by omega
    have htb : tb = 2 := by omega
    subst ra; subst rb; subst ta; subst tb
    norm_num at hrowr hrowt hrtb htrace hsqr
    omega
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at hrau hrbv htau htbv
    have hra : ra = 3 := by omega
    have hrb : rb = 0 := by omega
    have hta : ta = 0 := by omega
    have htb : tb = 3 := by omega
    subst ra; subst rb; subst ta; subst tb
    norm_num at hrowr hrowt hrtb htrace hsqr
    nlinarith
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at hrau
    omega

/-- Arithmetic endpoint excluding the residual invisible-order split `6+6`
after Model5's positive support has weights `3+3`.  Balance makes each
order-six component meet exactly one order-nine component with forward and
reverse multiplicities `2` and `3`.  Equal-size symmetry and trace then
contradict the diagonal square equation. -/
theorem false_of_degreeSixQuotient_model5_invisible_six_six
    (ar br au bu ra rb ta tb d rr rt tr tt : ℕ)
    (hrContact : ar + br = 2) (htContact : au + bu = 2)
    (hbalAR : 3 * ar = 2 * ra) (hbalBR : 3 * br = 2 * rb)
    (hbalAT : 3 * au = 2 * ta) (hbalBT : 3 * bu = 2 * tb)
    (hrowR : ra + rb + rr + rt = 6)
    (hrowT : ta + tb + tr + tt = 6)
    (hRT : rt = tr) (htrace : 2 * d + rr + tt = 6)
    (hsqR : ra * ar + rb * br + rr * rr + rt * tr = 9) : False := by
  have hrCases :
      (ar = 0 ∧ br = 2 ∧ ra = 0 ∧ rb = 3) ∨
      (ar = 2 ∧ br = 0 ∧ ra = 3 ∧ rb = 0) := by
    omega
  have htCases :
      (au = 0 ∧ bu = 2 ∧ ta = 0 ∧ tb = 3) ∨
      (au = 2 ∧ bu = 0 ∧ ta = 3 ∧ tb = 0) := by
    omega
  rcases hrCases with hr | hr <;> rcases htCases with ht | ht
  all_goals
    rcases hr with ⟨rfl, rfl, rfl, rfl⟩
    rcases ht with ⟨rfl, rfl, rfl, rfl⟩
    norm_num at hrowR hrowT hsqR
    subst tr
    have hdiag : d + rr = 3 := by omega
    have hrt : rt = d := by omega
    rw [hrt] at hsqR
    have hdle : d ≤ 3 := by omega
    have hrrle : rr ≤ 3 := by omega
    interval_cases d <;> interval_cases rr <;> omega

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
