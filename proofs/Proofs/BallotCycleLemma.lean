import Mathlib.Tactic

/-
# Cycle Lemma for Generalized Ballot Sequences (Dvoretzky-Motzkin, 1947)

## Research Problem: ballot-problem-oq-01

This file proves the Cycle Lemma: for a ballot sequence with `a` copies of +1
and `b` copies of -k (where a > k*b), exactly `a - k*b` of the `a + b` cyclic
rotations are "good" (have all prefix sums positive).

This is the key combinatorial result needed for the Generalized Ballot Theorem,
which extends Bertrand's classical ballot problem to k-fold dominance.

## Approach
- Model vote counting as lists with entries +1 and -k
- Define cyclic rotations and good rotations via prefix sums
- Prove upper bound via injection into integer levels
- Prove lower bound via discrete IVT + rightmost-at-level argument

## References
- Dvoretzky & Motzkin (1947): Cycle lemma
- Renault (2007): "Four Proofs of the Ballot Theorem"
-/

namespace BallotCycleLemma

open List Set

/- ## Ballot Sequences -/

def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = a ∧ l.count (-(k : ℤ)) = b ∧ ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)}

/- ## Core Algebraic Lemmas -/

theorem sum_eq_count_sub_mul_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.sum = (l.count 1 : ℤ) - (k : ℤ) * (l.count (-(k : ℤ))) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons.mpr (Or.inr hy))
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.sum_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · simp [hne]; omega
    · simp [hne.symm]; ring

theorem length_eq_count_add_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.length = l.count 1 + l.count (-(k : ℤ)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons.mpr (Or.inr hy))
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.length_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · simp [hne]; omega
    · simp [hne.symm]; omega

/- ## Properties of kCountedSequence -/

theorem kCountedSequence_sum {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.sum = (a : ℤ) - k * b := by
  have h := sum_eq_count_sub_mul_count hl.2.2
  rw [hl.1, hl.2.1] at h; exact h

theorem kCountedSequence_length {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.length = a + b := by
  have h := length_eq_count_add_count hl.2.2
  rw [hl.1, hl.2.1] at h; exact h

theorem kCountedSequence_pos_sum {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    0 < l.sum := by rw [kCountedSequence_sum hl]; omega

/- ## Cyclic Rotations -/

def cyclicRotation (l : List ℤ) (i : ℕ) : List ℤ :=
  l.drop i ++ l.take i

theorem cyclicRotation_sum (l : List ℤ) (i : ℕ) :
    (cyclicRotation l i).sum = l.sum := by
  simp only [cyclicRotation, List.sum_append]
  have h := congr_arg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h; omega

theorem cyclicRotation_length (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    (cyclicRotation l i).length = l.length := by
  simp [cyclicRotation, List.length_drop, List.length_take, Nat.min_eq_left hi]; omega

theorem cyclicRotation_mem_kCountedSequence {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (i : ℕ) (_hi : i ≤ l.length) :
    cyclicRotation l i ∈ kCountedSequence k a b := by
  have ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count 1) (List.take_append_drop i l)
    rw [List.count_append] at this; omega
  · simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count (-(k : ℤ))) (List.take_append_drop i l)
    rw [List.count_append] at this; omega
  · intro x hx; rw [cyclicRotation, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h3 x (List.drop_subset i l hx)
    · exact h3 x (List.take_subset i l hx)

/- ## Prefix Sums -/

def prefixSum (l : List ℤ) (i : ℕ) : ℤ := (l.take i).sum

theorem prefixSum_zero (l : List ℤ) : prefixSum l 0 = 0 := by simp [prefixSum]

theorem prefixSum_length (l : List ℤ) : prefixSum l l.length = l.sum := by
  simp [prefixSum, List.take_length]

private theorem sum_drop_eq (l : List ℤ) (i : ℕ) :
    (l.drop i).sum = l.sum - (l.take i).sum := by
  have h := congr_arg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h; omega

private theorem take_drop_sum (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hij : i + j ≤ l.length) :
    ((l.drop i).take j).sum = (l.take (i + j)).sum - (l.take i).sum := by
  have key : l.take (i + j) = l.take i ++ (l.drop i).take j := by
    rw [← List.take_append_drop i l]
    rw [List.take_append_eq_append_take]
    simp [List.length_take, Nat.min_eq_left hi]
    rw [List.take_take]
    congr 1; omega
  have := congr_arg List.sum key
  rw [List.sum_append] at this; omega

theorem cyclicRotation_prefixSum (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hj : j ≤ l.length) :
    ((cyclicRotation l i).take j).sum =
      if i + j ≤ l.length then
        (l.take (i + j)).sum - (l.take i).sum
      else
        (l.take (i + j - l.length)).sum + l.sum - (l.take i).sum := by
  simp only [cyclicRotation]
  by_cases hij : i + j ≤ l.length
  · simp only [hij, ↓reduceIte]
    have hj_le : j ≤ (l.drop i).length := by simp [List.length_drop]; omega
    rw [List.take_append_of_le_length hj_le]
    exact take_drop_sum l i j hi hij
  · push_neg at hij
    simp only [show ¬(i + j ≤ l.length) from by omega, ↓reduceIte]
    have hj_gt : (l.drop i).length ≤ j := by simp [List.length_drop]; omega
    rw [List.take_append, List.take_of_length_le hj_gt, List.sum_append, sum_drop_eq]
    have hlen_eq : j - (l.drop i).length = i + j - l.length := by
      simp [List.length_drop]; omega
    rw [hlen_eq]
    have htake_take : ((l.take i).take (i + j - l.length)).sum =
        (l.take (i + j - l.length)).sum := by
      congr 1; rw [List.take_take]; congr 1; exact Nat.min_eq_left (by omega)
    rw [htake_take]; omega

theorem prefixSum_doubled_periodic (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) (i + l.length) = prefixSum (l ++ l) i + l.sum := by
  simp only [prefixSum]
  rw [show i + l.length = l.length + i from by omega]
  rw [List.take_add, List.sum_append]
  congr 1
  · exact List.take_left
  · simp

theorem prefixSum_doubled_le (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) i = prefixSum l i := by
  simp only [prefixSum]; rw [List.take_append_of_le_length hi]

/- ## Good Rotations -/

def isGoodRotation (l : List ℤ) (i : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ l.length → 0 < ((cyclicRotation l i).take j).sum

instance (l : List ℤ) (i : ℕ) : Decidable (isGoodRotation l i) := by
  unfold isGoodRotation
  apply decidable_of_iff (∀ j ∈ Finset.Icc 1 l.length,
    0 < ((cyclicRotation l i).take j).sum)
  constructor
  · intro h j hj hjn; exact h j (Finset.mem_Icc.mpr ⟨hj, hjn⟩)
  · intro h j hj; rw [Finset.mem_Icc] at hj; exact h j hj.1 hj.2

def goodRotations (l : List ℤ) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isGoodRotation l i)

theorem isGoodRotation_iff_prefixSum (l : List ℤ) (i : ℕ) (hi : i < l.length) :
    isGoodRotation l i ↔
      ∀ j, 0 < j → j ≤ l.length →
        prefixSum l i < prefixSum (l ++ l) (i + j) := by
  unfold isGoodRotation
  constructor
  · intro h j hj hjn
    have hgood := h j hj hjn
    rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn] at hgood
    simp only [prefixSum]
    split_ifs at hgood with hij
    · rw [List.take_append_of_le_length (by omega)]; omega
    · push_neg at hij
      rw [show i + j = l.length + (i + j - l.length) from by omega,
          List.take_add, List.sum_append]
      rw [List.take_left]; simp; omega
  · intro h j hj hjn
    rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn]
    have hpf := h j hj hjn
    simp only [prefixSum] at hpf
    split_ifs with hij
    · rw [List.take_append_of_le_length (by omega)] at hpf; omega
    · push_neg at hij
      rw [show i + j = l.length + (i + j - l.length) from by omega,
          List.take_add, List.sum_append] at hpf
      rw [List.take_left] at hpf; simp at hpf; omega

/- ## Minimum Prefix Sum Infrastructure -/

noncomputable def minPrefixSum (l : List ℤ) : ℤ :=
  ((Finset.range (l.length + 1)).image (prefixSum l)).min'
    (Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ _)

theorem minPrefixSum_le_zero (l : List ℤ) : minPrefixSum l ≤ 0 := by
  unfold minPrefixSum; apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), prefixSum_zero l⟩

theorem minPrefixSum_le (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    minPrefixSum l ≤ prefixSum l i := by
  unfold minPrefixSum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)

/- ## Rightmost Minimum -/

private theorem rightmostMinPos_filter_nonempty (l : List ℤ) :
    ((Finset.range (l.length + 1)).filter (fun i => prefixSum l i = minPrefixSum l)).Nonempty := by
  unfold minPrefixSum
  have hmin := Finset.min'_mem
    ((Finset.range (l.length + 1)).image (prefixSum l))
    (Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ (prefixSum l))
  rw [Finset.mem_image] at hmin
  obtain ⟨a, ha_mem, ha_eq⟩ := hmin
  exact ⟨a, Finset.mem_filter.mpr ⟨ha_mem, ha_eq⟩⟩

noncomputable def rightmostMinPos (l : List ℤ) : ℕ :=
  ((Finset.range (l.length + 1)).filter (fun i => prefixSum l i = minPrefixSum l)).max'
    (rightmostMinPos_filter_nonempty l)

theorem rightmostMinPos_le (l : List ℤ) : rightmostMinPos l ≤ l.length := by
  unfold rightmostMinPos
  have hm := Finset.max'_mem _ (rightmostMinPos_filter_nonempty l)
  rw [Finset.mem_filter, Finset.mem_range] at hm; omega

theorem prefixSum_rightmostMinPos (l : List ℤ) :
    prefixSum l (rightmostMinPos l) = minPrefixSum l := by
  unfold rightmostMinPos
  have hm := Finset.max'_mem _ (rightmostMinPos_filter_nonempty l)
  exact (Finset.mem_filter.mp hm).2

theorem prefixSum_gt_after_rightmostMin (l : List ℤ) (j : ℕ)
    (hj : rightmostMinPos l < j) (hjn : j ≤ l.length) :
    minPrefixSum l < prefixSum l j := by
  by_contra h; push_neg at h
  have heq : prefixSum l j = minPrefixSum l := le_antisymm h (minPrefixSum_le l j hjn)
  have hj_in : j ∈ (Finset.range (l.length + 1)).filter
      (fun i => prefixSum l i = minPrefixSum l) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq⟩
  have hle : j ≤ rightmostMinPos l := by
    unfold rightmostMinPos; exact Finset.le_max' _ j hj_in
  omega

theorem rightmostMinPos_lt (l : List ℤ) (hS : 0 < l.sum) :
    rightmostMinPos l < l.length := by
  by_contra h; push_neg at h
  have heq : rightmostMinPos l = l.length := le_antisymm (rightmostMinPos_le l) h
  have : minPrefixSum l = l.sum := by
    rw [← prefixSum_length l, ← heq]; exact (prefixSum_rightmostMinPos l).symm
  linarith [minPrefixSum_le_zero l]

/- ## Good Rotation at Rightmost Minimum -/

theorem goodRotation_at_rightmostMin (l : List ℤ) (_hn : 0 < l.length) (hS : 0 < l.sum) :
    isGoodRotation l (rightmostMinPos l) := by
  set m := rightmostMinPos l
  have hm_lt : m < l.length := rightmostMinPos_lt l hS
  have hm_val : prefixSum l m = minPrefixSum l := prefixSum_rightmostMinPos l
  intro j hj hjn
  rw [cyclicRotation_prefixSum l m j (le_of_lt hm_lt) hjn]
  split_ifs with hmj
  · have h1 := prefixSum_gt_after_rightmostMin l (m + j) (by omega) hmj
    simp only [prefixSum] at h1 hm_val ⊢; omega
  · push_neg at hmj
    have h1 := minPrefixSum_le l (m + j - l.length) (by omega)
    simp only [prefixSum] at h1 hm_val ⊢; omega

theorem goodRotations_nonempty (l : List ℤ) (hn : 0 < l.length) (hS : 0 < l.sum) :
    (goodRotations l).Nonempty :=
  ⟨rightmostMinPos l, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (rightmostMinPos_lt l hS),
     goodRotation_at_rightmostMin l hn hS⟩⟩

/- ## Prefix Sum Monotonicity and Injectivity -/

theorem goodRotation_prefixSum_strictMono (l : List ℤ) (i₁ i₂ : ℕ)
    (hi₁ : i₁ < l.length) (hi₂ : i₂ < l.length) (hlt : i₁ < i₂)
    (hg₁ : isGoodRotation l i₁) :
    prefixSum l i₁ < prefixSum l i₂ := by
  have h := (isGoodRotation_iff_prefixSum l i₁ hi₁).mp hg₁ (i₂ - i₁) (by omega) (by omega)
  rwa [show i₁ + (i₂ - i₁) = i₂ from by omega, prefixSum_doubled_le l i₂ (le_of_lt hi₂)] at h

theorem goodRotation_prefixSum_injective (l : List ℤ) (i₁ i₂ : ℕ)
    (hi₁ : i₁ < l.length) (hi₂ : i₂ < l.length)
    (hg₁ : isGoodRotation l i₁) (hg₂ : isGoodRotation l i₂)
    (heq : prefixSum l i₁ = prefixSum l i₂) : i₁ = i₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · exact absurd heq (ne_of_lt (goodRotation_prefixSum_strictMono l i₁ i₂ hi₁ hi₂ hlt hg₁))
  · rfl
  · exact absurd heq.symm (ne_of_lt (goodRotation_prefixSum_strictMono l i₂ i₁ hi₂ hi₁ hgt hg₂))

/- ## Good Rotation Bounds -/

theorem goodRotation_ge_rightmostMinPos (l : List ℤ) (i : ℕ)
    (hi : i < l.length) (hS : 0 < l.sum) (hg : isGoodRotation l i) :
    rightmostMinPos l ≤ i := by
  by_contra h; push_neg at h
  have hm_lt : rightmostMinPos l < l.length := rightmostMinPos_lt l hS
  have hm_good := goodRotation_at_rightmostMin l (by omega) hS
  have hsm := goodRotation_prefixSum_strictMono l i (rightmostMinPos l) hi hm_lt h hg
  rw [prefixSum_rightmostMinPos] at hsm
  linarith [minPrefixSum_le l i (le_of_lt hi)]

theorem goodRotation_prefixSum_ge_min (l : List ℤ) (i : ℕ) (hi : i < l.length) :
    minPrefixSum l ≤ prefixSum l i :=
  minPrefixSum_le l i (le_of_lt hi)

theorem goodRotation_prefixSum_lt_sum (l : List ℤ) (i : ℕ)
    (hi : i < l.length) (hS : 0 < l.sum) (hg : isGoodRotation l i) :
    prefixSum l i < minPrefixSum l + l.sum := by
  set m := rightmostMinPos l
  have hm_le := goodRotation_ge_rightmostMinPos l i hi hS hg
  have hm_lt : m < l.length := rightmostMinPos_lt l hS
  rw [isGoodRotation_iff_prefixSum l i hi] at hg
  have hstep := hg (l.length - i + m) (by omega) (by omega)
  have hi_step : i + (l.length - i + m) = l.length + m := by omega
  rw [hi_step] at hstep
  rw [show l.length + m = m + l.length from by omega] at hstep
  rw [prefixSum_doubled_periodic l m (le_of_lt hm_lt)] at hstep
  rw [prefixSum_doubled_le l m (le_of_lt hm_lt)] at hstep
  rw [prefixSum_rightmostMinPos] at hstep
  exact hstep

/- ## Upper Bound: at most sum good rotations -/

theorem goodRotations_card_le {l : List ℤ} (hS : 0 < l.sum) :
    (goodRotations l).card ≤ l.sum.toNat := by
  set f := fun i => (prefixSum l i - minPrefixSum l).toNat
  have hinj : Set.InjOn f ↑(goodRotations l) := by
    intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_coe, goodRotations, Finset.mem_filter] at hi₁ hi₂
    have h1_lt := Finset.mem_range.mp hi₁.1
    have h2_lt := Finset.mem_range.mp hi₂.1
    have _hge1 := goodRotation_prefixSum_ge_min l i₁ h1_lt
    have _hge2 := goodRotation_prefixSum_ge_min l i₂ h2_lt
    have : prefixSum l i₁ = prefixSum l i₂ := by simp only [f] at heq; omega
    exact goodRotation_prefixSum_injective l i₁ i₂ h1_lt h2_lt hi₁.2 hi₂.2 this
  have hsub : (goodRotations l).image f ⊆ Finset.range l.sum.toNat := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [goodRotations, Finset.mem_filter] at hi
    have hi_lt := Finset.mem_range.mp hi.1
    have _hge := goodRotation_prefixSum_ge_min l i hi_lt
    have _hlt := goodRotation_prefixSum_lt_sum l i hi_lt hS hi.2
    simp only [f, Finset.mem_range]; omega
  calc (goodRotations l).card
      = ((goodRotations l).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range l.sum.toNat).card := Finset.card_le_card hsub
    _ = l.sum.toNat := Finset.card_range _

/- ## Lower Bound Infrastructure -/

private theorem prefixSum_step (l : List ℤ) (i : ℕ) (hi : i < l.length) :
    prefixSum l (i + 1) = prefixSum l i + l[i] := by
  simp only [prefixSum]
  have : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_succ_eq_append_getElem (h := hi)]
  rw [this, List.sum_append, List.sum_singleton]

/-- Discrete intermediate value theorem for ballot prefix sums.
    Since the only way to increase is by +1, prefix sums hit every integer level. -/
theorem level_achieved_ge_min {k : ℕ} {l : List ℤ}
    (hsteps : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ)
    (_hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum) :
    ∃ i, i < l.length ∧ prefixSum l i = v := by
  have hPn : v < prefixSum l l.length := by
    rw [prefixSum_length]; linarith [minPrefixSum_le_zero l]
  let K := (Finset.range (l.length + 1)).filter (fun j => prefixSum l j ≤ v)
  have hK_ne : K.Nonempty := by
    have hmin := Finset.min'_mem
      ((Finset.range (l.length + 1)).image (prefixSum l))
      (Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ (prefixSum l))
    rw [Finset.mem_image] at hmin
    obtain ⟨j, hj_mem, hj_eq⟩ := hmin
    exact ⟨j, Finset.mem_filter.mpr ⟨hj_mem, by
      have : prefixSum l j = minPrefixSum l := by unfold minPrefixSum; exact hj_eq
      linarith⟩⟩
  set q := K.max' hK_ne
  have hq_mem := Finset.max'_mem K hK_ne
  rw [Finset.mem_filter, Finset.mem_range] at hq_mem
  have hq_le : prefixSum l q ≤ v := hq_mem.2
  have hq_lt_n : q < l.length := by
    by_contra hc; push_neg at hc
    have : q = l.length := by omega
    rw [this] at hq_le; linarith
  have hq1_gt : v < prefixSum l (q + 1) := by
    by_contra h2; push_neg at h2
    have hmem : q + 1 ∈ K :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩
    have := Finset.le_max' K (q + 1) hmem; omega
  have hstep := prefixSum_step l q hq_lt_n
  have hmem_l : l[q] ∈ l := List.getElem_mem (by exact hq_lt_n)
  rcases hsteps _ hmem_l with h1 | hk
  · rw [h1] at hstep; exact ⟨q, hq_lt_n, by omega⟩
  · rw [hk] at hstep; omega

/-- The rightmost position achieving level v is a good rotation. -/
theorem rightmostAtLevel_good (l : List ℤ) (v : ℤ)
    (_hS : 0 < l.sum) (_hlo : minPrefixSum l ≤ v) (_hhi : v < minPrefixSum l + l.sum)
    (i : ℕ) (hi_lt : i < l.length) (hi_eq : prefixSum l i = v)
    (hi_right : ∀ j, i < j → j ≤ l.length → v < prefixSum l j) :
    isGoodRotation l i := by
  intro j hj hjn
  rw [cyclicRotation_prefixSum l i j (le_of_lt hi_lt) hjn]
  split_ifs with hmj
  · have := hi_right (i + j) (by omega) hmj
    simp only [prefixSum] at this hi_eq ⊢; omega
  · push_neg at hmj
    have h1 := minPrefixSum_le l (i + j - l.length) (by omega)
    simp only [prefixSum] at h1 hi_eq ⊢; omega

theorem positions_at_level_nonempty {k : ℕ} {l : List ℤ}
    (hsteps : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ) (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum) :
    ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty := by
  obtain ⟨i, hi_lt, hi_eq⟩ := level_achieved_ge_min hsteps v hlo hhi
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_lt, hi_eq⟩⟩

noncomputable def rightmostAtLevel (l : List ℤ) (v : ℤ)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty) : ℕ :=
  ((Finset.range l.length).filter (fun i => prefixSum l i = v)).max' hne

theorem rightmostAtLevel_lt (l : List ℤ) (v : ℤ)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty) :
    rightmostAtLevel l v hne < l.length := by
  have hm := Finset.max'_mem _ hne
  rw [Finset.mem_filter, Finset.mem_range] at hm; exact hm.1

theorem prefixSum_rightmostAtLevel (l : List ℤ) (v : ℤ)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty) :
    prefixSum l (rightmostAtLevel l v hne) = v := by
  have hm := Finset.max'_mem _ hne
  exact (Finset.mem_filter.mp hm).2

theorem rightmostAtLevel_strict_above {k : ℕ} (l : List ℤ)
    (hsteps : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ) (_hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty)
    (j : ℕ) (hj_gt : rightmostAtLevel l v hne < j) (hj_le : j ≤ l.length) :
    v < prefixSum l j := by
  by_contra h; push_neg at h
  have hPn : v < prefixSum l l.length := by
    rw [prefixSum_length]; linarith [minPrefixSum_le_zero l]
  let K := (Finset.Icc j l.length).filter (fun q => prefixSum l q ≤ v)
  have hK_ne : K.Nonempty :=
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, hj_le⟩, h⟩⟩
  set q := K.max' hK_ne
  have hq_mem := Finset.max'_mem K hK_ne
  rw [Finset.mem_filter, Finset.mem_Icc] at hq_mem
  have hq_le_v : prefixSum l q ≤ v := hq_mem.2
  have hq_lt_n : q < l.length := by
    by_contra hc; push_neg at hc
    have : q = l.length := by omega
    rw [this] at hq_le_v; linarith
  have hq1_gt : v < prefixSum l (q + 1) := by
    by_contra h2; push_neg at h2
    have hmem : q + 1 ∈ K :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h2⟩
    have := Finset.le_max' K (q + 1) hmem; omega
  have hstep := prefixSum_step l q hq_lt_n
  have hmem_l : l[q] ∈ l := List.getElem_mem (by exact hq_lt_n)
  rcases hsteps _ hmem_l with h1 | hk
  · rw [h1] at hstep
    have hpv : prefixSum l q = v := by omega
    have hmem_f : q ∈ (Finset.range l.length).filter (fun i => prefixSum l i = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq_lt_n, hpv⟩
    have := Finset.le_max' _ q hmem_f
    unfold rightmostAtLevel at hj_gt; omega
  · rw [hk] at hstep; omega

theorem rightmostAtLevel_isGoodRotation {k : ℕ} (l : List ℤ)
    (hsteps : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (hS : 0 < l.sum)
    (v : ℤ) (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty) :
    isGoodRotation l (rightmostAtLevel l v hne) := by
  exact rightmostAtLevel_good l v hS hlo hhi
    (rightmostAtLevel l v hne) (rightmostAtLevel_lt l v hne)
    (prefixSum_rightmostAtLevel l v hne)
    (fun j hj hjn => rightmostAtLevel_strict_above l hsteps v hlo hhi hne j hj hjn)

theorem rightmostAtLevel_mem_goodRotations {k : ℕ} (l : List ℤ)
    (hsteps : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (hS : 0 < l.sum)
    (v : ℤ) (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum)
    (hne : ((Finset.range l.length).filter (fun i => prefixSum l i = v)).Nonempty) :
    rightmostAtLevel l v hne ∈ goodRotations l :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (rightmostAtLevel_lt l v hne),
     rightmostAtLevel_isGoodRotation l hsteps hS v hlo hhi hne⟩

/- ## Lower Bound: at least sum good rotations -/

set_option maxHeartbeats 400000 in
theorem goodRotations_card_ge {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    (a - k * b : ℕ) ≤ (goodRotations l).card := by
  have hsteps := hl.2.2
  have hS : 0 < l.sum := kCountedSequence_pos_sum hl hab
  have _hsum : l.sum = (a : ℤ) - k * b := kCountedSequence_sum hl
  set S := (a - k * b : ℕ)
  have hlo_m : ∀ (m : Fin S), minPrefixSum l ≤ minPrefixSum l + ↑(m : ℕ) := by
    intro m; omega
  have hhi_m : ∀ (m : Fin S), minPrefixSum l + ↑(m : ℕ) < minPrefixSum l + l.sum := by
    intro m; have := m.isLt; omega
  have hne_m : ∀ (m : Fin S),
      ((Finset.range l.length).filter (fun i => prefixSum l i = minPrefixSum l + ↑(m : ℕ))).Nonempty :=
    fun m => positions_at_level_nonempty hsteps _ (hlo_m m) (hhi_m m)
  let f : Fin S → ℕ := fun m => rightmostAtLevel l (minPrefixSum l + ↑(m : ℕ)) (hne_m m)
  suffices h : (∀ m, f m ∈ goodRotations l) ∧ Function.Injective f by
    obtain ⟨hf_mem, hf_inj⟩ := h
    let g : Fin S → goodRotations l := fun m => ⟨f m, hf_mem m⟩
    have hg_inj : Function.Injective g := by
      intro m₁ m₂ h; exact hf_inj (Subtype.mk.inj h)
    calc S = Fintype.card (Fin S) := (Fintype.card_fin S).symm
      _ ≤ Fintype.card (goodRotations l) := Fintype.card_le_of_injective g hg_inj
      _ = (goodRotations l).card := by rw [Fintype.card_coe]
  constructor
  · intro m
    exact rightmostAtLevel_mem_goodRotations l hsteps hS _ (hlo_m m) (hhi_m m) _
  · intro m₁ m₂ heq
    have h1 := prefixSum_rightmostAtLevel l (minPrefixSum l + ↑(m₁ : ℕ)) (hne_m m₁)
    have h2 := prefixSum_rightmostAtLevel l (minPrefixSum l + ↑(m₂ : ℕ)) (hne_m m₂)
    show m₁ = m₂
    change f m₁ = f m₂ at heq
    rw [show f m₁ = rightmostAtLevel l _ (hne_m m₁) from rfl] at heq
    rw [show f m₂ = rightmostAtLevel l _ (hne_m m₂) from rfl] at heq
    rw [heq] at h1; rw [h1] at h2
    ext; omega

/- ## The Cycle Lemma -/

/-- **The Cycle Lemma (Dvoretzky-Motzkin, 1947) for ballot sequences.**
    Among the n = a + b cyclic rotations of a ballot sequence with a copies of +1
    and b copies of -k (where a > kb), exactly a - kb are "good" rotations
    (all prefix sums positive). -/
theorem cycle_lemma {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b)
    (hab : k * b < a) :
    (goodRotations l).card = a - k * b := by
  apply le_antisymm
  · have hS : 0 < l.sum := kCountedSequence_pos_sum hl hab
    have hle := goodRotations_card_le hS
    have hsum : l.sum = (a : ℤ) - k * b := kCountedSequence_sum hl
    omega
  · exact goodRotations_card_ge hl hab

/- ## Verification Examples -/

example : (goodRotations [1, 1, -1]).card = 1 := by native_decide
example : (goodRotations [1, 1, 1, -1, -1]).card = 1 := by native_decide
example : (goodRotations [1, 1, 1, -1]).card = 2 := by native_decide

end BallotCycleLemma
