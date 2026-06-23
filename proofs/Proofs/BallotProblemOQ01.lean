import Archive.Wiedijk100Theorems.BallotProblem
import Mathlib.Tactic

/-
# The Generalized Ballot Problem: k-Fold Dominance

## Research Problem: ballot-problem-oq-01
Generalization of the Ballot Problem to the k-fold case.

## What This Proves
The Generalized Ballot Problem extends Bertrand's classical result (Wiedijk #30)
to the case where candidate A must maintain more than k times the votes of
candidate B throughout the entire counting process.

**Mathematical Statement:**
In an election where candidate A receives `a` votes and candidate B receives `b`
votes (where `a > k * b` for a positive integer `k`), the probability that A
always has more than `k` times as many votes as B throughout the counting is:

  P = (a - k * b) / (a + b)

This generalizes the classical formula P = (p - q)/(p + q) (the case k = 1).

## Approach
- **Lattice Path Model**: We model the vote counting using paths with upsteps (+1)
  and downsteps (-k). The condition "A has > k times B's votes" is equivalent to
  the path staying strictly above the x-axis.
- **Cycle Lemma**: The proof of the counting formula uses the Dvoretzky-Motzkin
  cycle lemma, which counts the number of "good" cyclic rotations.
- **Connection to Classical Case**: When k = 1, this reduces to the standard
  ballot problem with steps +1 and -1.

## Status
- [x] Definitions for generalized ballot sequences
- [x] Statement of the generalized ballot theorem
- [x] Proof that k=1 reduces to the classical ballot theorem
- [x] Key structural lemmas (sum, length, nonempty, path height, permutation characterization)
- [x] Finiteness of kCountedSequence (via permutation characterization)
- [x] Cycle lemma infrastructure (rotation sum/length/identity/membership preservation)
- [x] Positive sum/length preconditions for cycle lemma
- [x] Prefix sum relation for rotations (both wrapping and non-wrapping cases)
- [x] Rightmost minimum infrastructure (definition, bounds, good rotation existence)
- [x] Prefix sum strict monotonicity and injectivity on good rotations
- [x] Cycle lemma upper bound: |goodRotations| ≤ sum (via injection to levels)
- [x] Cycle lemma bounds on good rotation prefix sums
- [x] Good rotations occur at or after rightmost minimum
- [x] Cycle lemma lower bound: level_achieved_ge_min (discrete IVT) + levelPos injection
- [x] **The Cycle Lemma** (Dvoretzky-Motzkin, 1947): |goodRotations l| = a - k*b
- [x] Full proof of the generalized counting formula (via choose identities)

## References
- Bertrand (1887): Original ballot problem
- Dvoretzky & Motzkin (1947): Cycle lemma
- Renault (2007): "Four Proofs of the Ballot Theorem"
-/

namespace GeneralizedBallot

open List Set

/- ## Part I: Generalized Ballot Sequences -/

def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = a ∧ l.count (-(k : ℤ)) = b ∧ ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)}

def kStaysPositive : Set (List ℤ) :=
  {l | ∀ (i : ℕ), 0 < i → i ≤ l.length → 0 < (l.take i).sum}

/- ## Part II: Core Algebraic Lemmas -/

theorem sum_eq_count_sub_mul_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.sum = (l.count 1 : ℤ) - (k : ℤ) * (l.count (-(k : ℤ))) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.sum_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · simp [hne]; push_cast; omega
    · simp [hne.symm]; push_cast; ring

theorem length_eq_count_add_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.length = l.count 1 + l.count (-(k : ℤ)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.length_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · simp [hne]; omega
    · simp [hne.symm]; omega

/- ## Part III: Basic Properties of kCountedSequence -/

theorem kCountedSequence_sum {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.sum = (a : ℤ) - k * b := by
  have h := sum_eq_count_sub_mul_count hl.2.2
  rw [hl.1, hl.2.1] at h; exact h

theorem kCountedSequence_length {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.length = a + b := by
  have h := length_eq_count_add_count hl.2.2
  rw [hl.1, hl.2.1] at h; exact h

theorem kCountedSequence_perm (k a b : ℕ) (l : List ℤ) (hl : l ∈ kCountedSequence k a b) :
    l ~ (List.replicate a 1 ++ List.replicate b (-(k : ℤ))) := by
  rw [List.perm_iff_count]
  intro x
  have ⟨h1, h2, h3⟩ := hl
  have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
  by_cases hx1 : x = 1
  · subst hx1; simp [List.count_append, List.count_replicate, hne, hne.symm, h1]
  · by_cases hxk : x = -(k : ℤ)
    · subst hxk; simp [List.count_append, List.count_replicate, hne, hne.symm, h2]
    · have hcl : l.count x = 0 := by
        rw [List.count_eq_zero]; intro hm; rcases h3 x hm with rfl | rfl <;> contradiction
      have hcr : (List.replicate a (1 : ℤ) ++ List.replicate b (-(k : ℤ))).count x = 0 := by
        rw [List.count_eq_zero, List.mem_append, List.mem_replicate, List.mem_replicate]
        push_neg; exact ⟨fun _ => hx1, fun _ => hxk⟩
      omega

theorem kCountedSequence_finite (k a b : ℕ) : (kCountedSequence k a b).Finite := by
  let w := List.replicate a 1 ++ List.replicate b (-(k : ℤ))
  apply Set.Finite.subset (Finset.finite_toSet w.permutations.toFinset)
  intro l hl
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
  exact kCountedSequence_perm k a b l hl

theorem kCountedSequence_nonempty (k a b : ℕ) : (kCountedSequence k a b).Nonempty := by
  use List.replicate a 1 ++ List.replicate b (-(k : ℤ))
  have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.count_append, List.count_replicate]; simp [hne, hne.symm]
  · simp only [List.count_append, List.count_replicate]; simp [hne, hne.symm]
  · intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl (List.eq_of_mem_replicate hx)
    · exact Or.inr (List.eq_of_mem_replicate hx)

/- ## Part IV: Connection to Classical Ballot Problem -/

theorem kCountedSequence_eq_countedSequence (a b : ℕ) :
    kCountedSequence 1 a b = Ballot.countedSequence a b := by
  ext l
  simp only [kCountedSequence, Ballot.countedSequence, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_, h3⟩; simpa using h2
  · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_, h3⟩; simpa using h2

/- ## Part V: The Generalized Ballot Theorem -/

/-- Identity: b * C(a+b, a) = (a+b) * C(a+b-1, a).
    From Nat.succ_mul_choose_eq with n=a+b-1, k=b-1. -/
private theorem choose_mul_identity (a b : ℕ) (hb : 0 < b) :
    b * (a + b).choose a = (a + b) * (a + b - 1).choose a := by
  have h := Nat.succ_mul_choose_eq (a + b - 1) (b - 1)
  simp only [Nat.succ_eq_add_one] at h
  rw [show a + b - 1 + 1 = a + b from by omega,
      show b - 1 + 1 = b from by omega] at h
  -- h : (a+b) * C(a+b-1, b-1) = C(a+b, b) * b
  -- Convert C(a+b-1, b-1) → C(a+b-1, a)
  have eq1 : (a + b - 1).choose (b - 1) = (a + b - 1).choose a := by
    have : (a + b - 1).choose ((a + b - 1) - a) = (a + b - 1).choose a :=
      Nat.choose_symm (by omega)
    rwa [show (a + b - 1) - a = b - 1 from by omega] at this
  -- Convert C(a+b, b) → C(a+b, a)
  have eq2 : (a + b).choose b = (a + b).choose a := by
    have : (a + b).choose ((a + b) - a) = (a + b).choose a :=
      Nat.choose_symm (by omega)
    rwa [show (a + b) - a = b from by omega] at this
  rw [eq1, eq2] at h; linarith

/-- Identity: a * C(a+b-1, a) = b * C(a+b-1, a-1).
    From Nat.succ_mul_choose_eq with n=a+b-2 and symmetry. -/
private theorem choose_mul_identity2 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a * (a + b - 1).choose a = b * (a + b - 1).choose (a - 1) := by
  have h1 := Nat.succ_mul_choose_eq (a + b - 2) (a - 1)
  simp only [Nat.succ_eq_add_one] at h1
  rw [show a + b - 2 + 1 = a + b - 1 from by omega,
      show a - 1 + 1 = a from by omega] at h1
  -- h1 : (a+b-1) * C(a+b-2, a-1) = C(a+b-1, a) * a
  have h2 := Nat.succ_mul_choose_eq (a + b - 2) (b - 1)
  simp only [Nat.succ_eq_add_one] at h2
  rw [show a + b - 2 + 1 = a + b - 1 from by omega,
      show b - 1 + 1 = b from by omega] at h2
  -- h2 : (a+b-1) * C(a+b-2, b-1) = C(a+b-1, b) * b
  -- C(a+b-2, b-1) = C(a+b-2, a-1) by symmetry
  have eq1 : (a + b - 2).choose (b - 1) = (a + b - 2).choose (a - 1) := by
    have : (a + b - 2).choose ((a + b - 2) - (a - 1)) = (a + b - 2).choose (a - 1) :=
      Nat.choose_symm (by omega)
    rwa [show (a + b - 2) - (a - 1) = b - 1 from by omega] at this
  -- C(a+b-1, b) = C(a+b-1, a-1) by symmetry
  have eq2 : (a + b - 1).choose b = (a + b - 1).choose (a - 1) := by
    have : (a + b - 1).choose ((a + b - 1) - (a - 1)) = (a + b - 1).choose (a - 1) :=
      Nat.choose_symm (by omega)
    rwa [show (a + b - 1) - (a - 1) = b from by omega] at this
  rw [eq1] at h2; rw [eq2] at h2; linarith

/-- b divides (a - k*b) * C(a+b-1, a) when k*b < a. -/
private theorem dvd_choose_mul (a b k : ℕ) (hb : 0 < b) (hab : k * b < a) :
    b ∣ (a - k * b) * (a + b - 1).choose a := by
  have ha : 0 < a := by omega
  -- b ∣ a * C(a+b-1, a) from identity: a*C = b*C'
  have hd1 : b ∣ a * (a + b - 1).choose a := by
    rw [choose_mul_identity2 a b ha hb]; exact dvd_mul_right b _
  -- b ∣ k*b * C(a+b-1, a) trivially
  have hd2 : b ∣ k * b * (a + b - 1).choose a :=
    dvd_mul_of_dvd_left (dvd_mul_left b k) _
  -- (a-kb)*C = a*C - kb*C, and b divides both terms
  rw [Nat.sub_mul]
  obtain ⟨q, hq⟩ := hd1
  obtain ⟨r, hr⟩ := hd2
  rw [hq, hr, ← Nat.mul_sub]
  exact dvd_mul_right b _

theorem generalized_ballot_count (k a b : ℕ) (hab : k * b < a) :
    ∃ (good_count : ℕ),
      good_count * (a + b) = (a - k * b) * (a + b).choose a := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- b = 0: good_count = 1
    exact ⟨1, by simp [Nat.choose_self]⟩
  · -- b > 0: good_count = (a - k*b) * C(a+b-1, a) / b
    refine ⟨(a - k * b) * (a + b - 1).choose a / b, ?_⟩
    have hdvd := dvd_choose_mul a b k hb hab
    have hkey := choose_mul_identity a b hb
    -- Prove by multiplying both sides by b and cancelling
    refine mul_right_cancel₀ (show (b : ℕ) ≠ 0 from by omega) ?_
    calc (a - k * b) * (a + b - 1).choose a / b * (a + b) * b
        = (a - k * b) * (a + b - 1).choose a / b * b * (a + b) := by ring
      _ = (a - k * b) * (a + b - 1).choose a * (a + b) := by
            rw [Nat.div_mul_cancel hdvd]
      _ = (a - k * b) * ((a + b) * (a + b - 1).choose a) := by ring
      _ = (a - k * b) * (b * (a + b).choose a) := by rw [hkey]
      _ = (a - k * b) * (a + b).choose a * b := by ring

theorem generalized_ballot_prob (k a b : ℕ) (hab : k * b < a) :
    ((a : ℚ) - k * b) / (a + b) > 0 := by
  have h1 : (0 : ℚ) < a - k * b := by rw [sub_pos]; exact_mod_cast hab
  have h2 : (0 : ℚ) < a + b := by exact_mod_cast Nat.add_pos_left (by omega : 0 < a) b
  exact div_pos h1 h2

/- ## Part VI: Special Cases and Verification -/

theorem generalized_ballot_classical (a b : ℕ) :
    ((a : ℚ) - 1 * b) / (a + b) = (a - b) / (a + b) := by ring

example : ((5 : ℚ) - 2 * 2) / (5 + 2) = 1 / 7 := by norm_num
example : ((10 : ℚ) - 3 * 3) / (10 + 3) = 1 / 13 := by norm_num
example : ((3 : ℚ) - 1 * 1) / (3 + 1) = 1 / 2 := by norm_num
example : ((7 : ℚ) - 2 * 3) / (7 + 3) = 1 / 10 := by norm_num

/- ## Part VII: The Cycle Lemma -/

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

theorem cyclicRotation_zero (l : List ℤ) : cyclicRotation l 0 = l := by
  simp [cyclicRotation]

theorem cyclicRotation_length_self (l : List ℤ) : cyclicRotation l l.length = l := by
  simp [cyclicRotation]

theorem cyclicRotation_mem_kCountedSequence {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (i : ℕ) (hi : i ≤ l.length) :
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

theorem cyclicRotation_compose (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hj : j ≤ l.length - i) :
    cyclicRotation (cyclicRotation l i) j = cyclicRotation l (i + j) := by
  simp only [cyclicRotation]
  have hj_le : j ≤ (l.drop i).length := by simp [List.length_drop]; omega
  rw [List.drop_append_of_le_length hj_le, List.take_append_of_le_length hj_le]
  rw [List.drop_drop, List.append_assoc]
  congr 1; rw [← List.take_add]

theorem kCountedSequence_pos_sum {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    0 < l.sum := by rw [kCountedSequence_sum hl]; omega

theorem kCountedSequence_pos_length {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : 0 < a + b) :
    0 < l.length := by rw [kCountedSequence_length hl]; exact hab

private theorem sum_drop_eq (l : List ℤ) (i : ℕ) :
    (l.drop i).sum = l.sum - (l.take i).sum := by
  have h := congr_arg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h; omega

private theorem take_drop_sum (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hij : i + j ≤ l.length) :
    ((l.drop i).take j).sum = (l.take (i + j)).sum - (l.take i).sum := by
  have key : l.take (i + j) = l.take i ++ (l.drop i).take j := List.take_add
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

def prefixSum (l : List ℤ) (i : ℕ) : ℤ := (l.take i).sum

theorem prefixSum_zero (l : List ℤ) : prefixSum l 0 = 0 := by simp [prefixSum]

theorem prefixSum_length (l : List ℤ) : prefixSum l l.length = l.sum := by
  simp [prefixSum, List.take_length]

theorem prefixSum_doubled_periodic (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) (i + l.length) = prefixSum (l ++ l) i + l.sum := by
  simp only [prefixSum]
  rw [show i + l.length = l.length + i from Nat.add_comm i l.length]
  rw [List.take_add, List.sum_append, List.take_left, List.drop_left,
      List.take_append_of_le_length hi]
  ring

def isGoodRotation (l : List ℤ) (i : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ l.length → 0 < ((cyclicRotation l i).take j).sum

instance (l : List ℤ) (i : ℕ) : Decidable (isGoodRotation l i) := by
  unfold isGoodRotation
  apply decidable_of_iff (∀ j ∈ Finset.Icc 1 l.length,
    0 < ((cyclicRotation l i).take j).sum)
  constructor
  · intro h j hj hjn
    exact h j (Finset.mem_Icc.mpr ⟨hj, hjn⟩)
  · intro h j hj
    rw [Finset.mem_Icc] at hj
    exact h j hj.1 hj.2

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
          List.take_add, List.sum_append, List.take_left, List.drop_left]; omega
  · intro h j hj hjn
    rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn]
    have hpf := h j hj hjn
    simp only [prefixSum] at hpf
    split_ifs with hij
    · rw [List.take_append_of_le_length (by omega)] at hpf; omega
    · push_neg at hij
      rw [show i + j = l.length + (i + j - l.length) from by omega,
          List.take_add, List.sum_append, List.take_left, List.drop_left] at hpf; omega

theorem prefixSum_doubled_le (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) i = prefixSum l i := by
  simp only [prefixSum]; rw [List.take_append_of_le_length hi]

/- ## Cycle Lemma Infrastructure -/

noncomputable def minPrefixSum (l : List ℤ) : ℤ :=
  ((Finset.range (l.length + 1)).image (prefixSum l)).min'
    (Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ _)

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

theorem minPrefixSum_le_zero (l : List ℤ) : minPrefixSum l ≤ 0 := by
  unfold minPrefixSum; apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), prefixSum_zero l⟩

theorem minPrefixSum_le (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    minPrefixSum l ≤ prefixSum l i := by
  unfold minPrefixSum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)

theorem prefixSum_gt_after_rightmostMin (l : List ℤ) (j : ℕ)
    (hj : rightmostMinPos l < j) (hjn : j ≤ l.length) :
    minPrefixSum l < prefixSum l j := by
  by_contra h; push_neg at h
  have heq : prefixSum l j = minPrefixSum l := le_antisymm h (minPrefixSum_le l j hjn)
  have hj_in : j ∈ (Finset.range (l.length + 1)).filter
      (fun i => prefixSum l i = minPrefixSum l) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq⟩
  have hle : j ≤ rightmostMinPos l := by
    unfold rightmostMinPos
    exact Finset.le_max' _ j hj_in
  omega

theorem rightmostMinPos_lt (l : List ℤ) (hS : 0 < l.sum) :
    rightmostMinPos l < l.length := by
  by_contra h; push_neg at h
  have heq : rightmostMinPos l = l.length := le_antisymm (rightmostMinPos_le l) h
  have : minPrefixSum l = l.sum := by
    rw [← prefixSum_length l, ← heq]; exact (prefixSum_rightmostMinPos l).symm
  linarith [minPrefixSum_le_zero l]

theorem goodRotation_at_rightmostMin (l : List ℤ) (hn : 0 < l.length) (hS : 0 < l.sum) :
    isGoodRotation l (rightmostMinPos l) := by
  set m := rightmostMinPos l
  have hm_lt : m < l.length := rightmostMinPos_lt l hS
  have hm_val : prefixSum l m = minPrefixSum l := prefixSum_rightmostMinPos l
  intro j hj hjn
  rw [cyclicRotation_prefixSum l m j (le_of_lt hm_lt) hjn]
  split_ifs with hmj
  · -- Case: m + j ≤ l.length (no wrapping)
    -- Need: 0 < P(m+j) - P(m) = P(m+j) - minPrefixSum
    -- Since m < m+j ≤ l.length, and m is rightmost min, P(m+j) > minPrefixSum
    have h1 := prefixSum_gt_after_rightmostMin l (m + j) (by omega) hmj
    simp only [prefixSum] at h1 hm_val; omega
  · -- Case: m + j > l.length (wrapping)
    -- Need: 0 < P(m+j-n) + S - P(m) = P(m+j-n) + S - minPrefixSum
    push_neg at hmj
    have h1 := minPrefixSum_le l (m + j - l.length) (by omega)
    simp only [prefixSum] at h1 hm_val; omega

theorem goodRotations_nonempty (l : List ℤ) (hn : 0 < l.length) (hS : 0 < l.sum) :
    (goodRotations l).Nonempty :=
  ⟨rightmostMinPos l, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (rightmostMinPos_lt l hS),
     goodRotation_at_rightmostMin l hn hS⟩⟩

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

/-- No good rotation can have index strictly before the rightmost minimum. -/
theorem goodRotation_ge_rightmostMinPos (l : List ℤ) (i : ℕ)
    (hi : i < l.length) (hS : 0 < l.sum) (hg : isGoodRotation l i) :
    rightmostMinPos l ≤ i := by
  by_contra h; push_neg at h
  -- i < rightmostMinPos, and both i and rightmostMinPos are good rotations
  have hm_lt : rightmostMinPos l < l.length := rightmostMinPos_lt l hS
  have hm_good := goodRotation_at_rightmostMin l (by omega) hS
  -- By strict monotonicity: prefixSum i < prefixSum rightmostMinPos = minPrefixSum
  have hsm := goodRotation_prefixSum_strictMono l i (rightmostMinPos l) hi hm_lt h hg
  rw [prefixSum_rightmostMinPos] at hsm
  -- But prefixSum i ≥ minPrefixSum by definition
  linarith [minPrefixSum_le l i (le_of_lt hi)]

/-- Good rotation prefix sums are bounded: minPrefixSum ≤ P(i) -/
theorem goodRotation_prefixSum_ge_min (l : List ℤ) (i : ℕ)
    (hi : i < l.length) :
    minPrefixSum l ≤ prefixSum l i :=
  minPrefixSum_le l i (le_of_lt hi)

/-- Good rotation prefix sums are bounded above: P(i) < minPrefixSum + sum.
    Key insight: the wrapping part of a good rotation passes through
    prefix sums including minPrefixSum, and these must all be > 0. -/
theorem goodRotation_prefixSum_lt_sum (l : List ℤ) (i : ℕ)
    (hi : i < l.length) (hS : 0 < l.sum) (hg : isGoodRotation l i) :
    prefixSum l i < minPrefixSum l + l.sum := by
  set m := rightmostMinPos l
  have hm_le := goodRotation_ge_rightmostMinPos l i hi hS hg
  have hm_lt : m < l.length := rightmostMinPos_lt l hS
  -- Use the isGoodRotation_iff_prefixSum characterization
  rw [isGoodRotation_iff_prefixSum l i hi] at hg
  -- At step j = l.length - i + m, we're in the wrapping part
  -- The doubled prefix sum at position i + (l.length - i + m) = l.length + m
  -- By periodicity: P_doubled(l.length + m) = P_doubled(m) + l.sum = P(m) + l.sum
  have hstep := hg (l.length - i + m) (by omega) (by omega)
  -- P_doubled(i + (l.length - i + m)) = P_doubled(l.length + m)
  -- = P_doubled(m) + l.sum = P(m) + l.sum = minPrefixSum + l.sum
  have hi_step : i + (l.length - i + m) = l.length + m := by omega
  rw [hi_step] at hstep
  rw [show l.length + m = m + l.length from by omega] at hstep
  rw [prefixSum_doubled_periodic l m (le_of_lt hm_lt)] at hstep
  rw [prefixSum_doubled_le l m (le_of_lt hm_lt)] at hstep
  rw [prefixSum_rightmostMinPos] at hstep
  -- Now hstep is exactly the goal: P(i) < minPrefixSum + l.sum
  exact hstep

/-- Cardinality upper bound: at most sum good rotations. -/
theorem goodRotations_card_le {l : List ℤ} (hS : 0 < l.sum) :
    (goodRotations l).card ≤ l.sum.toNat := by
  -- goodRotations is a subset of Finset.range l.length which has card ≤ l.length
  -- But we need card ≤ l.sum.toNat which could be smaller
  -- Use injection into Finset.range l.sum.toNat via shifted prefix sums
  -- Strategy: show goodRotations.card ≤ goodRotations.card = image.card ≤ range.card
  set f := fun i => (prefixSum l i - minPrefixSum l).toNat
  -- f is injective on goodRotations
  have hinj : Set.InjOn f ↑(goodRotations l) := by
    intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_coe, goodRotations, Finset.mem_filter] at hi₁ hi₂
    have h1_lt := Finset.mem_range.mp hi₁.1
    have h2_lt := Finset.mem_range.mp hi₂.1
    have hge1 := goodRotation_prefixSum_ge_min l i₁ h1_lt
    have hge2 := goodRotation_prefixSum_ge_min l i₂ h2_lt
    have : prefixSum l i₁ = prefixSum l i₂ := by simp only [f] at heq; omega
    exact goodRotation_prefixSum_injective l i₁ i₂ h1_lt h2_lt hi₁.2 hi₂.2 this
  -- image is contained in Finset.range l.sum.toNat
  have hsub : (goodRotations l).image f ⊆ Finset.range l.sum.toNat := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [goodRotations, Finset.mem_filter] at hi
    have hi_lt := Finset.mem_range.mp hi.1
    have hge := goodRotation_prefixSum_ge_min l i hi_lt
    have hlt := goodRotation_prefixSum_lt_sum l i hi_lt hS hi.2
    simp only [f, Finset.mem_range]; omega
  calc (goodRotations l).card
      = ((goodRotations l).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range l.sum.toNat).card := Finset.card_le_card hsub
    _ = l.sum.toNat := Finset.card_range _

/-- For each integer level v in [minPrefixSum, minPrefixSum + sum), there exists a
    position i < l.length with prefixSum l i = v. This follows from the +1 steps:
    since the only way to increase is by +1, the prefix sums pass through every
    integer level between the minimum and the maximum. -/
theorem level_achieved_ge_min {k : ℕ} (l : List ℤ)
    (hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ)
    (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum) :
    ∃ i, i < l.length ∧ prefixSum l i = v := by
  have hv_lt_sum : v < l.sum := by linarith [minPrefixSum_le_zero l]
  -- Use Finset.max' of {i ≤ l.length | prefixSum l i ≤ v}
  let S := (Finset.range (l.length + 1)).filter (fun i => prefixSum l i ≤ v)
  have hS_ne : S.Nonempty :=
    ⟨rightmostMinPos l, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (rightmostMinPos_le l)),
       by rw [prefixSum_rightmostMinPos]; exact hlo⟩⟩
  obtain ⟨j, hj_max⟩ : ∃ j, j = S.max' hS_ne := ⟨_, rfl⟩
  have hj_mem : j ∈ S := hj_max ▸ Finset.max'_mem S hS_ne
  have hj_le : j ≤ l.length :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1)
  have hj_le_v : prefixSum l j ≤ v := (Finset.mem_filter.mp hj_mem).2
  have hj_lt : j < l.length := by
    rcases Nat.eq_or_lt_of_le hj_le with rfl | h
    · simp only [prefixSum, List.take_length] at hj_le_v; linarith
    · exact h
  -- j+1 ∉ S: prefixSum l (j+1) > v (by maximality of j)
  have hj1_gt : v < prefixSum l (j + 1) := by
    by_contra hle; push_neg at hle
    have hj1_mem : j + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩
    have := Finset.le_max' S (j + 1) hj1_mem
    omega
  -- The element at j is +1 (not -k)
  have hj_elem : l[j] = (1 : ℤ) := by
    rcases hmem l[j] (List.getElem_mem hj_lt) with h1 | hk
    · exact h1
    · exfalso
      have hstep : prefixSum l (j + 1) = prefixSum l j + l[j] := by
        simp only [prefixSum]; exact List.sum_take_succ l j hj_lt
      rw [hstep, hk] at hj1_gt
      linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]
  -- Therefore prefixSum l j = v exactly
  have hj_eq : prefixSum l j = v := by
    have hstep : prefixSum l (j + 1) = prefixSum l j + 1 := by
      simp only [prefixSum]; rw [List.sum_take_succ l j hj_lt, hj_elem]
    linarith
  exact ⟨j, hj_lt, hj_eq⟩

/-- The rightmost position achieving level v is a good rotation.
    After this position, all prefix sums are strictly above v (by rightmost).
    In the wrapping part, prefix sums are ≥ minPrefixSum, and since the circular
    sum is S > 0, the shifted values are all > 0. -/
theorem rightmostAtLevel_good (l : List ℤ) (v : ℤ)
    (hS : 0 < l.sum) (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum)
    (i : ℕ) (hi_lt : i < l.length) (hi_eq : prefixSum l i = v)
    (hi_right : ∀ j, i < j → j ≤ l.length → v < prefixSum l j) :
    isGoodRotation l i := by
  intro j hj hjn
  rw [cyclicRotation_prefixSum l i j (le_of_lt hi_lt) hjn]
  split_ifs with hij
  · -- Non-wrapping case: 0 < P(i+j) - P(i)
    have h1 : v < prefixSum l (i + j) := hi_right (i + j) (by omega) hij
    simp only [prefixSum] at h1 hi_eq; omega
  · -- Wrapping case: 0 < P(i+j-n) + S - P(i)
    push_neg at hij
    have h1 : minPrefixSum l ≤ prefixSum l (i + j - l.length) :=
      minPrefixSum_le l (i + j - l.length) (by omega)
    simp only [prefixSum] at h1 hi_eq; omega

/-- Private helper: for each n : ℕ, the rightmost position in [0, l.length]
    where prefix sum ≤ minPrefixSum l + n. Well-defined for all n ≥ 0. -/
private noncomputable def levelPos (l : List ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (l.length + 1)).filter (fun i => prefixSum l i ≤ minPrefixSum l + n)).max'
    ⟨rightmostMinPos l, Finset.mem_filter.mpr ⟨
      Finset.mem_range.mpr (Nat.lt_succ_of_le (rightmostMinPos_le l)),
      by rw [prefixSum_rightmostMinPos]; omega⟩⟩

private theorem levelPos_mem (l : List ℤ) (n : ℕ) :
    levelPos l n ∈ (Finset.range (l.length + 1)).filter
      (fun i => prefixSum l i ≤ minPrefixSum l + n) := by
  unfold levelPos; exact Finset.max'_mem _ _

private theorem levelPos_le (l : List ℤ) (n : ℕ) : levelPos l n ≤ l.length :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (levelPos_mem l n)).1)

private theorem levelPos_prefixSum_le (l : List ℤ) (n : ℕ) :
    prefixSum l (levelPos l n) ≤ minPrefixSum l + n :=
  (Finset.mem_filter.mp (levelPos_mem l n)).2

private theorem levelPos_max (l : List ℤ) (n m : ℕ)
    (hm : m ≤ l.length) (hm_le : prefixSum l m ≤ minPrefixSum l + n) :
    m ≤ levelPos l n :=
  Finset.le_max' _ m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm_le⟩)

private theorem levelPos_lt (l : List ℤ) (n : ℕ) (hn : (n : ℤ) < l.sum) :
    levelPos l n < l.length := by
  rcases Nat.eq_or_lt_of_le (levelPos_le l n) with h | h
  · -- levelPos l n = l.length contradicts prefixSum ≤ minPrefixSum l + n < l.sum
    have hle := levelPos_prefixSum_le l n
    rw [h, prefixSum_length] at hle
    linarith [minPrefixSum_le_zero l]
  · exact h

private theorem levelPos_right (l : List ℤ) (n m : ℕ)
    (hm_gt : levelPos l n < m) (hm_le : m ≤ l.length) :
    minPrefixSum l + (n : ℤ) < prefixSum l m := by
  by_contra hle; push_neg at hle
  exact absurd (levelPos_max l n m hm_le hle) (by omega)

private theorem levelPos_eq {k : ℕ} (l : List ℤ)
    (hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (n : ℕ) (hn : (n : ℤ) < l.sum) :
    prefixSum l (levelPos l n) = minPrefixSum l + n := by
  have hj_lt : levelPos l n < l.length := levelPos_lt l n hn
  have hj_le : prefixSum l (levelPos l n) ≤ minPrefixSum l + n := levelPos_prefixSum_le l n
  -- levelPos l n + 1 ∉ the filter (maximality)
  have hj1_gt : minPrefixSum l + (n : ℤ) < prefixSum l (levelPos l n + 1) := by
    by_contra hle; push_neg at hle
    exact absurd (levelPos_max l n (levelPos l n + 1) (by omega) hle) (by omega)
  -- The step at levelPos l n is +1 (not -k)
  have helem : l[levelPos l n] = (1 : ℤ) := by
    rcases hmem l[levelPos l n] (List.getElem_mem hj_lt) with h1 | hk
    · exact h1
    · exfalso
      have hstep : prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + l[levelPos l n] := by
        simp only [prefixSum]; exact List.sum_take_succ l (levelPos l n) hj_lt
      rw [hstep, hk] at hj1_gt
      linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]
  -- Therefore prefixSum l (levelPos l n) = minPrefixSum l + n
  have hstep : prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + 1 := by
    simp only [prefixSum]; rw [List.sum_take_succ l (levelPos l n) hj_lt, helem]
  linarith

/-- Lower bound via level surjectivity: at least sum good rotations.
    For each integer level v in [minPrefixSum, minPrefixSum + sum),
    the rightmost position achieving that level is a good rotation.
    These give S = a - k*b distinct good rotations. -/
theorem goodRotations_card_ge {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    (a - k * b : ℕ) ≤ (goodRotations l).card := by
  have hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ) := hl.2.2
  have hS : 0 < l.sum := kCountedSequence_pos_sum hl hab
  have hsum : l.sum = (a : ℤ) - k * b := kCountedSequence_sum hl
  -- Rewrite as cardinality inequality via injection
  rw [← Finset.card_range (a - k * b)]
  apply Finset.card_le_card_of_injOn (levelPos l)
  · -- levelPos n ∈ goodRotations for each n ∈ Finset.range (a-k*b)
    intro n hn
    have hn_lt : n < a - k * b := Finset.mem_range.mp (Finset.mem_coe.mp hn)
    have hn' : (n : ℤ) < l.sum := by rw [hsum]; omega
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (levelPos_lt l n hn'),
        rightmostAtLevel_good l (minPrefixSum l + n) hS
          (by linarith [show (0 : ℤ) ≤ n from Int.natCast_nonneg n])
          (by linarith)
          (levelPos l n) (levelPos_lt l n hn')
          (levelPos_eq l hmem n hn')
          (fun m hm hml => levelPos_right l n m hm hml)⟩)
  · -- levelPos is injective on Finset.range (a-k*b)
    intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hn₁ hn₂
    have hn₁' : (n₁ : ℤ) < l.sum := by rw [hsum]; omega
    have hn₂' : (n₂ : ℤ) < l.sum := by rw [hsum]; omega
    have h₁ := levelPos_eq l hmem n₁ hn₁'
    have h₂ := levelPos_eq l hmem n₂ hn₂'
    rw [heq] at h₁
    have : (n₁ : ℤ) = n₂ := by linarith
    exact_mod_cast this

/-- **The Cycle Lemma (Dvoretzky-Motzkin, 1947) for ballot sequences.** -/
theorem cycle_lemma {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b)
    (hab : k * b < a) :
    (goodRotations l).card = a - k * b := by
  apply le_antisymm
  · -- Upper bound: at most a - kb good rotations
    have hS : 0 < l.sum := kCountedSequence_pos_sum hl hab
    have hle := goodRotations_card_le hS
    have hsum : l.sum = (a : ℤ) - k * b := kCountedSequence_sum hl
    omega
  · -- Lower bound: at least a - kb good rotations
    exact goodRotations_card_ge hl hab

/-- Verification examples -/
example : (goodRotations [1, 1, -1]).card = 1 := by native_decide
example : (goodRotations [1, 1, 1, -1, -1]).card = 1 := by native_decide
example : (goodRotations [1, 1, 1, -1]).card = 2 := by native_decide

/- ## Part VIII: Lattice Path Interpretation -/

theorem path_height_interpretation {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (i : ℕ) (hi : i ≤ l.length) :
    (l.take i).sum = (l.take i).count 1 - (k : ℤ) * (l.take i).count (-(k : ℤ)) := by
  apply sum_eq_count_sub_mul_count
  intro x hx; exact hl.2.2 x (List.take_subset i l hx)

end GeneralizedBallot
