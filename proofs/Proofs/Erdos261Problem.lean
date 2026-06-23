/-
# Erdős Problem #261 — Reciprocal Power-of-Two Representations

Erdős asked whether every positive integer n can be represented as

  n / 2^n = ∑_{k ∈ S} k / 2^k

for some finite set S of distinct positive integers with |S| ≥ 2.

More precisely:
(1) Are there infinitely many such n? (Yes — proved by Cusick)
(2) Does this hold for all n? (Verified for n ≤ 10000 by Tengely–Ulas–Zygadło)
(3) Does some rational x = ∑ aₖ/2^{aₖ} admit continuum-many representations?

Borwein and Loring showed that for every m ≥ 1, setting n = 2^{m+1} − m − 2 gives
  n / 2^n = ∑_{k=n+1}^{n+m} k / 2^k.

Reference: https://erdosproblems.com/261
-/

import Mathlib

/- ## Core Definitions -/

/-- The "weight" function: k / 2^k as a rational number -/
noncomputable def recipPow2Weight (k : ℕ) : ℚ :=
  (k : ℚ) / (2 ^ k : ℚ)

/-- Sum of k/2^k over a finite set of distinct positive integers -/
noncomputable def recipPow2Sum (S : Finset ℕ) : ℚ :=
  S.sum recipPow2Weight

/-- A valid representation of n/2^n as a sum of distinct k/2^k values -/
def IsRecipPow2Rep (n : ℕ) (S : Finset ℕ) : Prop :=
  2 ≤ S.card ∧
  (∀ k ∈ S, 1 ≤ k) ∧
  recipPow2Sum S = recipPow2Weight n

/-- n is representable if there exists a valid decomposition -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, IsRecipPow2Rep n S

/- ## Basic Properties -/

/-- The weight function is positive for positive k -/
theorem recipPow2Weight_pos (k : ℕ) (hk : 1 ≤ k) : 0 < recipPow2Weight k := by
  unfold recipPow2Weight
  apply div_pos
  · exact_mod_cast show 0 < k by omega
  · positivity

/-- The weight at k = 1 is 1/2 -/
theorem recipPow2Weight_one : recipPow2Weight 1 = 1 / 2 := by
  unfold recipPow2Weight; norm_num

/-- The weight at k = 2 is also 1/2 (2/4 = 1/2) -/
theorem recipPow2Weight_two : recipPow2Weight 2 = 1 / 2 := by
  unfold recipPow2Weight; norm_num

/-- recipPow2Weight 1 = recipPow2Weight 2: a coincidence at k=1,2 -/
theorem recipPow2Weight_one_eq_two : recipPow2Weight 1 = recipPow2Weight 2 := by
  rw [recipPow2Weight_one, recipPow2Weight_two]

/-- Empty set has zero sum -/
theorem recipPow2Sum_empty : recipPow2Sum ∅ = 0 := by
  unfold recipPow2Sum; simp

/-- Singleton sum equals the weight -/
theorem recipPow2Sum_singleton (k : ℕ) : recipPow2Sum {k} = recipPow2Weight k := by
  unfold recipPow2Sum; simp

/-- The weight at k = 0 is 0 -/
theorem recipPow2Weight_zero : recipPow2Weight 0 = 0 := by
  unfold recipPow2Weight; simp

/-- The weight at k = 3 is 3/8 -/
theorem recipPow2Weight_three : recipPow2Weight 3 = 3 / 8 := by
  unfold recipPow2Weight; norm_num

/-- The sum over any set of positive integers is non-negative -/
theorem recipPow2Sum_nonneg (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k) :
    0 ≤ recipPow2Sum S := by
  unfold recipPow2Sum
  apply Finset.sum_nonneg
  intro k hk
  exact le_of_lt (recipPow2Weight_pos k (hS k hk))

/-- Adding an element to a disjoint set adds to the sum -/
theorem recipPow2Sum_insert {S : Finset ℕ} {k : ℕ} (hk : k ∉ S) :
    recipPow2Sum (insert k S) = recipPow2Weight k + recipPow2Sum S := by
  unfold recipPow2Sum
  exact Finset.sum_insert hk

/-- The sum over a two-element set is the sum of the two weights -/
theorem recipPow2Sum_pair {a b : ℕ} (hab : a ≠ b) :
    recipPow2Sum {a, b} = recipPow2Weight a + recipPow2Weight b := by
  unfold recipPow2Sum
  rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]

/-- Monotonicity: adding positive elements increases the sum -/
theorem recipPow2Sum_le_of_subset {S T : Finset ℕ}
    (hST : S ⊆ T) (hT : ∀ k ∈ T, 1 ≤ k) :
    recipPow2Sum S ≤ recipPow2Sum T := by
  unfold recipPow2Sum
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro k _ _
  exact le_of_lt (recipPow2Weight_pos k (hT k (by assumption)))

/- ## Partial Sum Formula -/

/-- Key identity: ∑_{k=1}^{n} k/2^k = 2 - (n+2)/2^n.
    Proved by induction on n. -/
theorem partial_sum_formula (n : ℕ) :
    (Finset.range n).sum (fun k => recipPow2Weight (k + 1)) =
    2 - ((n : ℚ) + 2) / 2 ^ n := by
  induction n with
  | zero => simp [recipPow2Weight]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold recipPow2Weight
    rw [pow_succ]
    push_cast
    field_simp
    ring

/- ## Known Results -/

/-- n = 1 is representable: 1/2 = 4/16 + 5/32 + 6/64. -/
theorem representable_one : IsRepresentable 1 := by
  refine ⟨{4, 5, 6}, ?_, ?_, ?_⟩
  · -- card ≥ 2
    simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · -- all ≥ 1
    intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  · -- sum = 1/2 (= recipPow2Weight 1)
    show recipPow2Sum {4, 5, 6} = recipPow2Weight 1
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6} : Finset ℕ) by decide),
                Finset.sum_insert (show (5 : ℕ) ∉ ({6} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- Representability transfers via equal weight: if w(n) = w(m) and m is
    representable, then n is representable using the same witness set. -/
theorem representable_of_eq_weight {n m : ℕ}
    (hw : recipPow2Weight n = recipPow2Weight m)
    (hm : IsRepresentable m) : IsRepresentable n := by
  obtain ⟨S, hcard, hpos, hsum⟩ := hm
  exact ⟨S, hcard, hpos, hsum.trans hw.symm⟩

/-- n = 2 is representable: w(2) = w(1) = 1/2, so the same witness works. -/
theorem representable_two : IsRepresentable 2 :=
  representable_of_eq_weight recipPow2Weight_one_eq_two.symm representable_one

/-- n = 3 is representable: 3/8 = 4/16 + 6/64 + 8/256. -/
theorem representable_three : IsRepresentable 3 := by
  refine ⟨{4, 6, 8}, ?_, ?_, ?_⟩
  · -- card ≥ 2
    simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · -- all ≥ 1
    intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  · -- sum = recipPow2Weight 3
    show recipPow2Sum {4, 6, 8} = recipPow2Weight 3
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (4 : ℕ) ∉ ({6, 8} : Finset ℕ) by decide),
                Finset.sum_insert (show (6 : ℕ) ∉ ({8} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- Sum over consecutive block {a+1, ..., a+m} as a telescoping difference.
    ∑_{k=a+1}^{a+m} k/2^k = (a+2)/2^a - (a+m+2)/2^(a+m). -/
private lemma icc_recipPow2_sum (a m : ℕ) :
    (Finset.Icc (a + 1) (a + m)).sum recipPow2Weight =
    ((a : ℚ) + 2) / 2 ^ a - ((a : ℚ) + m + 2) / 2 ^ (a + m) := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, add_zero]
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ m ih =>
    have h_ins : Finset.Icc (a + 1) (a + (m + 1)) =
        insert (a + m + 1) (Finset.Icc (a + 1) (a + m)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h_ins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
    simp only [recipPow2Weight]
    push_cast
    rw [show (2 : ℚ) ^ (a + (m + 1)) = 2 ^ (a + m) * 2 from by ring]
    rw [show (2 : ℚ) ^ (a + m) = 2 ^ a * 2 ^ m from by ring]
    field_simp
    ring

/-- Borwein–Loring explicit family: n = 2^{m+1} − m − 2 is representable
    via the consecutive block {n+1, ..., n+m} for m ≥ 2.
    For m = 1 (n = 1), uses representable_one.
    Proof: telescoping via partial_sum_formula gives
    ∑_{k=n+1}^{n+m} = (n+2)/2^n - (n+m+2)/2^{n+m} = n/2^n
    using the key identity n + m + 2 = 2^{m+1}. -/
theorem borwein_loring_family (m : ℕ) (hm : 1 ≤ m) :
    let n := 2 ^ (m + 1) - m - 2
    IsRepresentable n := by
  obtain rfl | hm2 := hm.eq_or_gt
  · -- m = 1: n = 2^2 - 3 = 1
    exact representable_one
  · -- m ≥ 2: use consecutive block {n+1, ..., n+m}
    intro n
    have hpow : m + 2 ≤ 2 ^ (m + 1) := by
      have := Nat.lt_two_pow_self (n := m + 1); omega
    have hn_sum : n + m + 2 = 2 ^ (m + 1) := by simp only [n]; omega
    refine ⟨Finset.Icc (n + 1) (n + m), ?_, ?_, ?_⟩
    · -- card ≥ 2
      rw [show Finset.Icc (n + 1) (n + m) = Finset.Ico (n + 1) (n + m + 1) from
        (Finset.Ico_succ_right).symm, Finset.card_Ico]
      omega
    · -- all elements ≥ 1
      intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · -- recipPow2Sum S = recipPow2Weight n
      unfold recipPow2Sum
      rw [icc_recipPow2_sum n m]
      unfold recipPow2Weight
      have h_eq : ((n : ℚ) + ↑m + 2) = (2 : ℚ) ^ (m + 1) := by exact_mod_cast hn_sum
      rw [h_eq, show (2 : ℚ) ^ (n + m) = 2 ^ n * 2 ^ m from by ring,
          show (2 : ℚ) ^ (m + 1) = 2 ^ m * 2 from by ring]
      field_simp
      ring

/-- For m ≥ 1, the Borwein-Loring value n = 2^{m+1} - m - 2 satisfies n ≥ m.
    Follows from 2(m+1) ≤ 2^{m+1} (exponential dominates linear). -/
private lemma borwein_loring_value_ge (m : ℕ) (_ : 1 ≤ m) :
    m ≤ 2 ^ (m + 1) - m - 2 := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 * (m + 1) ≤ 2 ^ (m + 1) := by
    have : 2 * 2 ^ m = 2 ^ (m + 1) := by ring
    omega
  omega

/-- Cusick's result: infinitely many n are representable.
    Proved from Borwein-Loring: for any N, take m = max(N,1),
    then n = 2^{m+1} - m - 2 ≥ m ≥ N. -/
theorem cusick_infinitely_many :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsRepresentable n := by
  intro N
  set m := max N 1
  have hm : 1 ≤ m := le_max_right N 1
  refine ⟨2 ^ (m + 1) - m - 2, ?_, borwein_loring_family m hm⟩
  calc N ≤ m := le_max_left N 1
    _ ≤ 2 ^ (m + 1) - m - 2 := borwein_loring_value_ge m hm

/-- n = 4 is representable, from the Borwein-Loring family with m = 2:
    4 = 2³ - 2 - 2, and 4/16 = 5/32 + 6/64. -/
theorem representable_four : IsRepresentable 4 :=
  borwein_loring_family 2 (by omega)

/-- n = 5 is representable: 5/32 = 6/64 + 7/128 + 11/2048 + 13/8192 + 14/16384. -/
theorem representable_five : IsRepresentable 5 := by
  refine ⟨{6, 7, 11, 13, 14}, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  · show recipPow2Sum {6, 7, 11, 13, 14} = recipPow2Weight 5
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (6 : ℕ) ∉ ({7, 11, 13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (7 : ℕ) ∉ ({11, 13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (11 : ℕ) ∉ ({13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (13 : ℕ) ∉ ({14} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- n = 6 is representable: 6/64 = 7/128 + 8/256 + 11/2048 + 13/8192 + 14/16384. -/
theorem representable_six : IsRepresentable 6 := by
  refine ⟨{7, 8, 11, 13, 14}, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  · show recipPow2Sum {7, 8, 11, 13, 14} = recipPow2Weight 6
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (7 : ℕ) ∉ ({8, 11, 13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (8 : ℕ) ∉ ({11, 13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (11 : ℕ) ∉ ({13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (13 : ℕ) ∉ ({14} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- n = 7 is representable: 7/128 = 8/256 + 9/512 + 11/2048 + 15/32768
    + 20/1048576 + 21/2097152 + 24/16777216. -/
theorem representable_seven : IsRepresentable 7 := by
  refine ⟨{8, 9, 11, 15, 20, 21, 24}, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · show recipPow2Sum {8, 9, 11, 15, 20, 21, 24} = recipPow2Weight 7
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (8 : ℕ) ∉ ({9, 11, 15, 20, 21, 24} : Finset ℕ) by decide),
                Finset.sum_insert (show (9 : ℕ) ∉ ({11, 15, 20, 21, 24} : Finset ℕ) by decide),
                Finset.sum_insert (show (11 : ℕ) ∉ ({15, 20, 21, 24} : Finset ℕ) by decide),
                Finset.sum_insert (show (15 : ℕ) ∉ ({20, 21, 24} : Finset ℕ) by decide),
                Finset.sum_insert (show (20 : ℕ) ∉ ({21, 24} : Finset ℕ) by decide),
                Finset.sum_insert (show (21 : ℕ) ∉ ({24} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- All n from 1 to 7 are representable. -/
theorem representable_le_7 (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 7) : IsRepresentable n := by
  interval_cases n
  · exact representable_one
  · exact representable_two
  · exact representable_three
  · exact representable_four
  · exact representable_five
  · exact representable_six
  · exact representable_seven

/-- n = 9 is representable: 9/512 = 10/1024 + 11/2048 + 13/8192 + 14/16384. -/
theorem representable_nine : IsRepresentable 9 := by
  refine ⟨{10, 11, 13, 14}, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_not_mem, Finset.card_singleton]; omega
  · intro k hk; simp [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  · show recipPow2Sum {10, 11, 13, 14} = recipPow2Weight 9
    simp only [recipPow2Sum, recipPow2Weight]
    simp only [Finset.sum_insert (show (10 : ℕ) ∉ ({11, 13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (11 : ℕ) ∉ ({13, 14} : Finset ℕ) by decide),
                Finset.sum_insert (show (13 : ℕ) ∉ ({14} : Finset ℕ) by decide),
                Finset.sum_singleton]
    norm_num

/-- n = 11 is representable, from the Borwein-Loring family with m = 3:
    11 = 2⁴ - 3 - 2, and 11/2¹¹ = ∑_{k=12}^{14} k/2^k. -/
theorem representable_eleven : IsRepresentable 11 :=
  borwein_loring_family 3 (by omega)

/-- n = 26 is representable, from the Borwein-Loring family with m = 4:
    26 = 2⁵ - 4 - 2, and 26/2²⁶ = ∑_{k=27}^{30} k/2^k. -/
theorem representable_26 : IsRepresentable 26 :=
  borwein_loring_family 4 (by omega)

/-- n = 57 is representable, from the Borwein-Loring family with m = 5:
    57 = 2⁶ - 5 - 2, and 57/2⁵⁷ = ∑_{k=58}^{62} k/2^k. -/
theorem representable_57 : IsRepresentable 57 :=
  borwein_loring_family 5 (by omega)

/-- n = 120 is representable, from the Borwein-Loring family with m = 6:
    120 = 2⁷ - 6 - 2, and 120/2¹²⁰ = ∑_{k=121}^{126} k/2^k. -/
theorem representable_120 : IsRepresentable 120 :=
  borwein_loring_family 6 (by omega)

/-- Tengely–Ulas–Zygadło: all n ≤ 10000 are representable -/
/- ## The Erdős Conjectures -/

/-- Erdős Problem 261, Part 1: infinitely many n are representable.
    This is resolved by Cusick's theorem. -/
theorem ErdosProblem261_infinitely_many :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsRepresentable n :=
  cusick_infinitely_many

/-- Erdős Problem 261, Part 2 (stronger conjecture): every n ≥ 1 is representable -/
/- ## Continuum Representations -/

/-- An infinite representation: a sequence a : ℕ → ℕ of distinct positive integers.
    NOTE: This definition is INCOMPLETE — it does not include the convergence
    condition ∑ a(k)/2^{a(k)} = x. The x parameter is currently unused.
    A complete formalization would require Filter.Tendsto or tsum from Mathlib's
    topology library to express convergence of the series.
    As a result, the theorems below using IsInfiniteRep are trivially satisfiable
    and do not capture the intended mathematical content. -/
def IsInfiniteRep (a : ℕ → ℕ) (x : ℚ) : Prop :=
  (∀ i, 1 ≤ a i) ∧
  (∀ i j, i ≠ j → a i ≠ a j)

/-- Erdős Problem 261, Part 3: there exists a rational x admitting
    uncountably many (≥ 2^ℵ₀) distinct infinite representations.
    NOTE: Trivially satisfiable because IsInfiniteRep lacks convergence.
    The intended statement requires the series ∑ a(k)/2^{a(k)} to converge to x. -/
theorem ErdosProblem261_continuum :
    ∃ x : ℚ, ∃ f : Set.Icc (0 : ℝ) 1 → (ℕ → ℕ),
      ∀ t, IsInfiniteRep (f t) x :=
  ⟨0, fun _ n => n + 1, fun _ => ⟨fun i => by omega, fun i j hij => by omega⟩⟩

/-- Erdős's weakened form: some rational admits at least two distinct representations.
    NOTE: Trivially satisfiable because IsInfiniteRep lacks convergence. -/
theorem ErdosProblem261_two_reps :
    ∃ x : ℚ, ∃ a b : ℕ → ℕ,
      IsInfiniteRep a x ∧ IsInfiniteRep b x ∧ a ≠ b :=
  ⟨0, fun n => 2 * n + 1, fun n => 2 * n + 2,
    ⟨fun i => by omega, fun i j hij => by omega⟩,
    ⟨fun i => by omega, fun i j hij => by omega⟩,
    fun h => by have := congr_fun h 0; omega⟩
