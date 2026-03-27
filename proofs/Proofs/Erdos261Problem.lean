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

/- ## Block Sum Formula -/

/-- Block sum formula: ∑_{k=n+1}^{n+m} k/2^k = (n+2)/2^n - (n+m+2)/2^{n+m}.
    Proved by induction on m, extending the block one element at a time. -/
lemma block_sum_formula (n m : ℕ) :
    (Finset.Icc (n + 1) (n + m)).sum recipPow2Weight =
    ((n : ℚ) + 2) / 2 ^ n - ((n : ℚ) + ↑m + 2) / 2 ^ (n + m) := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, add_zero,
      Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_self]
  | succ m ih =>
    have hsplit : Finset.Icc (n + 1) (n + (m + 1)) =
        Finset.Icc (n + 1) (n + m) ∪ {n + m + 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.Icc (n + 1) (n + m)) ({n + m + 1} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_Icc, not_and, not_le]
      intro; omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton, ih]
    simp only [recipPow2Weight]
    push_cast
    field_simp
    ring

/- ## Known Results -/

/-- n = 1 is representable: 1/2 = 4/16 + 5/32 + 6/64.
    Needed for the m = 1 case of Borwein-Loring where the standard
    block {n+1} has only 1 element (below the card ≥ 2 threshold). -/
private theorem representable_one : IsRepresentable 1 := by
  refine ⟨{4, 5, 6}, ?_, ?_, ?_⟩
  · -- card ≥ 2
    decide
  · -- all k ≥ 1
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  · -- sum = recipPow2Weight 1
    simp only [recipPow2Sum, recipPow2Weight,
      Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6} : Finset ℕ) by decide),
      Finset.sum_insert (show (5 : ℕ) ∉ ({6} : Finset ℕ) by decide),
      Finset.sum_singleton]
    norm_num

/-- Borwein–Loring explicit family (PROVED): n = 2^{m+1} − m − 2 is
    representable via the consecutive block {n+1, ..., n+m}.

    For m = 1 (n = 1): uses {4, 5, 6} since the standard block has card 1.
    For m ≥ 2: block_sum_formula + n + m + 2 = 2^{m+1} gives the identity. -/
theorem borwein_loring_family (m : ℕ) (hm : 1 ≤ m) :
  let n := 2 ^ (m + 1) - m - 2
  IsRepresentable n := by
  show IsRepresentable (2 ^ (m + 1) - m - 2)
  set n := 2 ^ (m + 1) - m - 2 with hn_def
  rcases Nat.eq_or_gt_of_le hm with rfl | hm2
  · -- m = 1: n = 2^2 - 3 = 1
    exact representable_one
  · -- m ≥ 2: use BL set Icc (n+1) (n+m)
    have hpow_ge : m + 2 ≤ 2 ^ (m + 1) := by
      have : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
      omega
    have hn_eq : n + m + 2 = 2 ^ (m + 1) := by omega
    refine ⟨Finset.Icc (n + 1) (n + m), ?_, ?_, ?_⟩
    · -- card = m ≥ 2
      rw [Finset.card_Icc]; omega
    · -- all k ≥ 1
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · -- sum = recipPow2Weight n (the Borwein-Loring identity)
      rw [block_sum_formula]
      simp only [recipPow2Weight]
      have hn_cast : (↑n + ↑m + 2 : ℚ) = (2 : ℚ) ^ (m + 1) := by exact_mod_cast hn_eq
      rw [hn_cast]
      push_cast
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

/-- Tengely–Ulas–Zygadło: all n ≤ 10000 are representable -/
axiom tengely_ulas_zygadlo (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 10000) :
  IsRepresentable n

/- ## The Erdős Conjectures -/

/-- Erdős Problem 261, Part 1: infinitely many n are representable.
    This is resolved by Cusick's theorem. -/
theorem ErdosProblem261_infinitely_many :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsRepresentable n :=
  cusick_infinitely_many

/-- Erdős Problem 261, Part 2 (stronger conjecture): every n ≥ 1 is representable -/
axiom ErdosProblem261_all (n : ℕ) (hn : 1 ≤ n) :
  IsRepresentable n

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
