/-
Erdős Problem #1110: Representability by Sums of p^k q^l

Source: https://erdosproblems.com/1110
Status: OPEN (partially resolved)

Statement:
Let p > q ≥ 2 be coprime integers. An integer n is "representable" if it is the
sum of numbers of the form p^k q^l where none of the summands divide each other.

If {p,q} ≠ {2,3}, what can be said about the density of non-representable numbers?
Are there infinitely many coprime non-representable numbers?

Key Results:
1. Erdős-Lewin (1996): Finitely many non-representable numbers iff {p,q} = {2,3}
2. The {2,3} case has a simple inductive proof (Jansen et al.)
3. Yu-Chen (2022): Density zero for non-representable numbers in many cases
4. Yu-Chen: Infinitely many coprime non-representable numbers for most (p,q)

Historical Note:
Erdős wrote in 1992: "last year I made the following silly conjecture" about the
{2,3} case, which turned out to have a simple inductive proof.

References:
- [ErLe96] Erdős-Lewin, "d-complete sequences of integers"
- [YuCh22] Yu-Chen, "On a conjecture of Erdős and Lewin"
- [YaZh25] Yang-Zhao, improved bounds on representation sizes

Tags: number-theory, additive-combinatorics, representations
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

open Finset

namespace Erdos1110

/-
## Part I: Basic Definitions
-/

/--
**Power form p^k q^l:**
A number of the form p^k q^l for some non-negative integers k, l.
-/
def IsPowerForm (p q n : ℕ) : Prop :=
  ∃ k l : ℕ, n = p ^ k * q ^ l

/--
**Non-divisibility condition:**
A collection of natural numbers where no element divides another.
-/
def NoOneDividesAnother (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b)

/--
**Representable number:**
n is representable (for p, q) if it can be written as a sum of terms p^{kᵢ}q^{lᵢ}
where no term divides another.
-/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    S.Nonempty ∧
    (∀ s ∈ S, IsPowerForm p q s) ∧
    NoOneDividesAnother S ∧
    S.sum id = n

/--
**The set of non-representable numbers:**
-/
def NonRepresentable (p q : ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentable p q n}

/-
## Part II: The {2,3} Case (Erdős's "Silly Conjecture")

Proof: By strong induction on n.
- Base: n = 1 = 3^0 · 2^0, use S = {1}.
- Even: n = 2m with m ≥ 1. By IH, m = ∑ S where S is an antichain of 3^a·2^b terms.
  Double each term: 2·S = {2s | s ∈ S}. Still an antichain (2a|2b ⟹ a|b), still power forms
  (2·3^a·2^b = 3^a·2^(b+1)), sum = 2·∑S = 2m = n.
- Odd: n ≥ 3 odd. Let k = ⌊log₃ n⌋, so 3^k ≤ n < 3^(k+1).
  If n = 3^k: use S = {3^k}.
  If n > 3^k: n - 3^k is positive and even (odd - odd). Write n - 3^k = 2m.
  By IH, m has representation S'. Double to get 2·S'. Add 3^k:
  - No element of 2·S' divides 3^k: elements are even (factor of 2), 3^k is odd.
  - 3^k doesn't divide any element of 2·S': any element 3^a·2^(b+1) divisible by 3^k
    requires a ≥ k, giving 3^a·2^(b+1) ≥ 2·3^k > n - 3^k ≥ element. Contradiction.
-/

/-- Doubling preserves the power form: if s = 3^a·2^b, then 2s = 3^a·2^(b+1). -/
lemma isPowerForm_mul_two {s : ℕ} (h : IsPowerForm 3 2 s) : IsPowerForm 3 2 (s * 2) := by
  obtain ⟨k, l, rfl⟩ := h
  exact ⟨k, l + 1, by ring⟩

/-- Doubling preserves the antichain property. -/
lemma noOneDividesAnother_image_mul_two {S : Finset ℕ} (hS : NoOneDividesAnother S)
    (hpos : ∀ s ∈ S, 0 < s) :
    NoOneDividesAnother (S.image (· * 2)) := by
  intro a ha b hb hab
  rw [Finset.mem_image] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hne : a' ≠ b' := by
    intro heq; subst heq; exact hab rfl
  intro hdvd
  have : a' ∣ b' := by
    rwa [Nat.mul_dvd_mul_iff_right (by norm_num : 0 < 2)] at hdvd
  exact hS a' ha' b' hb' hne this

/-- The sum of the doubled set is twice the original sum. -/
lemma sum_image_mul_two {S : Finset ℕ} (hinj : Set.InjOn (· * 2) (↑S)) :
    (S.image (· * 2)).sum id = 2 * S.sum id := by
  rw [Finset.sum_image (fun a ha b hb => hinj ha hb)]
  simp [Finset.mul_sum, mul_comm]

/-- Multiplication by 2 is injective on S (always true on ℕ). -/
lemma mul_two_injOn (S : Finset ℕ) : Set.InjOn (· * 2) (↑S) := by
  intro a _ b _ h
  omega

/-- 3^k is a power form. -/
lemma isPowerForm_pow_three (k : ℕ) : IsPowerForm 3 2 (3 ^ k) :=
  ⟨k, 0, by simp⟩

/-- An even number cannot divide an odd number. -/
lemma even_not_dvd_odd {a b : ℕ} (ha : 2 ∣ a) (hb : ¬ 2 ∣ b) : ¬ (a ∣ b) := by
  intro hab
  exact hb (dvd_trans ha hab)

/-- 3^k is odd for all k. -/
lemma three_pow_odd (k : ℕ) : ¬ 2 ∣ 3 ^ k := by
  intro h
  have h2d3 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  obtain ⟨c, hc⟩ := h2d3
  omega

/-- Elements of the doubled set are all even. -/
lemma image_mul_two_even {S : Finset ℕ} {x : ℕ} (hx : x ∈ S.image (· * 2)) :
    2 ∣ x := by
  rw [Finset.mem_image] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact dvd_mul_left 2 a

/-- The {2,3} case: all n ≥ 1 are representable as antichain sums of 3^a·2^b.
    Proved by strong induction. -/
theorem case_2_3_all_representable :
    ∀ n : ℕ, n ≥ 1 → IsRepresentable 3 2 n := by
  intro n
  induction n using Nat.strong_rec_on with
  | _ n ih =>
  intro hn
  by_cases hn1 : n = 1
  · -- Base case: n = 1 = 3^0 · 2^0
    subst hn1
    exact ⟨{1}, by simp, fun s hs => by simp at hs; subst hs; exact ⟨0, 0, by simp⟩,
      fun a ha b hb hab => by simp at ha hb; omega, by simp⟩
  · by_cases heven : 2 ∣ n
    · -- Even case: n = 2m, double the representation of m
      obtain ⟨m, rfl⟩ := heven
      have hm : m ≥ 1 := by omega
      have hm_lt : m < 2 * m := by omega
      obtain ⟨S, hne, hpf, hac, hsum⟩ := ih m hm_lt hm
      have hpos : ∀ s ∈ S, 0 < s := by
        intro s hs
        have := hpf s hs
        obtain ⟨k, l, rfl⟩ := this
        positivity
      refine ⟨S.image (· * 2), ?_, ?_, ?_, ?_⟩
      · exact Finset.Nonempty.image hne _
      · intro s hs
        rw [Finset.mem_image] at hs
        obtain ⟨a, ha, rfl⟩ := hs
        exact isPowerForm_mul_two (hpf a ha)
      · exact noOneDividesAnother_image_mul_two hac hpos
      · rw [sum_image_mul_two (mul_two_injOn S), hsum]
    · -- Odd case: n is odd, n ≥ 3
      have hn3 : n ≥ 3 := by omega
      -- Let k = ⌊log₃ n⌋, so 3^k ≤ n < 3^(k+1)
      let k := Nat.log 3 n
      have h3k_le : 3 ^ k ≤ n := Nat.pow_log_le_self 3 n
      have hn_lt : n < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) (by omega)
      -- n - 3^k is even (odd - odd = even)
      have h3k_odd : ¬ 2 ∣ 3 ^ k := three_pow_odd k
      have hn_odd : ¬ 2 ∣ n := heven
      have hdiff_even : 2 ∣ (n - 3 ^ k) := by omega
      by_cases heq : n = 3 ^ k
      · -- Subcase: n = 3^k exactly
        subst heq
        exact ⟨{3 ^ k}, by simp, fun s hs => by simp at hs; subst hs; exact isPowerForm_pow_three k,
          fun a ha b hb hab => by simp at ha hb; omega, by simp⟩
      · -- Subcase: n > 3^k, so n - 3^k is positive and even
        have hdiff_pos : n - 3 ^ k ≥ 1 := by omega
        obtain ⟨m, hm_eq⟩ := hdiff_even
        have hm_pos : m ≥ 1 := by omega
        have hm_lt : m < n := by omega
        -- By IH, m has a representation
        obtain ⟨S, hne, hpf, hac, hsum⟩ := ih m hm_lt hm_pos
        have hpos : ∀ s ∈ S, 0 < s := by
          intro s hs; obtain ⟨a, b, rfl⟩ := hpf s hs; positivity
        -- Double S to represent n - 3^k = 2m
        let S' := S.image (· * 2)
        have hS'_sum : S'.sum id = n - 3 ^ k := by
          simp only [S', sum_image_mul_two (mul_two_injOn S), hsum, hm_eq]
        -- Add 3^k to the doubled set
        have h3k_notin : 3 ^ k ∉ S' := by
          intro hmem
          exact three_pow_odd k (image_mul_two_even hmem)
        -- No element of S' divides 3^k (they're even, 3^k is odd)
        have h_not_dvd_3k : ∀ s ∈ S', ¬ (s ∣ 3 ^ k) := by
          intro s hs
          exact even_not_dvd_odd (image_mul_two_even hs) (three_pow_odd k)
        -- 3^k doesn't divide any element of S' (each element < 2·3^k)
        have h_3k_not_dvd : ∀ s ∈ S', ¬ (3 ^ k ∣ s) := by
          intro s hs hdvd
          have hs_pos : 0 < s := by
            rw [Finset.mem_image] at hs; obtain ⟨a, ha, rfl⟩ := hs
            exact Nat.mul_pos (hpos a ha) (by norm_num)
          have hs_le : s ≤ S'.sum id :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
          have hs_ge : 3 ^ k ≤ s := Nat.le_of_dvd hs_pos hdvd
          have hs_lt : s < 2 * 3 ^ k := by
            calc s ≤ S'.sum id := hs_le
              _ = n - 3 ^ k := hS'_sum
              _ < 3 ^ (k + 1) - 3 ^ k := by omega
              _ = 2 * 3 ^ k := by ring
          -- s ∈ [3^k, 2·3^k) and 3^k | s, so s = 3^k
          -- But s is even (in image (· * 2)) and 3^k is odd — contradiction
          have hs_eq : s = 3 ^ k := by
            obtain ⟨c, hc⟩ := hdvd
            have hcge : c ≥ 1 := by
              rcases Nat.eq_zero_or_pos c with h0 | h0
              · rw [h0, mul_zero] at hc; omega
              · omega
            have hcle : c ≤ 1 := by
              by_contra hc2
              push_neg at hc2
              have : 3 ^ k * 2 ≤ 3 ^ k * c := Nat.mul_le_mul_left _ hc2
              linarith
            omega
          rw [hs_eq] at hs
          exact three_pow_odd k (image_mul_two_even hs)
        refine ⟨insert (3 ^ k) S', ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_nonempty _ _
        · intro s hs
          rw [Finset.mem_insert] at hs
          cases hs with
          | inl h => subst h; exact isPowerForm_pow_three k
          | inr h =>
            rw [Finset.mem_image] at h
            obtain ⟨a, ha, rfl⟩ := h
            exact isPowerForm_mul_two (hpf a ha)
        · intro a ha b hb hab
          rw [Finset.mem_insert] at ha hb
          cases ha with
          | inl ha =>
            subst ha
            cases hb with
            | inl hb => exact absurd hb hab
            | inr hb => exact h_3k_not_dvd b hb
          | inr ha =>
            cases hb with
            | inl hb => subst hb; exact h_not_dvd_3k a ha
            | inr hb => exact noOneDividesAnother_image_mul_two hac hpos a ha b hb hab
        · rw [Finset.sum_insert h3k_notin, hS'_sum]
          omega

/--
**Key lemma: Representing even numbers with even summands:**
If n is even and representable, it has a representation with all even summands.
-/
/-
## Part III: General Case (p,q) ≠ (2,3)
-/

/--
**Erdős-Lewin Theorem (1996):**
The set of non-representable numbers is finite if and only if {p,q} = {2,3}.
-/
axiom erdos_lewin_theorem (p q : ℕ) :
    p > q → q ≥ 2 → Nat.Coprime p q →
    (Set.Finite (NonRepresentable p q) ↔ (p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))

/--
**Infinitely many non-representable for most (p,q):**
If {p,q} ≠ {2,3}, there are infinitely many non-representable numbers.
-/
theorem infinitely_many_non_rep (p q : ℕ) (hp : p > q) (hq : q ≥ 2)
    (hcop : Nat.Coprime p q) (hne : ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))) :
    Set.Infinite (NonRepresentable p q) := by
  have h := erdos_lewin_theorem p q hp hq hcop
  intro hfin
  exact hne (h.mp hfin)

/-
## Part IV: Yu-Chen Results (2022)
-/

/--
**Natural density of a set:**
d(A) = lim_{n→∞} |A ∩ {1,...,n}| / n
-/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ) / n - d| < ε

/--
**Yu-Chen Density Zero Theorem:**
The non-representable numbers have density zero for many parameter choices:
- q > 3, or
- q = 3 and p > 6, or
- q = 2 and p > 10
-/
/--
**Yu-Chen Coprime Non-Representables:**
There are infinitely many coprime non-representable numbers for most (p,q):
- q > 3, or
- q = 3 and p ≠ 5, or
- q = 2 and p ∉ {3, 5, 9}
-/
def CoprimeNonRepresentable (p q : ℕ) : Set ℕ :=
  {n ∈ NonRepresentable p q | Nat.Coprime n (p * q)}

/-
## Part V: Minimum Summand Size
-/

/--
**f(n) = largest floor function:**
For the {2,3} case, all large n can be represented with all summands > f(n).
Erdős-Lewin asked: what is the largest f(n) → ∞?
-/
noncomputable def minSummandBound (n : ℕ) : ℝ :=
  sSup {f : ℝ | ∃ S : Finset ℕ, (∀ s ∈ S, IsPowerForm 3 2 s ∧ (s : ℝ) > f) ∧
    NoOneDividesAnother S ∧ S.sum id = n}

/--
**Yu-Chen bounds (2022):**
n / (log n)^{log₂ 3} ≪ f(n) ≪ n / log n
-/
/--
**Yang-Zhao improvement (2025):**
The lower bound improves to f(n) ≫ n / log n.
-/
/-
## Part VI: Related Problems
-/

/--
**Related Problems:**
- Problem #123: The analog with three coprime bases (p, q, r)
- Problem #845: Additional questions about the {2,3} representation
- Problem #246: Representations without the non-divisibility constraint
-/

/-
## Part VII: Examples
-/

/--
**Example: 1 = 2^0 · 3^0:**
The number 1 is trivially representable (single summand).
-/
theorem example_1_representable : IsRepresentable 3 2 1 := by
  use {1}
  constructor
  · simp
  constructor
  · intro s hs
    simp at hs
    subst hs
    use 0, 0
    simp
  constructor
  · intro a ha b hb hab
    simp at ha hb
    omega
  · simp

/--
**Example: Small cases for {3,2}:**
All of 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 are representable.
-/
/-
## Part VIII: Summary
-/

/--
**Erdős Problem #1110: Status**

**QUESTION 1:** For {p,q} ≠ {2,3}, what is the density of non-representable numbers?
**ANSWER:** Zero density in many cases (Yu-Chen 2022), but OPEN in general.

**QUESTION 2:** Are there infinitely many coprime non-representable numbers?
**ANSWER:** YES for most parameter choices (Yu-Chen 2022).

**KEY RESULTS:**
1. {2,3} case: All positive integers representable (simple induction)
2. Other cases: Infinitely many non-representable (Erdős-Lewin)
3. Density zero for large p or q > 3 (Yu-Chen)
4. Infinitely many coprime non-representables for most (p,q) (Yu-Chen)
5. Minimum summand bounds: f(n) ~ n/log n (Yu-Chen, Yang-Zhao)

**HISTORICAL NOTE:**
Erdős called his original {2,3} conjecture "silly" after it received a simple
inductive proof. The general problem remains rich and partially open.
-/
theorem erdos_1110_summary :
    -- {2,3} case is completely solved
    (∀ n ≥ 1, IsRepresentable 3 2 n) ∧
    -- Other cases have infinitely many non-representables
    (∀ p q : ℕ, p > q → q ≥ 2 → Nat.Coprime p q →
      ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3)) →
      Set.Infinite (NonRepresentable p q)) := by
  constructor
  · exact case_2_3_all_representable
  · intro p q hp hq hcop hne
    exact infinitely_many_non_rep p q hp hq hcop hne

/-- {2,3} case fully solved: every n ≥ 1 is representable.
    General case partially open: non-{2,3} coprime pairs have
    infinitely many non-representable integers. -/
theorem erdos_1110_status :
    (∀ n ≥ 1, IsRepresentable 3 2 n) ∧
    (∀ p q : ℕ, p > q → q ≥ 2 → Nat.Coprime p q →
      ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3)) →
      Set.Infinite (NonRepresentable p q)) :=
  ⟨case_2_3_all_representable, fun p q hp hq hcop hne =>
    infinitely_many_non_rep p q hp hq hcop hne⟩

end Erdos1110
