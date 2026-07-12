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

import Mathlib

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
  dsimp only at h
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
  induction n using Nat.strong_induction_on with
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
      have h3k_le : 3 ^ k ≤ n := Nat.pow_log_le_self 3 (by omega)
      have hn_lt : n < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) n
      -- n - 3^k is even (odd - odd = even)
      have h3k_odd : ¬ 2 ∣ 3 ^ k := three_pow_odd k
      have hn_odd : ¬ 2 ∣ n := heven
      have hdiff_even : 2 ∣ (n - 3 ^ k) := by omega
      by_cases heq : n = 3 ^ k
      · -- Subcase: n = 3^k exactly (rw rather than subst: `k := Nat.log 3 n` depends on n)
        rw [heq]
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
            Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hs
          have hs_ge : 3 ^ k ≤ s := Nat.le_of_dvd hs_pos hdvd
          have hs_lt : s < 2 * 3 ^ k := by
            calc s ≤ S'.sum id := hs_le
              _ = n - 3 ^ k := hS'_sum
              _ < 3 ^ (k + 1) - 3 ^ k := by omega
              _ = 2 * 3 ^ k := by rw [pow_succ]; omega
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
            have hc1 : c = 1 := by omega
            rw [hc1, mul_one] at hc
            exact hc
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
            | inl hb => exact absurd hb.symm hab
            | inr hb => exact h_3k_not_dvd b hb
          | inr ha =>
            cases hb with
            | inl hb => subst hb; exact h_not_dvd_3k a ha
            | inr hb => exact noOneDividesAnother_image_mul_two hac hpos a ha b hb hab
        · rw [Finset.sum_insert h3k_notin, hS'_sum]
          simp only [id_eq]
          omega

/-
## Part IIb: The Easy Direction of Erdős–Lewin (unconditional, 0-axiom)

The original development axiomatised the full Erdős–Lewin *iff*
`Finite (NonRepresentable p q) ↔ {p,q} = {2,3}`. Only the forward
direction (`Finite ⟹ {2,3}`, equivalently `{p,q} ≠ {2,3} ⟹ Infinite`) is
the deep theorem. The backward direction (`{2,3} ⟹ Finite`) is an immediate
corollary of `case_2_3_all_representable`, which we already proved by
induction. We discharge it here so it is no longer assumed, and in fact pin
down the non-representable set exactly: `NonRepresentable 3 2 = {0}`.
-/

/-- Power forms are commutative in the base pair: `p^k q^l` and `q^l p^k` range
over the same set, so `IsPowerForm p q = IsPowerForm q p` as predicates. -/
lemma isPowerForm_comm {p q n : ℕ} : IsPowerForm p q n ↔ IsPowerForm q p n := by
  constructor <;> · rintro ⟨k, l, rfl⟩; exact ⟨l, k, by ring⟩

/-- Representability only depends on the (symmetric) set of power forms, so it is
invariant under swapping the two bases. -/
lemma isRepresentable_comm {p q n : ℕ} :
    IsRepresentable p q n ↔ IsRepresentable q p n := by
  constructor
  · rintro ⟨S, hne, hpf, hac, hsum⟩
    exact ⟨S, hne, fun s hs => isPowerForm_comm.mp (hpf s hs), hac, hsum⟩
  · rintro ⟨S, hne, hpf, hac, hsum⟩
    exact ⟨S, hne, fun s hs => isPowerForm_comm.mp (hpf s hs), hac, hsum⟩

/-- Zero is never representable: a nonempty antichain of positive power forms has
strictly positive sum. -/
lemma not_isRepresentable_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ¬ IsRepresentable p q 0 := by
  rintro ⟨S, hne, hpf, _, hsum⟩
  obtain ⟨s, hs⟩ := hne
  obtain ⟨k, l, rfl⟩ := hpf s hs
  have hpos : 0 < p ^ k * q ^ l := mul_pos (pow_pos hp k) (pow_pos hq l)
  have hle : p ^ k * q ^ l ≤ S.sum id :=
    Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hs
  omega

/-- **Exact characterisation of the {3,2} case:** the only non-representable
number is `0`. Every `n ≥ 1` is representable (`case_2_3_all_representable`) and
`0` is not (`not_isRepresentable_zero`). -/
theorem nonRepresentable_three_two : NonRepresentable 3 2 = {0} := by
  ext n
  simp only [NonRepresentable, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hn
    by_contra hne
    exact hn (case_2_3_all_representable n (by omega))
  · rintro rfl
    exact not_isRepresentable_zero (by norm_num) (by norm_num)

/-- Same characterisation with the bases written in the other order. -/
theorem nonRepresentable_two_three : NonRepresentable 2 3 = {0} := by
  ext n
  simp only [NonRepresentable, Set.mem_setOf_eq, Set.mem_singleton_iff,
    isRepresentable_comm (p := 2) (q := 3)]
  constructor
  · intro hn
    by_contra hne
    exact hn (case_2_3_all_representable n (by omega))
  · rintro rfl
    exact not_isRepresentable_zero (by norm_num) (by norm_num)

/-- **Easy direction of Erdős–Lewin (unconditional).** If `{p,q} = {2,3}` then the
set of non-representable numbers is finite — indeed it is the singleton `{0}`.
This needs no axiom. -/
theorem finite_nonRepresentable_of_two_three {p q : ℕ}
    (h : (p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3)) :
    Set.Finite (NonRepresentable p q) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [nonRepresentable_three_two]; exact Set.finite_singleton 0
  · rw [nonRepresentable_two_three]; exact Set.finite_singleton 0

/-
## Part IIc: Existence of a positive non-representable (unconditional, 0-axiom)

The deep direction `erdos_lewin_infinite` (axiomatised below) asserts that every
coprime pair `{p,q} ≠ {2,3}` leaves *infinitely many* non-representable numbers.
Its existence shadow — that there is *at least one positive* non-representable
number — is far more elementary and can be proved unconditionally. We exhibit a
universal small witness:

* if both bases are `≥ 3`, then `2` is non-representable (the only power form
  `≤ 2` is `1`, and a distinct-element antichain of `1`s sums to at most `1`);
* if `q = 2` (so `p ≥ 4`, since `p > 2` and `p ≠ 3`), then `3` is
  non-representable (power forms `≤ 3` are exactly `{1,2}`, and `{1,2}` is not an
  antichain because `1 ∣ 2`).

This sharpens the contrast with `nonRepresentable_three_two = {0}`: the `{2,3}`
pair has **no** positive non-representable number, while **every** other coprime
pair has one. It is the (unconditional) existence version of the open infinitude
statement, and needs no axiom.
-/

/-- When both bases are `≥ 3`, the only power form that is `≤ 2` is `1`:
any positive exponent on a base `≥ 3` already pushes the value to `≥ 3`. -/
lemma isPowerForm_eq_one_of_le_two {p q n : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : IsPowerForm p q n) (hle : n ≤ 2) : n = 1 := by
  obtain ⟨k, l, rfl⟩ := h
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have hql : 1 ≤ q ^ l := Nat.one_le_pow _ _ (by omega)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · simp [hk, hl]
    · have hqge : 3 ≤ q ^ l := le_trans hq (Nat.le_self_pow (by omega) q)
      have : 3 ≤ p ^ k * q ^ l :=
        le_trans hqge (Nat.le_mul_of_pos_left (q ^ l) hpk)
      omega
  · have hpge : 3 ≤ p ^ k := le_trans hp (Nat.le_self_pow (by omega) p)
    have : 3 ≤ p ^ k * q ^ l :=
      le_trans hpge (Nat.le_mul_of_pos_right (p ^ k) hql)
    omega

/-- **`2` is non-representable when both bases are `≥ 3`.** Every summand is a
power form `≤ 2`, hence equal to `1`; a `Finset` of distinct `1`s is at most the
singleton `{1}`, whose sum is `1`, never `2`. -/
theorem two_nonRepresentable_of_three_le {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    ¬ IsRepresentable p q 2 := by
  rintro ⟨S, hne, hpf, _, hsum⟩
  have hle : ∀ s ∈ S, s ≤ 2 := by
    intro s hs
    have hb := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hs
    rw [hsum] at hb
    exact hb
  have hone : ∀ s ∈ S, s = 1 := fun s hs =>
    isPowerForm_eq_one_of_le_two hp hq (hpf s hs) (hle s hs)
  have hsub : S ⊆ {1} := fun s hs => Finset.mem_singleton.mpr (hone s hs)
  rcases Finset.subset_singleton_iff.mp hsub with h0 | h1
  · exact (Finset.nonempty_iff_ne_empty.mp hne) h0
  · rw [h1] at hsum; simp at hsum

/-- When `q = 2` and `p ≥ 4`, the only power forms that are `≤ 3` are `1` and
`2`: a positive exponent on `p ≥ 4` gives a value `≥ 4`, so the form is a pure
power of `2`, and `2 ^ l ≤ 3` forces `l ≤ 1`. -/
lemma isPowerForm_le_two_or_eq {p n : ℕ} (hp : 4 ≤ p)
    (h : IsPowerForm p 2 n) (hle : n ≤ 3) : n = 1 ∨ n = 2 := by
  obtain ⟨k, l, rfl⟩ := h
  have hk0 : k = 0 := by
    by_contra hk
    have hpge : 4 ≤ p ^ k := le_trans hp (Nat.le_self_pow hk p)
    have hql : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
    have : 4 ≤ p ^ k * 2 ^ l :=
      le_trans hpge (Nat.le_mul_of_pos_right (p ^ k) hql)
    omega
  subst hk0
  simp only [pow_zero, one_mul] at hle ⊢
  match l with
  | 0 => left; simp
  | 1 => right; simp
  | (m + 2) =>
    exfalso
    have h4 : (4 : ℕ) ≤ 2 ^ (m + 2) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **`3` is non-representable when `q = 2` and `p ≥ 4`.** Each summand is a
power form `≤ 3`, hence `1` or `2`. To reach the sum `3` the antichain would have
to contain both `1` and `2`, but `1 ∣ 2` violates the antichain condition; a set
of `1`s alone sums to `≤ 1` and a set of `2`s alone to `≤ 2`. -/
theorem three_nonRepresentable_of_q_two {p : ℕ} (hp : 4 ≤ p) :
    ¬ IsRepresentable p 2 3 := by
  rintro ⟨S, _, hpf, hac, hsum⟩
  have hle : ∀ s ∈ S, s ≤ 3 := by
    intro s hs
    have hb := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hs
    rw [hsum] at hb
    exact hb
  have hmem : ∀ s ∈ S, s = 1 ∨ s = 2 := fun s hs =>
    isPowerForm_le_two_or_eq hp (hpf s hs) (hle s hs)
  by_cases h1 : (1 : ℕ) ∈ S
  · by_cases h2 : (2 : ℕ) ∈ S
    · exact hac 1 h1 2 h2 (by norm_num) (by norm_num)
    · -- no `2`s: `S ⊆ {1}`, sum `≤ 1`
      have hsub : S ⊆ {1} := by
        intro s hs
        rcases hmem s hs with h | h
        · exact Finset.mem_singleton.mpr h
        · exact absurd (h ▸ hs) h2
      have hb : S.sum id ≤ ({1} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub
      rw [hsum] at hb
      simp at hb
  · -- no `1`s: `S ⊆ {2}`, sum `≤ 2`
    have hsub : S ⊆ {2} := by
      intro s hs
      rcases hmem s hs with h | h
      · exact absurd (h ▸ hs) h1
      · exact Finset.mem_singleton.mpr h
    have hb : S.sum id ≤ ({2} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub
    rw [hsum] at hb
    simp at hb

/-- **Unconditional existence of a positive non-representable number** for every
coprime pair `p > q ≥ 2` with `{p,q} ≠ {2,3}`. This is the existence shadow of
the deep infinitude statement `erdos_lewin_infinite`, proved here with **no
axiom**. Contrast with `nonRepresentable_three_two`: the `{2,3}` pair has the
non-representable set `{0}` (no *positive* witness), whereas here every other
coprime pair admits one — the universal witness `2` (when `q ≥ 3`) or `3`
(when `q = 2`). -/
theorem exists_positive_nonRepresentable_of_ne_two_three
    {p q : ℕ} (hp : p > q) (hq : q ≥ 2) (_hcop : Nat.Coprime p q)
    (hne : ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))) :
    ∃ n, 1 ≤ n ∧ n ∈ NonRepresentable p q := by
  rcases Nat.lt_or_ge q 3 with hq2 | hq3
  · -- `q = 2`; then `p > 2` and `p ≠ 3`, so `p ≥ 4`
    have hq2' : q = 2 := by omega
    subst hq2'
    have hp3 : p ≠ 3 := fun h => hne (Or.inl ⟨h, rfl⟩)
    have hp4 : 4 ≤ p := by omega
    exact ⟨3, by norm_num, three_nonRepresentable_of_q_two hp4⟩
  · -- `q ≥ 3`, so `p > q ≥ 3` and both bases are `≥ 3`
    exact ⟨2, by norm_num, two_nonRepresentable_of_three_le (by omega) hq3⟩

/-
## Part IId: Window Characterization (unconditional, 0-axiom)

The two ad-hoc witnesses above (`2` when `q ≥ 3`, `3` when `q = 2`) are special
cases of a single structural fact: because the unit power form `1 = p^0 q^0`
divides *every* other power form, it can never sit in a representing antichain
alongside another summand. Hence for `n ≥ 2` **every summand is `≥ q`** (the
smallest power form exceeding `1`). Two or more such summands already sum past
`2q`, so on the window `[q, 2q)` a representation can only be the singleton `{n}`
— i.e. `n` is representable iff it is itself a power form. This *characterises*
representability on the whole window (not just exhibits one witness) and
uniformly recovers both special cases above.
-/

/-- The smallest power form exceeding `1` is `q`: any `p^k q^l ≥ 2` (necessarily
with a positive exponent, given `p > q ≥ 2`) is at least `q`. -/
lemma isPowerForm_ge_q_of_ge_two {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (h : IsPowerForm p q n) (hn : 2 ≤ n) : q ≤ n := by
  obtain ⟨k, l, rfl⟩ := h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [pow_zero, one_mul] at hn ⊢
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp only [pow_zero] at hn; omega
    · calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ l := Nat.pow_le_pow_right (by omega) hl
  · have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hql : 1 ≤ q ^ l := Nat.one_le_pow _ _ (by omega)
    calc q ≤ p := by omega
      _ ≤ p ^ k := hpk
      _ ≤ p ^ k * q ^ l := Nat.le_mul_of_pos_right (p ^ k) hql

/-- **Every summand of a representation of `n ≥ 2` is at least `q`.** The unit
power form `1` cannot appear alongside any other summand (it divides everything,
breaking the antichain) nor on its own (it would sum to `1 < 2 ≤ n`); so every
summand is `≥ 2`, hence `≥ q` by `isPowerForm_ge_q_of_ge_two`. -/
lemma representable_summands_ge_q {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hn : 2 ≤ n) {S : Finset ℕ}
    (hpf : ∀ s ∈ S, IsPowerForm p q s)
    (hac : NoOneDividesAnother S) (hsum : S.sum id = n) :
    ∀ s ∈ S, q ≤ s := by
  have hpos : ∀ s ∈ S, 1 ≤ s := by
    intro s hs
    obtain ⟨k, l, rfl⟩ := hpf s hs
    have : 0 < p ^ k * q ^ l := mul_pos (pow_pos (by omega) k) (pow_pos (by omega) l)
    omega
  -- `1 ∉ S`: it would divide a distinct second element, or be the lone summand.
  have h1 : (1 : ℕ) ∉ S := by
    intro h1mem
    by_cases hcard : S = {1}
    · rw [hcard] at hsum; simp at hsum; omega
    · obtain ⟨b, hbmem, hbne⟩ : ∃ b ∈ S, b ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hcard (Finset.eq_singleton_iff_unique_mem.mpr ⟨h1mem, hcon⟩)
      exact hac 1 h1mem b hbmem (Ne.symm hbne) (one_dvd b)
  intro s hs
  have hsne1 : s ≠ 1 := by rintro rfl; exact h1 hs
  have h1le := hpos s hs
  have hs2 : 2 ≤ s := by omega
  exact isPowerForm_ge_q_of_ge_two hp hq (hpf s hs) hs2

/-- **Every power form is representable** (unconditional, 0-axiom). A power form
`n = p^k q^l` is represented by the singleton antichain `{n}`: a one-element set is
vacuously an antichain (`NoOneDividesAnother`), its sole element is a power form, and it
sums to `n`. This is the base fact underlying the backward direction of the window
characterisation, and generalises `example_1_representable` (the `{3,2}` unit) to every
pair and every power form. -/
theorem isRepresentable_of_isPowerForm {p q n : ℕ} (h : IsPowerForm p q n) :
    IsRepresentable p q n :=
  ⟨{n}, Finset.singleton_nonempty n, by simpa using h,
    by intro a ha b hb hab; simp only [Finset.mem_singleton] at ha hb
       exact absurd (ha.trans hb.symm) hab,
    by simp⟩

/-- **The unit `1` is representable for every pair** — it is the power form `p^0 q^0`.
Generalises `example_1_representable` from `{3,2}` to all `p, q`. -/
theorem isRepresentable_one {p q : ℕ} : IsRepresentable p q 1 :=
  isRepresentable_of_isPowerForm ⟨0, 0, by simp⟩

/-- **Every power form `p^a q^b` is representable.** The representable set contains the
whole multiplicative monoid of power forms — immediate from `isRepresentable_of_isPowerForm`. -/
theorem isRepresentable_powerForm {p q : ℕ} (a b : ℕ) :
    IsRepresentable p q (p ^ a * q ^ b) :=
  isRepresentable_of_isPowerForm ⟨a, b, rfl⟩

/-- **Representability window characterization (unconditional, 0-axiom).**
For `q ≤ n < 2q`, the number `n` is representable iff it is itself a single power
form `p^k q^l`. Forward: every summand is `≥ q` (`representable_summands_ge_q`),
so two or more summands already exceed `2q > n`; the representation must be the
singleton `{n}`, forcing `n` to be a power form. Backward: a power form `n` is
represented by `{n}`. -/
theorem isRepresentable_iff_isPowerForm_window {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hlo : q ≤ n) (hhi : n < 2 * q) :
    IsRepresentable p q n ↔ IsPowerForm p q n := by
  constructor
  · rintro ⟨S, hne, hpf, hac, hsum⟩
    have hn2 : 2 ≤ n := by omega
    have hge : ∀ s ∈ S, q ≤ s := representable_summands_ge_q hp hq hn2 hpf hac hsum
    have hcard1 : S.card = 1 := by
      rcases Nat.lt_or_ge S.card 2 with hc | hc
      · have : 1 ≤ S.card := Finset.card_pos.mpr hne
        omega
      · exfalso
        obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hc
        have hsub : ({a, b} : Finset ℕ) ⊆ S := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hpair : ({a, b} : Finset ℕ).sum id ≤ S.sum id :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_pair hab, hsum] at hpair
        simp only [id_eq] at hpair
        have hqa := hge a ha
        have hqb := hge b hb
        omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard1
    rw [Finset.sum_singleton, id_eq] at hsum
    rw [← hsum]
    exact hpf x (Finset.mem_singleton_self x)
  · intro h
    exact isRepresentable_of_isPowerForm h

/-- **Non-power-forms in the window `[q, 2q)` are non-representable
(unconditional, 0-axiom).** Contrapositive of the window characterization. This
furnishes, for *every* pair `p > q ≥ 2`, an explicit family of non-representable
numbers (each non-power-form strictly between `q` and `2q`), uniformly subsuming
the ad-hoc witnesses `two_nonRepresentable_of_three_le` (take `n = 2`, `q ≥ 3`)
and `three_nonRepresentable_of_q_two` (take `n = 3`, `q = 2`). -/
theorem nonRepresentable_of_window {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hlo : q ≤ n) (hhi : n < 2 * q) (hnp : ¬ IsPowerForm p q n) :
    n ∈ NonRepresentable p q := by
  rw [NonRepresentable, Set.mem_setOf_eq,
    isRepresentable_iff_isPowerForm_window hp hq hlo hhi]
  exact hnp

/-- **Sharp criterion for the canonical candidate `q + 1` (unconditional, 0-axiom).**
For every pair `p > q ≥ 2` the number `q + 1` always lies in the window `[q, 2q)`,
so by the window characterization it is non-representable *exactly* when it is not
a power of `p`:

    `q + 1 ∈ NonRepresentable p q  ↔  ¬ ∃ k, q + 1 = p ^ k`.

The only power form `q + 1` could be is a pure power of `p`: a factor `q ^ l` with
`l ≥ 1` would force `q ∣ q + 1`, hence `q ∣ 1`, impossible for `q ≥ 2`. For `q = 2`
this says `q + 1 = 3` is non-representable unless `3 = p ^ k`, i.e. unless `p = 3` —
pinpointing the excluded `{2,3}` pair as the *unique* `q = 2` exception, the case
where the canonical witness `3` happens to be the power form `3 = 3 ^ 1`. -/
theorem add_one_nonRepresentable_iff {p q : ℕ} (hp : p > q) (hq : q ≥ 2) :
    (q + 1) ∈ NonRepresentable p q ↔ ¬ ∃ k : ℕ, q + 1 = p ^ k := by
  rw [NonRepresentable, Set.mem_setOf_eq,
    isRepresentable_iff_isPowerForm_window hp hq (by omega) (by omega)]
  simp only [IsPowerForm]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨k, l, hkl⟩
    refine ⟨k, ?_⟩
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simpa using hkl
    · exfalso
      have hqdvd : q ∣ q + 1 := by
        rw [hkl]; exact (dvd_pow_self q hl.ne').mul_left (p ^ k)
      have h1 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp hqdvd
      have := Nat.le_of_dvd one_pos h1
      omega
  · rintro ⟨k, hk⟩
    exact ⟨k, 0, by simpa using hk⟩

/-- **Easy sufficient condition: `q + 1` is non-representable whenever `p > q + 1`
(unconditional, 0-axiom).** If `p` overshoots `q + 1` then `q + 1` cannot be any
power `p ^ k` (`p ^ 0 = 1 < q + 1` and `p ^ k ≥ p > q + 1` for `k ≥ 1`), so the
criterion `add_one_nonRepresentable_iff` fires. This hands every pair with
`p ≥ q + 2` an explicit, trivially checkable non-representable number. -/
theorem add_one_nonRepresentable_of_lt {p q : ℕ} (hq : q ≥ 2) (hp : q + 1 < p) :
    (q + 1) ∈ NonRepresentable p q := by
  rw [add_one_nonRepresentable_iff (by omega) hq]
  rintro ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp at hk; omega
  · have hple : p ≤ p ^ k := Nat.le_self_pow hk0.ne' p
    omega

/-- The pair `(5, 2)`: `3 = q + 1` is non-representable (3 is not a power of 5). -/
example : (3 : ℕ) ∈ NonRepresentable 5 2 :=
  add_one_nonRepresentable_of_lt (by norm_num) (by norm_num)

/-- **Everything in the sub-unit window `[2, q)` is non-representable (unconditional,
0-axiom).** Every summand of a representation of `n ≥ 2` is `≥ q`
(`representable_summands_ge_q`), so any nonempty representation already sums to `≥ q`;
hence no `n` with `2 ≤ n < q` can be represented. This furnishes, for *every* pair
`p > q ≥ 2`, an explicit family of `q - 2` non-representable numbers — the whole
interval `[2, q)` — disjoint from the `[q, 2q)` window family
(`nonRepresentable_of_window`), which begins exactly where this one ends. -/
theorem nonRepresentable_of_lt_q {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hn : 2 ≤ n) (hlt : n < q) : n ∈ NonRepresentable p q := by
  rw [NonRepresentable, Set.mem_setOf_eq]
  rintro ⟨S, hne, hpf, hac, hsum⟩
  have hge := representable_summands_ge_q hp hq hn hpf hac hsum
  obtain ⟨s, hs⟩ := hne
  have hle : id s ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le i) hs
  rw [hsum] at hle
  simp only [id_eq] at hle
  have hqs := hge s hs
  omega

/-- **Representability characterization on the full lower window `[1, 2q)`
(unconditional, 0-axiom).** Strengthens `isRepresentable_iff_isPowerForm_window` from
`[q, 2q)` down to `[1, 2q)`: for every `1 ≤ n < 2q`,

    `IsRepresentable p q n ↔ IsPowerForm p q n`.

Below `q` the only power form is the unit `1` — any power form `≥ 2` is already `≥ q`
(`isPowerForm_ge_q_of_ge_two`) — and by `nonRepresentable_of_lt_q` every other `n < q`
is non-representable, so both sides agree there (true at `n = 1`, false on `[2, q)`).
On `[q, 2q)` this is the existing window characterization. The equivalence thus holds
on the entire initial segment below `2q`, with the sole representable numbers being the
power forms. -/
theorem isRepresentable_iff_isPowerForm_below_two_q {p q n : ℕ} (hp : p > q)
    (hq : q ≥ 2) (hlo : 1 ≤ n) (hhi : n < 2 * q) :
    IsRepresentable p q n ↔ IsPowerForm p q n := by
  rcases Nat.lt_or_ge n q with hnq | hnq
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- `n = 1`: the unit power form, representable.
      have hn1 : n = 1 := by omega
      subst hn1
      exact ⟨fun _ => ⟨0, 0, by simp⟩, fun _ => isRepresentable_one⟩
    · -- `2 ≤ n < q`: both sides false.
      constructor
      · intro hrep
        have hnr := nonRepresentable_of_lt_q hp hq h2 hnq
        rw [NonRepresentable, Set.mem_setOf_eq] at hnr
        exact absurd hrep hnr
      · intro hpf
        exact absurd (isPowerForm_ge_q_of_ge_two hp hq hpf h2) (by omega)
  · exact isRepresentable_iff_isPowerForm_window hp hq hnq hhi

/-- **`2` is non-representable for every pair with `q ≥ 3`** (unconditional, 0-axiom).
Immediate from `nonRepresentable_of_lt_q` (`2 ∈ [2, q)` once `q ≥ 3`). This drops the
`3 ≤ p` hypothesis of `two_nonRepresentable_of_three_le`: only `p > q ≥ 3` is required
(which forces `p ≥ 4` anyway), so the witness `2` needs no separate assumption on `p`. -/
theorem two_nonRepresentable_of_q_ge_three {p q : ℕ} (hp : p > q) (hq : q ≥ 3) :
    (2 : ℕ) ∈ NonRepresentable p q :=
  nonRepresentable_of_lt_q hp (by omega) (le_refl 2) (by omega)

/-
## Part IId': The sharp lower window `[1, p + q)` (unconditional, 0-axiom)

The `[q, 2q)` window bound `isRepresentable_iff_isPowerForm_window` used only the crude
estimate "two summands, each `≥ q`, sum to `≥ 2q`". That is not tight: the *smallest*
possible sum of a genuine two-element antichain of power forms is not `2q` but `p + q`.

Indeed, every power form strictly below `p` is a **pure power of `q`** (any factor of `p`
already pushes the value up to `≥ p`), and pure powers of `q` form a divisibility *chain*.
So a two-element antichain cannot live entirely below `p`: at least one member is `≥ p`,
while the other is still `≥ q` (the unit `1` divides everything, so it never appears in an
antichain of size `≥ 2`). Hence any two-summand representation already sums to `≥ p + q`.

This sharpens the exact characterization `IsRepresentable ↔ IsPowerForm` from the interval
`[1, 2q)` up to `[1, p + q)` — strictly larger, since `p > q` gives `p + q > 2q`. The
threshold `p + q` is **optimal**: whenever `q ∤ p` the antichain `{p, q}` represents `p + q`
itself (`isRepresentable_p_add_q`), and `p + q` is generally not a power form, so the
equivalence must fail at `p + q`.
-/

/-- **A power form strictly below `p` is a pure power of `q`.** Any factor of `p`
(exponent `k ≥ 1`) already forces the value to be `≥ p`, so a power form `< p` must have
`k = 0`. -/
lemma isPowerForm_lt_p_pow_q {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (h : IsPowerForm p q n) (hlt : n < p) : ∃ l, n = q ^ l := by
  obtain ⟨k, l, rfl⟩ := h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact ⟨l, by rw [hk, pow_zero, one_mul]⟩
  · exfalso
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hql : 1 ≤ q ^ l := Nat.one_le_pow _ _ (by omega)
    have : p ≤ p ^ k * q ^ l := le_trans hpk (Nat.le_mul_of_pos_right _ hql)
    omega

/-- **Two power forms both below `p` are comparable under divisibility.** Below `p` every
power form is a pure power of `q` (`isPowerForm_lt_p_pow_q`), and the powers of `q` form a
chain, so one divides the other. -/
lemma powerForms_lt_p_dvd {p q a b : ℕ} (hp : p > q) (hq : q ≥ 2)
    (ha : IsPowerForm p q a) (hb : IsPowerForm p q b)
    (hap : a < p) (hbp : b < p) : a ∣ b ∨ b ∣ a := by
  obtain ⟨la, rfl⟩ := isPowerForm_lt_p_pow_q hp hq ha hap
  obtain ⟨lb, rfl⟩ := isPowerForm_lt_p_pow_q hp hq hb hbp
  rcases le_total la lb with h | h
  · exact Or.inl (pow_dvd_pow q h)
  · exact Or.inr (pow_dvd_pow q h)

/-- **The minimal sum of a two-element antichain of power forms is `p + q`
(unconditional, 0-axiom).** Given two distinct power forms `a, b` with neither dividing the
other: neither is `1` (the unit divides everything), so both are `≥ q`; and they cannot
both be `< p` (else they would be comparable powers of `q`), so the larger is `≥ p`. Hence
`a + b ≥ p + q`. -/
lemma antichain_pair_sum_ge {p q a b : ℕ} (hp : p > q) (hq : q ≥ 2)
    (ha : IsPowerForm p q a) (hb : IsPowerForm p q b)
    (hnd1 : ¬ a ∣ b) (hnd2 : ¬ b ∣ a) : p + q ≤ a + b := by
  have ha1 : a ≠ 1 := fun h => hnd1 (h ▸ one_dvd b)
  have hb1 : b ≠ 1 := fun h => hnd2 (h ▸ one_dvd a)
  have hapos : 0 < a := by
    obtain ⟨k, l, rfl⟩ := ha
    exact mul_pos (pow_pos (by omega) k) (pow_pos (by omega) l)
  have hbpos : 0 < b := by
    obtain ⟨k, l, rfl⟩ := hb
    exact mul_pos (pow_pos (by omega) k) (pow_pos (by omega) l)
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have haq : q ≤ a := isPowerForm_ge_q_of_ge_two hp hq ha ha2
  have hbq : q ≤ b := isPowerForm_ge_q_of_ge_two hp hq hb hb2
  have hmax : p ≤ a ∨ p ≤ b := by
    by_contra hcon
    push_neg at hcon
    rcases powerForms_lt_p_dvd hp hq ha hb hcon.1 hcon.2 with h | h
    · exact hnd1 h
    · exact hnd2 h
  rcases hmax with h | h <;> omega

/-- **Any representation with two or more summands has sum `≥ p + q`
(unconditional, 0-axiom).** Pick two distinct summands `a ≠ b`; they form an antichain, so
`a + b ≥ p + q` (`antichain_pair_sum_ge`), and the full sum dominates the pair. -/
lemma representable_card_two_sum_ge {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    {S : Finset ℕ} (hpf : ∀ s ∈ S, IsPowerForm p q s)
    (hac : NoOneDividesAnother S) (hcard : 2 ≤ S.card) (hsum : S.sum id = n) :
    p + q ≤ n := by
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair : ({a, b} : Finset ℕ).sum id ≤ S.sum id :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hab, hsum] at hpair
  simp only [id_eq] at hpair
  have hge := antichain_pair_sum_ge hp hq (hpf a ha) (hpf b hb)
    (hac a ha b hb hab) (hac b hb a ha (Ne.symm hab))
  omega

/-- **Sharp representability characterization on the lower window `[1, p + q)`
(unconditional, 0-axiom).** For every `1 ≤ n < p + q`,

    `IsRepresentable p q n ↔ IsPowerForm p q n`.

Any representation with `≥ 2` summands has sum `≥ p + q` (`representable_card_two_sum_ge`),
so below `p + q` every representation is a singleton `{n}`, forcing `n` to be a power form;
the converse is `isRepresentable_of_isPowerForm`. Strictly strengthens
`isRepresentable_iff_isPowerForm_below_two_q` (`p + q > 2q` since `p > q`). -/
theorem isRepresentable_iff_isPowerForm_below_p_add_q {p q n : ℕ} (hp : p > q)
    (hq : q ≥ 2) (hlo : 1 ≤ n) (hhi : n < p + q) :
    IsRepresentable p q n ↔ IsPowerForm p q n := by
  constructor
  · rintro ⟨S, hne, hpf, hac, hsum⟩
    have hcard1 : S.card = 1 := by
      rcases Nat.lt_or_ge S.card 2 with hc | hc
      · have : 1 ≤ S.card := Finset.card_pos.mpr hne
        omega
      · have := representable_card_two_sum_ge hp hq hpf hac hc hsum
        omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard1
    rw [Finset.sum_singleton, id_eq] at hsum
    rw [← hsum]
    exact hpf x (Finset.mem_singleton_self x)
  · intro h
    exact isRepresentable_of_isPowerForm h

/-- **Non-power-forms in the sharp window `[1, p + q)` are non-representable
(unconditional, 0-axiom).** Contrapositive of `isRepresentable_iff_isPowerForm_below_p_add_q`:
for every pair `p > q ≥ 2` this hands an explicit non-representable for each non-power-form
below `p + q` — a strictly larger family than the `[q, 2q)` window
(`nonRepresentable_of_window`). -/
theorem nonRepresentable_of_below_p_add_q {p q n : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hlo : 1 ≤ n) (hhi : n < p + q) (hnp : ¬ IsPowerForm p q n) :
    n ∈ NonRepresentable p q := by
  rw [NonRepresentable, Set.mem_setOf_eq,
    isRepresentable_iff_isPowerForm_below_p_add_q hp hq hlo hhi]
  exact hnp

/-- **Sharpness of the `p + q` threshold (unconditional, 0-axiom).** Whenever `q ∤ p` the
antichain `{p, q}` represents `p + q`: both are power forms (`p = p^1 q^0`, `q = p^0 q^1`),
they are distinct (`p > q`), and neither divides the other (`p ∤ q` because `q < p`, and
`q ∤ p` by hypothesis). Since `p + q` is in general not a power form, the equivalence
`isRepresentable_iff_isPowerForm_below_p_add_q` genuinely stops at `p + q`. -/
theorem isRepresentable_p_add_q {p q : ℕ} (hp : p > q) (hq : q ≥ 2)
    (hqp : ¬ q ∣ p) : IsRepresentable p q (p + q) := by
  refine ⟨{p, q}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hpq : ¬ p ∣ q := fun h => by
      have := Nat.le_of_dvd (by omega) h; omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hpq
    · exact hqp
    · exact absurd rfl hab
  · rw [Finset.sum_pair (by omega : p ≠ q)]
    simp

/-
## Part IIe: Multiplicative Closure of Representability (unconditional, 0-axiom)

The `{2,3}` induction (`case_2_3_all_representable`) rested on a *doubling* step:
multiplying a representing antichain by `2` keeps it a representing antichain
(`isPowerForm_mul_two`, `noOneDividesAnother_image_mul_two`, …). That doubling is
the `c = 2` instance of a single structural fact valid for **either base**: scaling
a representation by `p` (or `q`) is again a representation. We record the general
statement here.

The key algebraic point is that the antichain ("no element divides another")
relation is *invariant under scaling by a fixed positive constant*: `c·a ∣ c·b ↔
a ∣ b`. Combined with the fact that `c · p^k q^l` is still a power form (with the
exponent of the relevant base raised by one), this yields:

* `IsRepresentable p q n ⟹ IsRepresentable p q (p·n)` and `(q·n)`;
* by iteration, `IsRepresentable p q n ⟹ IsRepresentable p q (p^a q^b · n)` — the
  set of representable numbers is closed under multiplication by every power form;
* contrapositively, **non-representability propagates to power-form divisors**: if
  `p^a q^b · n` is non-representable, then so is `n`.

This is genuine structural theory (a `ℕ`-action of the multiplicative monoid of
power forms on the representable set), 0-axiom, and it subsumes the ad-hoc doubling
machinery. It does **not** resolve the open infinitude direction: the propagation
goes *downward* (to divisors), so it cannot manufacture infinitely many
non-representables from a single witness — the deep axiom `erdos_lewin_infinite`
remains untouched.
-/

/-- Multiplying a power form by `p` stays a power form: `p · p^k q^l = p^{k+1} q^l`. -/
lemma isPowerForm_mul_base_left {p q s : ℕ} (h : IsPowerForm p q s) :
    IsPowerForm p q (s * p) := by
  obtain ⟨k, l, rfl⟩ := h
  exact ⟨k + 1, l, by ring⟩

/-- Multiplying a power form by `q` stays a power form: `q · p^k q^l = p^k q^{l+1}`. -/
lemma isPowerForm_mul_base_right {p q s : ℕ} (h : IsPowerForm p q s) :
    IsPowerForm p q (s * q) := by
  obtain ⟨k, l, rfl⟩ := h
  exact ⟨k, l + 1, by ring⟩

/-- Scaling every element of an antichain by a fixed positive `c` preserves the
antichain property, since `c·a ∣ c·b ↔ a ∣ b`. (Generalises
`noOneDividesAnother_image_mul_two`, the `c = 2` case.) -/
lemma noOneDividesAnother_image_mul_const {S : Finset ℕ} {c : ℕ} (hc : 0 < c)
    (hS : NoOneDividesAnother S) :
    NoOneDividesAnother (S.image (· * c)) := by
  intro a ha b hb hab
  rw [Finset.mem_image] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hne : a' ≠ b' := by intro heq; subst heq; exact hab rfl
  intro hdvd
  exact hS a' ha' b' hb' hne ((Nat.mul_dvd_mul_iff_right hc).mp hdvd)

/-- Multiplication by a positive constant is injective on a `Finset` of naturals. -/
lemma mul_const_injOn (S : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    Set.InjOn (· * c) (↑S) := by
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_right hc h

/-- Scaling the antichain by `c` scales its sum by `c`. -/
lemma sum_image_mul_const {S : Finset ℕ} {c : ℕ} (hinj : Set.InjOn (· * c) (↑S)) :
    (S.image (· * c)).sum id = c * S.sum id := by
  rw [Finset.sum_image (fun a ha b hb => hinj ha hb)]
  simp [Finset.mul_sum, mul_comm]

/-- **Representability is closed under multiplication by `p`** (unconditional,
0-axiom). Scale a representing antichain of `n` by `p`: each summand `p^k q^l`
becomes `p^{k+1} q^l` (still a power form), the antichain property is preserved
(`noOneDividesAnother_image_mul_const`), and the sum scales to `p·n`. -/
theorem isRepresentable_mul_base_left {p q n : ℕ} (hp : 0 < p)
    (h : IsRepresentable p q n) : IsRepresentable p q (p * n) := by
  obtain ⟨S, hne, hpf, hac, hsum⟩ := h
  refine ⟨S.image (· * p), Finset.Nonempty.image hne _, ?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    exact isPowerForm_mul_base_left (hpf a ha)
  · exact noOneDividesAnother_image_mul_const hp hac
  · rw [sum_image_mul_const (mul_const_injOn S hp), hsum]

/-- **Representability is closed under multiplication by `q`** (unconditional,
0-axiom). Same argument scaling by `q`; each summand `p^k q^l` becomes
`p^k q^{l+1}`. -/
theorem isRepresentable_mul_base_right {p q n : ℕ} (hq : 0 < q)
    (h : IsRepresentable p q n) : IsRepresentable p q (q * n) := by
  obtain ⟨S, hne, hpf, hac, hsum⟩ := h
  refine ⟨S.image (· * q), Finset.Nonempty.image hne _, ?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    exact isPowerForm_mul_base_right (hpf a ha)
  · exact noOneDividesAnother_image_mul_const hq hac
  · rw [sum_image_mul_const (mul_const_injOn S hq), hsum]

/-- Closure under multiplication by `p^a` (iterating `isRepresentable_mul_base_left`). -/
theorem isRepresentable_mul_pow_left {p q n : ℕ} (hp : 0 < p) (a : ℕ)
    (h : IsRepresentable p q n) : IsRepresentable p q (p ^ a * n) := by
  induction a with
  | zero => simpa using h
  | succ k ih =>
    have h2 := isRepresentable_mul_base_left hp ih
    have heq : p ^ (k + 1) * n = p * (p ^ k * n) := by ring
    rwa [heq]

/-- Closure under multiplication by `q^b` (iterating `isRepresentable_mul_base_right`). -/
theorem isRepresentable_mul_pow_right {p q n : ℕ} (hq : 0 < q) (b : ℕ)
    (h : IsRepresentable p q n) : IsRepresentable p q (q ^ b * n) := by
  induction b with
  | zero => simpa using h
  | succ k ih =>
    have h2 := isRepresentable_mul_base_right hq ih
    have heq : q ^ (k + 1) * n = q * (q ^ k * n) := by ring
    rwa [heq]

/-- **Representability is closed under multiplication by every power form**
(unconditional, 0-axiom). If `n` is representable then so is `p^a q^b · n`: the
representable set is invariant under the multiplicative monoid action of the power
forms. This is the full structural generalisation of the `{2,3}` doubling step. -/
theorem isRepresentable_mul_powerForm {p q n : ℕ} (hp : 0 < p) (hq : 0 < q)
    (a b : ℕ) (h : IsRepresentable p q n) :
    IsRepresentable p q (p ^ a * q ^ b * n) := by
  have h1 := isRepresentable_mul_pow_left hp a h
  have h2 := isRepresentable_mul_pow_right hq b h1
  have heq : p ^ a * q ^ b * n = q ^ b * (p ^ a * n) := by ring
  rwa [heq]

/-- **Non-representability propagates to power-form divisors** (unconditional,
0-axiom). Contrapositive of `isRepresentable_mul_powerForm`: if `p^a q^b · n` is
non-representable, then `n` itself is non-representable. (The implication runs
*downward* to smaller divisors, so it does not generate new non-representables —
the open infinitude direction is unaffected.) -/
theorem nonRepresentable_of_mul_powerForm {p q n a b : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : (p ^ a * q ^ b * n) ∈ NonRepresentable p q) :
    n ∈ NonRepresentable p q := by
  rw [NonRepresentable, Set.mem_setOf_eq] at h ⊢
  exact fun hrep => h (isRepresentable_mul_powerForm hp hq a b hrep)

/-
## Part IIf: The Degenerate ("Chain") Regime — Infinitude is Elementary (0-axiom)

The deep axiom `erdos_lewin_infinite` below carries a `Nat.Coprime p q` hypothesis.
That hypothesis is not cosmetic: it excludes exactly the *degenerate* pairs where the
larger base is a power of the smaller (`p = q^k`), for which every power form
`p^a q^b = q^{k a + b}` is a pure power of `q`. Powers of a common base form a
divisibility **chain**, so no two of them can coexist in an antichain — a representing
set collapses to a singleton and representability coincides with being a power form for
*every* `n`, not merely below the `p + q` window. In this regime the "infinitely many
non-representables" conclusion is completely elementary (every number that is not a
power of `q` is non-representable), so the coprimality hypothesis of the deep theorem
marks the precise boundary between the elementary and the genuinely hard regimes.
-/

/-- **Chain regime ⟹ representability collapses to power forms, unconditionally
(0-axiom).** If every two power forms are divisibility-comparable then a representing
set, being an antichain (`NoOneDividesAnother`), has at most one element; hence for
**every** `n`, `IsRepresentable p q n ↔ IsPowerForm p q n`. Contrast the generic
regime, where this equivalence is sharp and stops at `p + q`
(`isRepresentable_iff_isPowerForm_below_p_add_q`). -/
theorem isRepresentable_iff_isPowerForm_of_chain {p q : ℕ}
    (hchain : ∀ a b, IsPowerForm p q a → IsPowerForm p q b → a ∣ b ∨ b ∣ a) (n : ℕ) :
    IsRepresentable p q n ↔ IsPowerForm p q n := by
  refine ⟨?_, isRepresentable_of_isPowerForm⟩
  rintro ⟨S, hne, hpf, hac, hsum⟩
  have hcard1 : S.card = 1 := by
    rcases Nat.lt_or_ge S.card 2 with hc | hc
    · have : 1 ≤ S.card := Finset.card_pos.mpr hne
      omega
    · exfalso
      obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hc
      rcases hchain a b (hpf a ha) (hpf b hb) with h | h
      · exact hac a ha b hb hab h
      · exact hac b hb a ha (Ne.symm hab) h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard1
  rw [Finset.sum_singleton, id_eq] at hsum
  rw [← hsum]
  exact hpf x (Finset.mem_singleton_self x)

/-- **When the larger base is a power of the smaller (`p = q^k`), the power forms are a
divisibility chain (0-axiom).** Every power form `(q^k)^a · q^b = q^{k a + b}` is a pure
power of `q`, and `q^i ∣ q^j ∨ q^j ∣ q^i` since the exponents are linearly ordered. -/
theorem powerForm_chain_of_base_pow {q : ℕ} (k : ℕ) :
    ∀ a b, IsPowerForm (q ^ k) q a → IsPowerForm (q ^ k) q b → a ∣ b ∨ b ∣ a := by
  rintro a b ⟨ka, la, rfl⟩ ⟨kb, lb, rfl⟩
  have ea : (q ^ k) ^ ka * q ^ la = q ^ (k * ka + la) := by rw [← pow_mul, ← pow_add]
  have eb : (q ^ k) ^ kb * q ^ lb = q ^ (k * kb + lb) := by rw [← pow_mul, ← pow_add]
  rw [ea, eb]
  rcases le_total (k * ka + la) (k * kb + lb) with hle | hle
  · exact Or.inl (pow_dvd_pow q hle)
  · exact Or.inr (pow_dvd_pow q hle)

/-- Every `(4,2)`-power form is either `1` or even: `4^a 2^b = 2^{2a+b}`, which is `1`
exactly when `a = b = 0` and otherwise divisible by `2`. -/
theorem isPowerForm_four_two_one_or_even {n : ℕ} (h : IsPowerForm 4 2 n) :
    n = 1 ∨ 2 ∣ n := by
  obtain ⟨a, b, rfl⟩ := h
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; subst hb; left; norm_num
    · subst hb; right
      simp only [pow_zero, mul_one]
      exact dvd_pow (by norm_num : (2 : ℕ) ∣ 4) ha.ne'
  · right
    exact (dvd_pow_self 2 hb.ne').mul_left (4 ^ a)

/-- **Concrete degenerate pair `(4, 2)`: representable ⇔ power of `2` (0-axiom).**
Since `4 = 2^2`, every power form `4^a 2^b = 2^{2a+b}` is a power of `2`, and the chain
collapse (`isRepresentable_iff_isPowerForm_of_chain`) gives `IsRepresentable 4 2 n ↔
IsPowerForm 4 2 n` for every `n`. Note `(4,2)` is *not* coprime, so the deep axiom
`erdos_lewin_infinite` does not even apply here. -/
theorem isRepresentable_four_two_iff (n : ℕ) :
    IsRepresentable 4 2 n ↔ IsPowerForm 4 2 n :=
  isRepresentable_iff_isPowerForm_of_chain
    (powerForm_chain_of_base_pow (q := 2) 2) n

/-- **Infinitely many non-representables for `(4, 2)` — elementary, 0-axiom.** Every odd
number `2m + 3 ≥ 3` is neither `1` nor even, hence not a `(4,2)`-power form
(`isPowerForm_four_two_one_or_even`), hence non-representable
(`isRepresentable_four_two_iff`). The injection `m ↦ 2m + 3` embeds `ℕ` into
`NonRepresentable 4 2`. This is precisely the conclusion of `erdos_lewin_infinite` — here
obtained with no axiom, because the degenerate (non-coprime) pair sits outside the deep
theorem's hypotheses. -/
theorem infinite_nonRepresentable_four_two :
    Set.Infinite (NonRepresentable 4 2) := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => 2 * m + 3) ?_ ?_
  · intro a b hab
    have : 2 * a + 3 = 2 * b + 3 := hab
    omega
  · intro m
    have hnp : ¬ IsPowerForm 4 2 (2 * m + 3) := by
      intro h
      rcases isPowerForm_four_two_one_or_even h with h1 | he <;> omega
    show (2 * m + 3) ∈ NonRepresentable 4 2
    rw [NonRepresentable, Set.mem_setOf_eq, isRepresentable_four_two_iff]
    exact hnp

/-! ### The full base-power family `(q^k, q)`

The concrete `(4, 2)` results above are the `q = 2, k = 2` instance of a uniform
phenomenon: whenever the larger base is a *power* of the smaller, `p = q^k`, the pair is
non-coprime and its power forms `(q^k)^a q^b = q^{ka+b}` are all powers of `q`, hence a
divisibility chain. The chain collapse then makes representability coincide with being a
power form for every `n`, and every number that is not a power of `q` is non-representable
— giving infinitely many non-representables with no axiom. This characterises the entire
non-coprime base-power regime, the exact complement of the coprime hypothesis of the deep
axiom `erdos_lewin_infinite`. -/

/-- Every `(q^k, q)`-power form with `k ≥ 1` is either `1` or divisible by `q`:
`(q^k)^a q^b = q^{ka+b}` equals `1` only when `a = b = 0`, and is a positive power of `q`
otherwise. The general-base companion of `isPowerForm_four_two_one_or_even`. -/
theorem isPowerForm_base_pow_one_or_dvd {q k n : ℕ} (hk : 1 ≤ k)
    (h : IsPowerForm (q ^ k) q n) : n = 1 ∨ q ∣ n := by
  obtain ⟨a, b, rfl⟩ := h
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; subst hb; left; norm_num
    · subst hb; right
      simp only [pow_zero, mul_one]
      exact dvd_pow (dvd_pow_self q (by omega : k ≠ 0)) ha.ne'
  · right
    exact (dvd_pow_self q hb.ne').mul_left ((q ^ k) ^ a)

/-- **Base-power regime `p = q^k`: representable ⇔ power form, unconditionally (0-axiom).**
Since `q^k` and `q` generate a divisibility chain (`powerForm_chain_of_base_pow`), a
representing antichain collapses to a singleton, so `IsRepresentable (q^k) q n ↔
IsPowerForm (q^k) q n` for every `n`. Generalises `isRepresentable_four_two_iff` (the
`q = 2, k = 2` instance) to the whole family. -/
theorem isRepresentable_base_pow_iff {q k n : ℕ} :
    IsRepresentable (q ^ k) q n ↔ IsPowerForm (q ^ k) q n :=
  isRepresentable_iff_isPowerForm_of_chain (powerForm_chain_of_base_pow k) n

/-- **Infinitely many non-representables for every base-power pair `(q^k, q)` — elementary,
0-axiom.** For `q ≥ 2` and `k ≥ 1`, each number `q(m+1)+1` exceeds `1` and leaves
remainder `1` on division by `q`, so it is neither `1` nor divisible by `q`; hence it is
not a `(q^k, q)`-power form (`isPowerForm_base_pow_one_or_dvd`) and therefore
non-representable (`isRepresentable_base_pow_iff`). The injection `m ↦ q(m+1)+1` embeds
`ℕ` into `NonRepresentable (q^k) q`. This is the full non-coprime base-power family of the
Erdős–Lewin phenomenon, obtained with no axiom; `infinite_nonRepresentable_four_two` is the
`q = 2, k = 2` case, and the coprimality hypothesis of `erdos_lewin_infinite` is exactly
what excludes this regime. -/
theorem infinite_nonRepresentable_base_pow {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    Set.Infinite (NonRepresentable (q ^ k) q) := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => q * (m + 1) + 1) ?_ ?_
  · intro a b hab
    change q * (a + 1) + 1 = q * (b + 1) + 1 at hab
    have h1 : q * (a + 1) = q * (b + 1) := by omega
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h1
    omega
  · intro m
    have hnp : ¬ IsPowerForm (q ^ k) q (q * (m + 1) + 1) := by
      intro h
      rcases isPowerForm_base_pow_one_or_dvd hk h with h1 | hd
      · have : 0 < q * (m + 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · have hone : q ∣ 1 := (Nat.dvd_add_right (dvd_mul_right q (m + 1))).mp hd
        have := Nat.le_of_dvd one_pos hone
        omega
    show (q * (m + 1) + 1) ∈ NonRepresentable (q ^ k) q
    rw [NonRepresentable, Set.mem_setOf_eq, isRepresentable_base_pow_iff]
    exact hnp

/-
## Part III: General Case (p,q) ≠ (2,3)
-/

/--
**Erdős-Lewin Theorem (1996), deep direction:**
If `{p,q} ≠ {2,3}` (with `p > q ≥ 2` coprime), there are infinitely many
non-representable numbers. This is the genuinely hard half of the
characterisation — the converse (`{2,3} ⟹ finite`) is proved unconditionally
above in `finite_nonRepresentable_of_two_three`. Not available in Mathlib 4.26.
-/
axiom erdos_lewin_infinite (p q : ℕ) :
    p > q → q ≥ 2 → Nat.Coprime p q →
    ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3)) →
    Set.Infinite (NonRepresentable p q)

/--
**Erdős-Lewin Theorem (1996), full iff** — now a *theorem*: the backward
direction is the unconditional `finite_nonRepresentable_of_two_three`, and only
the forward direction rests on the deep axiom `erdos_lewin_infinite`.
The set of non-representable numbers is finite iff `{p,q} = {2,3}`.
-/
theorem erdos_lewin_theorem (p q : ℕ) (hp : p > q) (hq : q ≥ 2)
    (hcop : Nat.Coprime p q) :
    Set.Finite (NonRepresentable p q) ↔ (p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3) := by
  constructor
  · intro hfin
    by_contra hne
    exact (erdos_lewin_infinite p q hp hq hcop hne) hfin
  · exact finite_nonRepresentable_of_two_three

/--
**Infinitely many non-representable for most (p,q):**
If {p,q} ≠ {2,3}, there are infinitely many non-representable numbers.
-/
theorem infinitely_many_non_rep (p q : ℕ) (hp : p > q) (hq : q ≥ 2)
    (hcop : Nat.Coprime p q) (hne : ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))) :
    Set.Infinite (NonRepresentable p q) :=
  erdos_lewin_infinite p q hp hq hcop hne

/-
## Part IV: Yu-Chen Results (2022)
-/

/-
**Natural density of a set:**
d(A) = lim_{n→∞} |A ∩ {1,...,n}| / n
-/
open scoped Classical in
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ) / n - d| < ε

/--
**The {2,3} non-representables have natural density zero (unconditional, 0-axiom).**

In the solved `{2,3}` case every positive integer is representable
(`case_2_3_all_representable`), so the non-representable set is exactly `{0}`
(`nonRepresentable_three_two`).  A single point has natural density `0`: for every
`n ≥ 1` precisely one element of `{0,…,n}` lies in `{0}`, so the counting ratio is
`1/n → 0`.  This is the density statement of Erdős #1110's *settled* case and the
first theorem to exercise the `HasDensity` definition.  (The open content of the
problem is the density in the *non*-`{2,3}` cases — zero in many cases by Yu-Chen
2022, open in general.) -/
theorem nonRepresentable_three_two_hasDensity_zero :
    HasDensity (NonRepresentable 3 2) 0 := by
  rw [nonRepresentable_three_two]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 N) hn
  -- Exactly one element of `{0,…,n}` lies in the singleton `{0}`, so the count is `1`.
  have hmem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  simp only [Set.mem_singleton_iff, Finset.filter_eq', hmem, if_true,
    Finset.card_singleton, Nat.cast_one, sub_zero]
  -- `|1/n| = 1/n < ε`, since `n ≥ N+1 > 1/ε`.
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [abs_of_pos (by positivity), div_lt_iff₀ hn0]
  have hNn : (1 / ε) < (n : ℝ) := by
    refine hN.trans_le ?_
    exact_mod_cast (by omega : (N : ℕ) ≤ n)
  rw [div_lt_iff₀ hε] at hNn
  rw [mul_comm]
  exact hNn

/-
**Yu-Chen Density Zero Theorem:**
The non-representable numbers have density zero for many parameter choices:
- q > 3, or
- q = 3 and p > 6, or
- q = 2 and p > 10
-/

/-- A single point has natural density `0`: for `n ≥ N` the count
`|{0} ∩ {0,…,n}| = 1`, so the ratio `1/n → 0`. (Helper for the `{2,3}` density-zero
instance below.) -/
theorem hasDensity_singleton_zero : HasDensity {0} 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have h0mem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  simp only [Set.mem_singleton_iff, Finset.filter_eq', h0mem, if_true,
    Finset.card_singleton, Nat.cast_one, sub_zero]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : (1 : ℝ) / ε < (n : ℝ) := by
    have : (N : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : N < n)
    linarith
  rw [abs_of_nonneg (by positivity), div_lt_iff₀ hnpos]
  rw [div_lt_iff₀ hε] at hcast
  linarith [mul_comm (n : ℝ) ε]

/-- **Yu-Chen density zero, `{2,3}` case (unconditional, 0-axiom).** For the base
pair `{2,3}` the non-representable set is the single point `{0}` (see
`nonRepresentable_two_three`), hence has natural density `0` — the sharpest possible
instance of the Yu-Chen density-zero phenomenon. No axiom needed. -/
theorem nonRepresentable_two_three_density_zero :
    HasDensity (NonRepresentable 2 3) 0 := by
  rw [nonRepresentable_two_three]; exact hasDensity_singleton_zero

/-- **Yu-Chen density zero, `{3,2}` case (unconditional, 0-axiom).** Same statement for
the reversed base pair (`NonRepresentable 3 2 = {0}`). -/
theorem nonRepresentable_three_two_density_zero :
    HasDensity (NonRepresentable 3 2) 0 := by
  rw [nonRepresentable_three_two]; exact hasDensity_singleton_zero

/--
**Yu-Chen Coprime Non-Representables:**
There are infinitely many coprime non-representable numbers for most (p,q):
- q > 3, or
- q = 3 and p ≠ 5, or
- q = 2 and p ∉ {3, 5, 9}
-/
def CoprimeNonRepresentable (p q : ℕ) : Set ℕ :=
  {n ∈ NonRepresentable p q | Nat.Coprime n (p * q)}

/-- The empty set has natural density `0`: the counting numerator is always `0`,
so the ratio is `0` for every `n ≥ 1`. (Helper for the `{2,3}` coprime
density-zero instances below.) -/
theorem hasDensity_empty : HasDensity (∅ : Set ℕ) 0 := by
  intro ε hε
  refine ⟨1, fun n _ => ?_⟩
  simp only [Set.mem_empty_iff_false, Finset.filter_false, Finset.card_empty,
    Nat.cast_zero, zero_div, sub_zero, abs_zero]
  exact hε

/- **Every finite set of naturals has natural density `0`** (unconditional, 0-axiom).
The general fact behind `hasDensity_singleton_zero` and `hasDensity_empty`: the
counting numerator `|A ∩ {0,…,n}|` never exceeds the fixed cardinality `|A|`, so the
ratio is at most `|A|/n → 0`. Combined with `finite_nonRepresentable_of_two_three`
this gives the `{2,3}` density-zero results directly, without computing the set. -/
open scoped Classical in
theorem hasDensity_zero_of_finite {A : Set ℕ} (hA : A.Finite) : HasDensity A 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((hA.toFinset.card : ℝ) / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsub : Finset.filter (· ∈ A) (Finset.range (n + 1)) ⊆ hA.toFinset := by
    intro k hk
    exact hA.mem_toFinset.mpr (Finset.mem_filter.mp hk).2
  have hcardR : ((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ)
      ≤ (hA.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  rw [sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hn0]
  have hCεn : (hA.toFinset.card : ℝ) < ε * n := by
    have hle : ((N : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (N : ℕ) ≤ n)
    have hNn : (hA.toFinset.card : ℝ) / ε < n := lt_of_lt_of_le hN hle
    rw [div_lt_iff₀ hε] at hNn
    linarith [mul_comm (n : ℝ) ε]
  linarith [hcardR]

/- **Natural density is unique** (unconditional, 0-axiom). If a set has natural
density `d₁` and also `d₂`, then `d₁ = d₂`. So `HasDensity A ·` is a genuine partial
function — "the density of `A`" is well-defined whenever it exists. Proof: if the two
densities differed, the counting ratio at a large `n` would sit within `|d₁−d₂|/2` of
both, forcing `|d₁−d₂| < |d₁−d₂|`. -/
open scoped Classical in
theorem hasDensity_unique {A : Set ℕ} {d₁ d₂ : ℝ}
    (h₁ : HasDensity A d₁) (h₂ : HasDensity A d₂) : d₁ = d₂ := by
  by_contra hne
  have hδpos : 0 < |d₁ - d₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N₁, hN₁⟩ := h₁ (|d₁ - d₂| / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h₂ (|d₁ - d₂| / 2) (by linarith)
  have e1 := hN₁ (max N₁ N₂ + 1) (by omega)
  have e2 := hN₂ (max N₁ N₂ + 1) (by omega)
  set r := ((Finset.filter (· ∈ A) (Finset.range (max N₁ N₂ + 1 + 1))).card : ℝ)
    / ((max N₁ N₂ + 1 : ℕ) : ℝ) with hr
  have key : |d₁ - d₂| ≤ |d₁ - r| + |r - d₂| := abs_sub_le d₁ r d₂
  rw [abs_sub_comm d₁ r] at key
  linarith [e1, e2, key]

/-- **The `{2,3}` coprime non-representables are empty (unconditional, 0-axiom).**

`CoprimeNonRepresentable` is the Yu-Chen object whose infinitude is asserted "for
most `(p,q)`" — explicitly excluding `{2,3}`. This theorem makes that exclusion
*sharp* for `{2,3}`: there are not merely finitely many coprime non-representables,
there are **none**. Indeed `NonRepresentable 2 3 = {0}` and `0` is not coprime to
`2·3 = 6` (`gcd 0 6 = 6 ≠ 1`), so the only non-representable is filtered out. This
gives the first content to the previously-unused `CoprimeNonRepresentable`
definition. -/
theorem coprimeNonRepresentable_two_three_eq_empty :
    CoprimeNonRepresentable 2 3 = ∅ := by
  rw [CoprimeNonRepresentable, nonRepresentable_two_three]
  ext n
  constructor
  · rintro ⟨hn, hcop⟩
    rw [Set.mem_singleton_iff] at hn
    subst hn
    rw [Nat.coprime_zero_left] at hcop
    norm_num at hcop
  · intro h; exact absurd h (Set.notMem_empty n)

/-- **The `{3,2}` coprime non-representables are empty (unconditional, 0-axiom).**
Same statement for the reversed base pair (`NonRepresentable 3 2 = {0}`, and `0` is
not coprime to `3·2 = 6`). -/
theorem coprimeNonRepresentable_three_two_eq_empty :
    CoprimeNonRepresentable 3 2 = ∅ := by
  rw [CoprimeNonRepresentable, nonRepresentable_three_two]
  ext n
  constructor
  · rintro ⟨hn, hcop⟩
    rw [Set.mem_singleton_iff] at hn
    subst hn
    rw [Nat.coprime_zero_left] at hcop
    norm_num at hcop
  · intro h; exact absurd h (Set.notMem_empty n)

/-- **Yu-Chen coprime density zero, `{2,3}` case (unconditional, 0-axiom).** Since the
`{2,3}` coprime non-representable set is empty, it has natural density `0` — the
degenerate extreme of the Yu-Chen coprime-density phenomenon, complementing the
infinitude that holds for the non-`{2,3}` pairs. -/
theorem coprimeNonRepresentable_two_three_density_zero :
    HasDensity (CoprimeNonRepresentable 2 3) 0 := by
  rw [coprimeNonRepresentable_two_three_eq_empty]; exact hasDensity_empty

/-- **Yu-Chen coprime density zero, `{3,2}` case (unconditional, 0-axiom).** Reversed
base pair; the coprime non-representable set is again empty. -/
theorem coprimeNonRepresentable_three_two_density_zero :
    HasDensity (CoprimeNonRepresentable 3 2) 0 := by
  rw [coprimeNonRepresentable_three_two_eq_empty]; exact hasDensity_empty

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
**Base value `minSummandBound 1 = 1`.**  Gives the scaffolding definition `minSummandBound`
concrete content at `n = 1`.  The only antichain of power-forms summing to `1` is `{1}`
itself: every power-form `3ᵏ2ˡ ≥ 1`, so a subset summing to `1` must be the singleton `{1}`.
Hence the witness set `{f | ∃ S, … ∧ ∑S = 1}` is exactly `{f | f < 1} = Iio 1` (the strict
bound `s > f` becomes `1 > f`), whose supremum is `1` by `csSup_Iio`.  So the largest
summand-size threshold achievable at `n = 1` is the value of the unique summand, `1`. -/
theorem minSummandBound_one : minSummandBound 1 = 1 := by
  have heq : minSummandBound 1 = sSup (Set.Iio (1 : ℝ)) := by
    unfold minSummandBound
    congr 1
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · rintro ⟨S, hpow, _, hsum⟩
      -- the witness sums to 1, so it is nonempty and contains a power-form ≤ 1, forcing 1
      have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hsum
      obtain ⟨s, hs⟩ := hne
      have h1le : 1 ≤ s := by
        obtain ⟨k, l, hkl⟩ := (hpow s hs).1
        rw [hkl]
        have : 0 < 3 ^ k * 2 ^ l := by positivity
        omega
      have hle1 : s ≤ 1 := by
        have hsingle : id s ≤ S.sum id :=
          Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hs
        rw [hsum] at hsingle
        simpa using hsingle
      have hs1 : s = 1 := le_antisymm hle1 h1le
      have hgt := (hpow s hs).2
      rw [hs1] at hgt; simpa using hgt
    · intro hf
      refine ⟨{1}, ?_, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs; subst hs
        exact ⟨⟨0, 0, by norm_num⟩, by simpa using hf⟩
      · intro a ha b hb hab
        rw [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact absurd rfl hab
      · simp
  rw [heq, csSup_Iio]

/-- Every `{2,3}` power form `3ᵏ2ˡ` is at least `1`. -/
private lemma one_le_isPowerForm_three_two {s : ℕ} (h : IsPowerForm 3 2 s) : 1 ≤ s := by
  obtain ⟨k, l, hkl⟩ := h
  subst hkl
  have : 0 < 3 ^ k * 2 ^ l := by positivity
  omega

/-- **Exact value on the whole power-form monoid: `minSummandBound (3ᵏ2ˡ) = 3ᵏ2ˡ`
(0-axiom).** Generalises `minSummandBound_one` (the `k = l = 0` case) from the single
point `1` to every power form `N = 3ᵏ2ˡ`. The witness set is exactly `Iio N`: the
singleton `{N}` represents `N` with its lone summand `N`, so every threshold `f < N`
is admissible (`Iio N ⊆ ·`); conversely any representation summing to `N` has some
summand `s ≤ N`, and the threshold obeys `f < s ≤ N`, so the set is contained in
`Iio N`. Its supremum is `N` by `csSup_Iio`. Thus on power forms the largest
achievable minimum-summand threshold is the number itself — the antichain is forced
to be the trivial singleton. -/
theorem minSummandBound_powerForm (k l : ℕ) :
    minSummandBound (3 ^ k * 2 ^ l) = (3 ^ k * 2 ^ l : ℕ) := by
  set N := 3 ^ k * 2 ^ l with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have heq : minSummandBound N = sSup (Set.Iio (N : ℝ)) := by
    unfold minSummandBound
    congr 1
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · rintro ⟨S, hpf, _, hsum⟩
      have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl
        simp only [Finset.sum_empty] at hsum; omega
      obtain ⟨s, hs⟩ := hne
      have hsf := (hpf s hs).2
      have hsle : s ≤ N := by
        have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hs
        rw [hsum] at this; simpa using this
      have : (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsle
      linarith
    · intro hf
      refine ⟨{N}, ?_, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs; subst hs
        exact ⟨⟨k, l, hN⟩, hf⟩
      · intro a ha b hb hab
        rw [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact absurd rfl hab
      · simp
  rw [heq, csSup_Iio]

/-- **Lower bound `1 ≤ minSummandBound n` for every `n ≥ 1` (0-axiom).** Every `n ≥ 1`
is representable in the `{2,3}` case (`case_2_3_all_representable`), and its summands
are power forms, hence `≥ 1`; so any threshold `f < 1` is admissible, giving
`Iio 1 ⊆` the witness set. The witness set is bounded above by `n` (some summand of any
representation is `≤ n`), so `minSummandBound n ≥ sSup (Iio 1) = 1`. -/
theorem one_le_minSummandBound {n : ℕ} (hn : 1 ≤ n) : 1 ≤ minSummandBound n := by
  obtain ⟨S, _, hpf, hac, hsum⟩ := case_2_3_all_representable n hn
  have hbdd : BddAbove {f : ℝ | ∃ T : Finset ℕ,
      (∀ s ∈ T, IsPowerForm 3 2 s ∧ (s : ℝ) > f) ∧ NoOneDividesAnother T ∧ T.sum id = n} := by
    refine ⟨(n : ℝ), ?_⟩
    rintro f ⟨T, hpfT, -, hsumT⟩
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl
      simp only [Finset.sum_empty] at hsumT; omega
    obtain ⟨t, ht⟩ := hTne
    have htf := (hpfT t ht).2
    have htle : t ≤ n := by
      have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) ht
      rw [hsumT] at this; simpa using this
    have : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htle
    linarith
  have hsub : Set.Iio (1 : ℝ) ⊆ {f : ℝ | ∃ T : Finset ℕ,
      (∀ s ∈ T, IsPowerForm 3 2 s ∧ (s : ℝ) > f) ∧ NoOneDividesAnother T ∧ T.sum id = n} := by
    intro f hf
    refine ⟨S, fun s hs => ⟨hpf s hs, ?_⟩, hac, hsum⟩
    have h1s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast one_le_isPowerForm_three_two (hpf s hs)
    have : f < 1 := hf
    linarith
  have hle := csSup_le_csSup hbdd ⟨(0 : ℝ), by rw [Set.mem_Iio]; norm_num⟩ hsub
  rw [csSup_Iio] at hle
  unfold minSummandBound
  exact hle

/-- **Upper bound `minSummandBound n ≤ n` for every `n ≥ 1` (0-axiom).** In any
representation summing to `n` some summand `s` satisfies `s ≤ n`, and the admissible
threshold obeys `f < s ≤ n`; hence the witness set is bounded above by `n` and its
supremum is `≤ n`. Together with `one_le_minSummandBound` this pins
`minSummandBound n ∈ [1, n]` for all `n ≥ 1`, with equality at the upper end exactly
on the power forms (`minSummandBound_powerForm`). -/
theorem minSummandBound_le_self {n : ℕ} (hn : 1 ≤ n) : minSummandBound n ≤ (n : ℝ) := by
  obtain ⟨S, _, hpf, hac, hsum⟩ := case_2_3_all_representable n hn
  unfold minSummandBound
  apply csSup_le
  · refine ⟨0, S, fun s hs => ⟨hpf s hs, ?_⟩, hac, hsum⟩
    have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast one_le_isPowerForm_three_two (hpf s hs)
    linarith
  · rintro f ⟨T, hpfT, -, hsumT⟩
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl
      simp only [Finset.sum_empty] at hsumT; omega
    obtain ⟨t, ht⟩ := hTne
    have htf := (hpfT t ht).2
    have htle : t ≤ n := by
      have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) ht
      rw [hsumT] at this; simpa using this
    have : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htle
    linarith

/-
**Yu-Chen bounds (2022):**
n / (log n)^{log₂ 3} ≪ f(n) ≪ n / log n
-/
/-
**Yang-Zhao improvement (2025):**
The lower bound improves to f(n) ≫ n / log n.
-/
/-
## Part VI: Related Problems
-/

/-
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
theorem example_1_representable : IsRepresentable 3 2 1 := isRepresentable_one

/-
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
