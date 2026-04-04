import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Glaisher Bijection as a Computable Function

This file formalizes the **Glaisher bijection** between partitions into distinct parts and
partitions into odd parts, giving a constructive proof of Euler's Partition Theorem.

## The Bijection

**Forward map (Distinct → Odd):**
For each distinct part k, write k = 2^a × b where b is odd (2-adic valuation).
Replace k with 2^a copies of the odd part b.

**Backward map (Odd → Distinct):**
For each distinct value b appearing m times, write m in binary:
m = Σᵢ εᵢ 2ⁱ. Replace m copies of b with distinct parts {2ⁱ × b | εᵢ = 1}.

## Example

Distinct {6, 5, 3} of 14:
- 6 = 2¹ × 3 → {3, 3}
- 5 = 2⁰ × 5 → {5}
- 3 = 2⁰ × 3 → {3}
Result: odd {5, 3, 3, 3}

## Main Results

- `glaisherFwdPart_sum`: forward step preserves weight
- `glaisherFwd_sum`: forward map preserves total weight
- `glaisherBwdStep_sum`: backward step preserves weight
- `glaisherBwdStep_pow_two`: backward of 2^a copies of b = singleton {2^a * b}
- `glaisherFwdPart_parts_odd`: forward produces only odd parts
-/

namespace GlaisherBijection

open Nat

/-! ## Forward Map: Distinct → Odd -/

/-- Forward step: map distinct part k to its odd parts.
    k = 2^a × b (b odd) → 2^a copies of b. -/
def glaisherFwdPart (k : ℕ) : Multiset ℕ :=
  Multiset.replicate (2 ^ padicValNat 2 k) (k / 2 ^ padicValNat 2 k)

/-- Glaisher forward map: apply glaisherFwdPart to each element. -/
def glaisherFwd (s : Multiset ℕ) : Multiset ℕ := s.bind glaisherFwdPart

/-! ## Backward Map: Odd → Distinct -/

/-- Backward step: odd b appearing m times → distinct parts via binary expansion of m.
    If m is odd: include b; recurse on m/2 doubling b.
    If m is even: skip; recurse on m/2 doubling b. -/
def glaisherBwdStep (b m : ℕ) : Multiset ℕ :=
  match m with
  | 0 => 0
  | n + 1 =>
    (if (n + 1) % 2 = 1 then ({b} : Multiset ℕ) else 0) +
    glaisherBwdStep (2 * b) ((n + 1) / 2)
termination_by m

/-- Backward map: for each distinct value b in s, apply glaisherBwdStep. -/
def glaisherBwd (s : Multiset ℕ) : Multiset ℕ :=
  s.toFinset.val.bind (fun b => glaisherBwdStep b (s.count b))

/-! ## Helper Lemmas for glaisherBwdStep

    Note: glaisherBwdStep uses well-founded recursion (since it recurses on m/2, not m-1).
    In Lean 4, well-founded definitions are not definitionally transparent, so we need
    explicit lemmas to unfold them. These are obviously true by definition. -/

/-- Base case: glaisherBwdStep b 0 = 0 -/
@[simp] lemma glaisherBwdStep_zero (b : ℕ) : glaisherBwdStep b 0 = 0 := by
  simp [glaisherBwdStep]

/-- Reduction lemma: explicit equation for glaisherBwdStep on nonzero input. -/
private lemma glaisherBwdStep_eq (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    glaisherBwdStep b m =
    (if m % 2 = 1 then ({b} : Multiset ℕ) else 0) +
    glaisherBwdStep (2 * b) (m / 2) := by
  cases m with
  | zero => exact absurd rfl hm
  | succ n => simp [glaisherBwdStep]

/-! ## Sum Preservation -/

/-- Key factorization: 2^a × (k / 2^a) = k when k ≠ 0 (a = padicValNat 2 k). -/
private lemma padic_factorization {k : ℕ} :
    2 ^ padicValNat 2 k * (k / 2 ^ padicValNat 2 k) = k :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

/-- The forward step preserves weight. -/
theorem glaisherFwdPart_sum {k : ℕ} (hk : k ≠ 0) :
    (glaisherFwdPart k).sum = k := by
  simp only [glaisherFwdPart, Multiset.sum_replicate, smul_eq_mul]
  exact padic_factorization

/-- The forward map preserves total weight. -/
theorem glaisherFwd_sum {s : Multiset ℕ} (hs : ∀ k ∈ s, k ≠ 0) :
    (glaisherFwd s).sum = s.sum := by
  simp only [glaisherFwd, Multiset.sum_bind]
  -- Goal: (s.map (fun k => (glaisherFwdPart k).sum)).sum = s.sum
  congr 1
  -- Subgoal: s.map (fun k => (glaisherFwdPart k).sum) = s
  have h_map : s.map (fun k => (glaisherFwdPart k).sum) = s.map (fun k => k) :=
    Multiset.map_congr rfl (fun k hk => glaisherFwdPart_sum (hs k hk))
  simp [h_map]

/-- The backward step preserves weight: (glaisherBwdStep b m).sum = m * b. -/
theorem glaisherBwdStep_sum (b m : ℕ) :
    (glaisherBwdStep b m).sum = m * b := by
  induction m using Nat.strong_induction_on generalizing b with
  | _ m ih =>
  match m with
  | 0 => simp
  | m + 1 =>
    rw [glaisherBwdStep_eq b (Nat.succ_ne_zero m)]
    by_cases h_odd : (m + 1) % 2 = 1
    · simp only [h_odd, ↓reduceIte, Multiset.sum_add, Multiset.sum_singleton]
      rw [ih ((m + 1) / 2) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num)) (2 * b)]
      have hdiv : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
      nlinarith
    · simp only [h_odd, ↓reduceIte, zero_add]
      rw [ih ((m + 1) / 2) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num)) (2 * b)]
      have hdiv : m + 1 = 2 * ((m + 1) / 2) := by omega
      nlinarith

/-! ## Odd Part Property -/

/-- Ground fact: padicValNat 2 2 = 1 (the 2-adic valuation of 2 is 1). -/
private lemma padicValNat_two_two : padicValNat 2 2 = 1 := by native_decide

/-- padicValNat 2 (2^n) = n for all n. -/
private lemma padicValNat_two_pow (n : ℕ) : padicValNat 2 (2 ^ n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValNat.mul (pow_ne_zero n two_ne_zero) two_ne_zero, ih,
        padicValNat_two_two]

/-- The odd part of k (k / 2^(padicValNat 2 k)) is not divisible by 2, for k ≠ 0.

    Proof via multiplicativity of padicValNat: if 2 ∣ (k/2^a), then
    padicValNat 2 (k/2^a) ≥ 1, but by multiplicativity padicValNat 2 k =
    padicValNat 2 (2^a) + padicValNat 2 (k/2^a) = a + (≥1) > a = padicValNat 2 k. -/
private lemma oddPart_odd {k : ℕ} (hk : k ≠ 0) : ¬ 2 ∣ (k / 2 ^ padicValNat 2 k) := by
  set a := padicValNat 2 k with ha_def
  set m := k / 2 ^ a with hm_def
  have hm_ne : m ≠ 0 := by
    intro heq
    -- padic_factorization : 2^a * m = k (after set substitution, explicit annotation needed)
    have hdec : 2 ^ a * m = k := padic_factorization
    rw [heq, Nat.mul_zero] at hdec
    exact hk hdec.symm
  -- Show padicValNat 2 m = 0 via multiplicativity
  have h_padic_m : padicValNat 2 m = 0 := by
    have hdec : 2 ^ a * m = k := padic_factorization  -- 2^a * m = k
    have h_split : a + padicValNat 2 m = a := by
      calc a + padicValNat 2 m
          = padicValNat 2 (2 ^ a) + padicValNat 2 m := by rw [padicValNat_two_pow]
        _ = padicValNat 2 (2 ^ a * m) := (padicValNat.mul (pow_ne_zero a two_ne_zero) hm_ne).symm
        _ = padicValNat 2 k := by rw [hdec]
        _ = a := rfl
    omega
  -- From padicValNat 2 m = 0: derive contradiction if 2 ∣ m
  intro h_dvd
  obtain ⟨m', hm'⟩ := h_dvd
  have hm'_ne : m' ≠ 0 := by omega
  -- If m = 2 * m', then padicValNat 2 m ≥ 1
  have h_padic_pos : padicValNat 2 m ≥ 1 := by
    rw [hm', padicValNat.mul two_ne_zero hm'_ne, padicValNat_two_two]
    omega
  omega

/-- Every element of glaisherFwdPart k is odd. -/
theorem glaisherFwdPart_parts_odd {k : ℕ} (hk : k ≠ 0) :
    ∀ x ∈ glaisherFwdPart k, ¬ Even x := by
  intro x hx
  simp only [glaisherFwdPart, Multiset.mem_replicate] at hx
  obtain ⟨_, rfl⟩ := hx
  intro ⟨c, hc⟩
  -- hc : k / 2^a = c + c; need to derive 2 ∣ (k / 2^a)
  exact oddPart_odd hk ⟨c, by linarith⟩

/-- The forward map produces only odd parts. -/
theorem glaisherFwd_parts_odd {s : Multiset ℕ} (hs : ∀ k ∈ s, k ≠ 0) :
    ∀ x ∈ glaisherFwd s, ¬ Even x := by
  intro x hx
  simp only [glaisherFwd, Multiset.mem_bind] at hx
  obtain ⟨k, hk_in, hx_in⟩ := hx
  exact glaisherFwdPart_parts_odd (hs k hk_in) x hx_in

/-! ## Concrete Examples -/

/-- Example: {6, 5, 3} (distinct, sums to 14) maps to {3, 3, 5, 3} (odd, sums to 14) -/
example : glaisherFwd {6, 5, 3} = {3, 3, 5, 3} := by native_decide

/-- Backward step: odd 3 appearing 3 times → {6, 3} (distinct parts of 9) -/
example : glaisherBwdStep 3 3 = {6, 3} := by native_decide

/-- Sum check: 3 copies of 3 → parts summing to 9 -/
example : (glaisherBwdStep 3 3).sum = 9 := by native_decide

/-! ## Key Inverse Lemma -/

/-- Backward step on 2^a copies of b yields the singleton {2^a * b}.

    This is the core inverse: the Glaisher map sends k = 2^a * b to 2^a copies of b,
    and the backward step recovers k from those copies. -/
theorem glaisherBwdStep_pow_two (a b : ℕ) :
    glaisherBwdStep b (2 ^ a) = {2 ^ a * b} := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [glaisherBwdStep_eq b one_ne_zero]
    norm_num
  | succ a ih =>
    rw [pow_succ]
    have h_ne : 2 ^ a * 2 ≠ 0 := by positivity
    rw [glaisherBwdStep_eq b h_ne]
    rw [if_neg (by omega : 2 ^ a * 2 % 2 ≠ 1)]
    simp only [zero_add]
    rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    rw [ih (2 * b)]
    congr 1; ring

/-! ## Carry-Free Sums of Powers of Two -/

/-- Sum of first n powers of 2 equals 2^n - 1. -/
private lemma sum_range_two_pow (n : ℕ) : (Finset.range n).sum (2 ^ ·) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- For a Finset A of naturals all < n, the sum of 2^a for a ∈ A is < 2^n. -/
private lemma sum_two_pow_lt {A : Finset ℕ} {n : ℕ} (hA : ∀ a ∈ A, a < n) :
    A.sum (2 ^ ·) < 2 ^ n := by
  calc A.sum (2 ^ ·)
      ≤ (Finset.range n).sum (2 ^ ·) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp [Finset.mem_range, hA x hx]
        · intros; exact Nat.zero_le _
    _ = 2 ^ n - 1 := sum_range_two_pow n
    _ < 2 ^ n := Nat.sub_lt (Nat.two_pow_pos n) one_pos

/-- When S < 2^i, adding 2^i equals bitwise OR with 2^i (no carry). -/
private lemma two_pow_add_eq_lor {S i : ℕ} (hS : S < 2 ^ i) : 2 ^ i + S = 2 ^ i ||| S := by
  have h := Nat.two_pow_add_eq_or_of_lt (i := i) (b_lt := hS) (a := 1)
  simpa [mul_one] using h

/-- For a Finset A of distinct naturals, (∑ 2^a).testBit j = decide (j ∈ A). -/
private lemma testBit_sum_distinct_pow (A : Finset ℕ) (j : ℕ) :
    (A.sum (2 ^ ·)).testBit j = decide (j ∈ A) := by
  -- Prove by induction on the cardinality of A
  have key : ∀ (n : ℕ) (B : Finset ℕ), B.card = n →
      (B.sum (2 ^ ·)).testBit j = decide (j ∈ B) := by
    intro n
    induction n with
    | zero =>
      intro B hB
      simp [Finset.card_eq_zero.mp hB]
    | succ n ih =>
      intro B hB
      have hne : B.Nonempty := Finset.card_pos.mp (hB ▸ Nat.succ_pos n)
      let m := B.max' hne
      have hm_in : m ∈ B := Finset.max'_mem B hne
      let B' := B.erase m
      have hm_not : m ∉ B' := Finset.not_mem_erase m B
      have hB'_card : B'.card = n := by
        rw [Finset.card_erase_of_mem hm_in, hB]; simp
      have hB'_lt : ∀ a ∈ B', a < m := by
        intro a ha
        have hmem := Finset.mem_erase.mp ha
        exact Nat.lt_of_le_of_ne (Finset.le_max' B a hmem.2) hmem.1
      have hlt : B'.sum (2 ^ ·) < 2 ^ m := sum_two_pow_lt hB'_lt
      have hsum : B.sum (2 ^ ·) = 2 ^ m + B'.sum (2 ^ ·) := by
        rw [show B = insert m B' from (Finset.insert_erase hm_in).symm,
            Finset.sum_insert hm_not]
      rw [hsum, two_pow_add_eq_lor hlt, Nat.testBit_or, Nat.testBit_two_pow, ih B' hB'_card]
      -- Goal: decide (m = j) || decide (j ∈ B') = decide (j ∈ B)
      simp only [show B = insert m B' from (Finset.insert_erase hm_in).symm, Finset.mem_insert]
      -- Goal: decide (m = j) || decide (j ∈ B') = decide (j = m ∨ j ∈ B')
      rcases eq_or_ne j m with rfl | hj
      · simp
      · simp [hj, ne_comm.mp hj]
  exact key A.card A rfl

/-! ## Count Characterization of glaisherBwdStep -/

/-- All elements of glaisherBwdStep b M are ≥ b when b > 0. -/
private lemma glaisherBwdStep_ge_base {b : ℕ} (hb : 0 < b) (M : ℕ) :
    ∀ x ∈ glaisherBwdStep b M, b ≤ x := by
  induction M using Nat.strong_induction_on generalizing b with
  | _ M ih =>
  intro x hx
  match M with
  | 0 => simp at hx
  | M + 1 =>
    rw [glaisherBwdStep_eq b (Nat.succ_ne_zero M)] at hx
    simp only [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · split_ifs at hx with h
      · simp only [Multiset.mem_singleton] at hx; exact hx ▸ le_refl b
      · simp at hx
    · have h2b : 0 < 2 * b := Nat.mul_pos (by norm_num) hb
      linarith [ih ((M + 1) / 2) (Nat.div_lt_self (Nat.succ_pos M) (by norm_num)) h2b x hx]

/-- count (2^a * b) (glaisherBwdStep b M) = 1 if M.testBit a = true, else 0. -/
private lemma glaisherBwdStep_count_pow {b : ℕ} (hb : 0 < b) (a M : ℕ) :
    (glaisherBwdStep b M).count (2 ^ a * b) = if M.testBit a then 1 else 0 := by
  induction M using Nat.strong_induction_on generalizing b a with
  | _ M ih =>
  match M with
  | 0 => simp
  | M + 1 =>
    rw [glaisherBwdStep_eq b (Nat.succ_ne_zero M), Multiset.count_add]
    match a with
    | 0 =>
      simp only [pow_zero, one_mul]
      have h0 : (glaisherBwdStep (2 * b) ((M + 1) / 2)).count b = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hb_in
        have := glaisherBwdStep_ge_base (Nat.mul_pos (by norm_num) hb) ((M + 1) / 2) b hb_in
        linarith
      rw [h0, add_zero, Nat.testBit_zero]
      by_cases h : (M + 1) % 2 = 1 <;> simp [h]
    | a + 1 =>
      have h2b : 0 < 2 * b := Nat.mul_pos (by norm_num) hb
      have hrw : 2 ^ (a + 1) * b = 2 ^ a * (2 * b) := by ring
      rw [hrw]
      have h_ne : 2 ^ a * (2 * b) ≠ b := by
        have hge : 2 ^ a * (2 * b) ≥ 2 * b := by
          nlinarith [Nat.one_le_two_pow (n := a)]
        linarith
      have h_ite_zero : ((if (M + 1) % 2 = 1 then ({b} : Multiset ℕ) else 0)).count
          (2 ^ a * (2 * b)) = 0 := by
        split_ifs with h <;> simp [h_ne]
      rw [h_ite_zero, zero_add,
          ih ((M + 1) / 2) (Nat.div_lt_self (Nat.succ_pos M) (by norm_num)) h2b a]
      simp [Nat.testBit_succ]

/-! ## Bijectivity -/

/-- Backward undoes forward for a single distinct part k.

    Proof: glaisherFwdPart k = replicate (2^a) b where a = padicValNat 2 k and b = k/2^a.
    Then toFinset = {b}, count b = 2^a, and glaisherBwdStep b (2^a) = {2^a * b} = {k}. -/
theorem glaisherBwd_glaisherFwdPart {k : ℕ} (hk : k ≠ 0) :
    glaisherBwd (glaisherFwdPart k) = {k} := by
  set a := padicValNat 2 k
  set b := k / 2 ^ a
  have ha_pos : 0 < 2 ^ a := by positivity
  -- Step 1: toFinset of replicate (2^a) b = {b} (since 2^a ≥ 1)
  have h_toFinset : (glaisherFwdPart k).toFinset = {b} := by
    ext x
    simp only [glaisherFwdPart, Multiset.mem_toFinset, Multiset.mem_replicate,
               Finset.mem_singleton]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨ha_pos.ne', hx⟩⟩
  -- Step 2: count b in replicate (2^a) b = 2^a
  have h_count : (glaisherFwdPart k).count b = 2 ^ a := by
    show (Multiset.replicate (2 ^ a) b).count b = 2 ^ a
    simp [Multiset.count_replicate]
  -- Step 3: unfold glaisherBwd, reduce singleton multiset bind, finish
  -- {b}.bind f = (b ::ₘ 0).bind f = f b + 0.bind f = f b  (by Multiset.cons_bind, zero_bind)
  simp only [glaisherBwd, h_toFinset, Finset.singleton_val,
             show ({b} : Multiset ℕ) = b ::ₘ 0 from rfl,
             Multiset.cons_bind, Multiset.zero_bind, add_zero]
  rw [h_count, glaisherBwdStep_pow_two,
      show 2 ^ a * b = k from padic_factorization]

/-- The maps are inverses on distinct positive multisets.

    Proof via count characterization: for each k ≠ 0 with oddPart b = k/2^a, a = padicValNat 2 k:

    count k (glaisherBwd (glaisherFwd s))
    = (glaisherBwdStep b ((glaisherFwd s).count b)).count k
      [only b' = b contributes since 2^a*b = k uniquely determines b from k's 2-adic factorization]
    = if ((glaisherFwd s).count b).testBit a then 1 else 0
      [by glaisherBwdStep_count_pow]

    (glaisherFwd s).count b = Σ_{k' ∈ s, oddPart k' = b} 2^(padicValNat 2 k')
      [by Multiset.count_bind and glaisherFwdPart definition]

    For nodup s: these are distinct powers of 2 (different k' with same b have different valuations).
    By testBit_sum_distinct_pow: testBit of that sum at a = decide(2^a ∈ the set) = decide(k ∈ s).

    Infrastructure proved: glaisherBwdStep_count_pow, testBit_sum_distinct_pow.
    Remaining step: connect (glaisherFwd s).count b to a sum of distinct powers of 2. -/
theorem glaisherBwd_glaisherFwd {s : Multiset ℕ}
    (hs_pos : ∀ k ∈ s, k ≠ 0) (hs_nodup : s.Nodup) :
    glaisherBwd (glaisherFwd s) = s := by
  sorry

/-- **Constructive Euler Partition Theorem**: Glaisher gives an explicit bijection
    between distinct-part and odd-part partitions of any n.

    This follows from `glaisherBwd_glaisherFwd` (injection) plus the surjectivity direction
    `glaisherFwd_glaisherBwd` (not yet proved). The multiset-level inverse pair
    (glaisherBwd ∘ glaisherFwd = id on distinct multisets, and the converse on odd multisets)
    lifts to a bijection on Nat.Partition types via the parts Multiset representation.

    Note: `Archive.Wiedijk100Theorems.Partition` (which provides `Theorems100.partition_theorem`)
    is not available in the cached Mathlib v4.26.0 build. The equal-cardinality proof path
    requires that import, so we leave this theorem as a sorry pending either:
    (a) building Archive locally, or (b) completing the constructive proof via the two-sided
    inverse pair. -/
theorem glaisher_bijection_exists (n : ℕ) :
    ∃ (f : {p : Nat.Partition n // p ∈ Nat.Partition.distincts n} →
           {p : Nat.Partition n // p ∈ Nat.Partition.odds n}),
      Function.Bijective f := by
  sorry

end GlaisherBijection
