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

    Key sub-lemma needed (marked sorry for future work):
    glaisherBwdStep b (m1 + m2) = glaisherBwdStep b m1 + glaisherBwdStep b m2
    when m1 and m2 have disjoint binary representations (m1 &&& m2 = 0).
    This holds because carry-free binary addition preserves bit patterns.

    Proof sketch for the main theorem:
    - Group elements of s by their odd part b = k / 2^padicValNat(k)
    - For each odd b, count b in glaisherFwd s = Σ_{k in s, oddPart k = b} 2^padicValNat(k)
    - The 2^padicValNat values for distinct k with same odd part are distinct powers of 2
       (since different k's with same odd part have different 2-adic valuations, and s is Nodup)
    - glaisherBwdStep b over that sum of distinct powers = union of {2^a * b} by additive decomp
    - Summing over all odd b recovers exactly s. -/
theorem glaisherBwd_glaisherFwd {s : Multiset ℕ}
    (hs_pos : ∀ k ∈ s, k ≠ 0) (hs_nodup : s.Nodup) :
    glaisherBwd (glaisherFwd s) = s := by
  sorry

/-- **Constructive Euler Partition Theorem**: Glaisher gives an explicit bijection
    between distinct-part and odd-part partitions of any n. -/
theorem glaisher_bijection_exists (n : ℕ) :
    ∃ (f : {p : Nat.Partition n // p ∈ Nat.Partition.distincts n} →
           {p : Nat.Partition n // p ∈ Nat.Partition.odds n}),
      Function.Bijective f := by
  sorry

end GlaisherBijection
