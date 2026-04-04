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

/-- Key sub-lemma: if the a-th bit of m is 0, then adding 2^a to m gives {2^a * b} in the backward step.
    Condition: (m / 2^a) % 2 = 0 means "bit a of m is zero" (carry-free addition at position a). -/
private lemma glaisherBwdStep_add_pow_two : ∀ (a b m : ℕ),
    (m / 2^a) % 2 = 0 →
    glaisherBwdStep b (2^a + m) = {2^a * b} + glaisherBwdStep b m := by
  intro a
  induction a with
  | zero =>
    intro b m h
    simp only [pow_zero, Nat.div_one] at h
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    subst hk
    simp only [pow_zero, one_mul]
    rw [glaisherBwdStep_eq b (by omega : 1 + 2 * k ≠ 0)]
    simp only [if_pos (show (1 + 2 * k) % 2 = 1 from by omega)]
    rw [show (1 + 2 * k) / 2 = k from by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [glaisherBwdStep]
    · rw [glaisherBwdStep_eq b (by omega : 2 * k ≠ 0)]
      simp only [if_neg (show 2 * k % 2 ≠ 1 from by omega), zero_add]
      rw [show 2 * k / 2 = k from by omega]
  | succ a ih =>
    intro b m h
    have h_shifted : (m / 2 / 2^a) % 2 = 0 := by
      rwa [Nat.div_div_eq_div_mul, show 2 * 2^a = 2^(a+1) from by ring]
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- Even case: hk : m = k + k; we need m = 2 * k for the rewrites
      have hk2 : m = 2 * k := by omega
      subst hk2
      rw [glaisherBwdStep_eq b (by positivity : 2^(a+1) + 2*k ≠ 0)]
      rw [if_neg (show (2^(a+1) + 2*k) % 2 ≠ 1 from by rw [pow_succ]; omega)]
      simp only [zero_add]
      rw [show (2^(a+1) + 2*k) / 2 = 2^a + k from by rw [pow_succ]; omega]
      have hk_bit : (k / 2^a) % 2 = 0 := by
        have heq : 2 * k / 2 = k := by omega
        rw [heq] at h_shifted; exact h_shifted
      rw [ih (2*b) k hk_bit]
      -- Goal: {2^a * (2*b)} + glaisherBwdStep (2*b) k = {2^(a+1) * b} + glaisherBwdStep b (2*k)
      have step_double : glaisherBwdStep b (2*k) = glaisherBwdStep (2*b) k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · simp [glaisherBwdStep]
        · rw [glaisherBwdStep_eq b (by omega : 2*k ≠ 0)]
          rw [if_neg (show 2*k % 2 ≠ 1 from by omega)]
          simp only [zero_add]
          rw [show 2*k/2 = k from by omega]
      rw [step_double]
      congr 1; ring
    · -- Odd case: hk : m = 2 * k + 1
      subst hk
      rw [glaisherBwdStep_eq b (by positivity : 2^(a+1) + (2*k+1) ≠ 0)]
      rw [if_pos (show (2^(a+1) + (2*k+1)) % 2 = 1 from by rw [pow_succ]; omega)]
      rw [show (2^(a+1) + (2*k+1)) / 2 = 2^a + k from by rw [pow_succ]; omega]
      have hk_bit : (k / 2^a) % 2 = 0 := by
        have heq : (2*k+1) / 2 = k := by omega
        rw [heq] at h_shifted; exact h_shifted
      rw [ih (2*b) k hk_bit]
      rw [glaisherBwdStep_eq b (by omega : 2*k+1 ≠ 0)]
      rw [if_pos (show (2*k+1) % 2 = 1 from by omega)]
      rw [show (2*k+1)/2 = k from by omega]
      rw [show 2^(a+1) * b = 2^a * (2*b) from by ring]
      exact add_left_comm _ _ _

/-- Adding 2^a copies of b shifts the backward map by {2^a*b}. -/
private lemma glaisherBwd_add_replicate {a b : ℕ}
    {t : Multiset ℕ} (h_bit : (t.count b / 2^a) % 2 = 0) :
    glaisherBwd (Multiset.replicate (2^a) b + t) = {2^a * b} + glaisherBwd t := by
  have ha_pos : 0 < 2^a := by positivity
  simp only [glaisherBwd]
  have h_toFinset : (Multiset.replicate (2^a) b + t).toFinset = insert b t.toFinset := by
    ext x
    simp only [Multiset.mem_toFinset, Multiset.mem_add, Multiset.mem_replicate,
               Finset.mem_insert, Multiset.mem_toFinset]
    exact ⟨fun h => h.elim (fun ⟨_, rfl⟩ => Or.inl rfl) Or.inr,
           fun h => h.elim (fun rfl => Or.inl ⟨ha_pos.ne', rfl⟩) Or.inr⟩
  have h_count_b : (Multiset.replicate (2^a) b + t).count b = 2^a + t.count b := by
    simp [Multiset.count_add, Multiset.count_replicate]
  have h_count_ne : ∀ v, v ≠ b → (Multiset.replicate (2^a) b + t).count v = t.count v := by
    intro v hv
    have h_not_mem : v ∉ Multiset.replicate (2^a) b :=
      fun h => hv ((Multiset.mem_replicate.mp h).2)
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr h_not_mem, zero_add]
  rw [h_toFinset, Finset.insert_val]
  by_cases hb : b ∈ t.toFinset
  · -- b ∈ t.toFinset; decompose via cons_erase
    have hb_val : b ∈ t.toFinset.val := hb
    set vals := t.toFinset.val.erase b with hvals_def
    have h_cons : t.toFinset.val = b ::ₘ vals := (Multiset.cons_erase hb_val).symm
    have hb_not_vals : b ∉ vals := by
      have hnd := t.toFinset.nodup; rw [h_cons] at hnd
      exact (Multiset.nodup_cons.mp hnd).1
    rw [Multiset.ndinsert_of_mem hb_val, h_cons,
        Multiset.cons_bind, Multiset.cons_bind, h_count_b,
        glaisherBwdStep_add_pow_two a b (t.count b) h_bit]
    have h_rest_eq : vals.bind (fun v => glaisherBwdStep v ((Multiset.replicate (2^a) b + t).count v)) =
        vals.bind (fun v => glaisherBwdStep v (t.count v)) :=
      Multiset.bind_congr fun v hv => congrArg _ (h_count_ne v (fun h => hb_not_vals (h ▸ hv)))
    rw [h_rest_eq]; exact add_assoc _ _ _
  · have hb_not_val : b ∉ t.toFinset.val := hb
    have hb_count : t.count b = 0 :=
      Multiset.count_eq_zero.mpr (fun h => hb (Multiset.mem_toFinset.mpr h))
    rw [Multiset.ndinsert_of_not_mem hb_not_val, Multiset.cons_bind, h_count_b,
        glaisherBwdStep_add_pow_two a b (t.count b) h_bit, hb_count,
        glaisherBwdStep_zero, add_zero]
    congr 1
    exact Multiset.bind_congr fun v hv =>
      congrArg _ (h_count_ne v (fun h => hb_not_val (h ▸ hv)))

/-- Bit a of (glaisherFwd t).count b is 0 when 2^a*b ∉ t (Nodup t). -/
private lemma glaisherFwd_count_bit_zero {k : ℕ} (hk : k ≠ 0) {t : Multiset ℕ}
    (ht_pos : ∀ x ∈ t, x ≠ 0) (ht_nodup : t.Nodup) (hk_not_in : k ∉ t) :
    ((glaisherFwd t).count (k / 2^(padicValNat 2 k)) / 2^(padicValNat 2 k)) % 2 = 0 := by
  sorry

/-- **Round-trip**: backward undoes forward on Nodup multisets of positive naturals. -/
theorem glaisherBwd_glaisherFwd {s : Multiset ℕ}
    (hs_pos : ∀ k ∈ s, k ≠ 0) (hs_nodup : s.Nodup) :
    glaisherBwd (glaisherFwd s) = s := by
  induction s using Multiset.induction with
  | empty => simp [glaisherFwd, glaisherBwd]
  | cons k t ih =>
    rw [Multiset.nodup_cons] at hs_nodup
    obtain ⟨hk_not_in, ht_nodup⟩ := hs_nodup
    have ht_pos : ∀ x ∈ t, x ≠ 0 := fun x hx => hs_pos x (Multiset.mem_cons_of_mem hx)
    have hk_pos : k ≠ 0 := hs_pos k (Multiset.mem_cons_self k t)
    have h_fwd : glaisherFwd (k ::ₘ t) = glaisherFwdPart k + glaisherFwd t := by
      simp [glaisherFwd, Multiset.cons_bind]
    set a := padicValNat 2 k
    set b := k / 2 ^ a with hb_def
    rw [h_fwd, show glaisherFwdPart k = Multiset.replicate (2^a) b from rfl,
        glaisherBwd_add_replicate (glaisherFwd_count_bit_zero hk_pos ht_pos ht_nodup hk_not_in),
        show 2^a * b = k from padic_factorization, ih ht_pos ht_nodup]
    change (k ::ₘ (0 : Multiset ℕ)) + t = k ::ₘ t
    rw [Multiset.cons_add, zero_add]

/-- **Constructive Euler Partition Theorem**: Glaisher gives an explicit bijection
    between distinct-part and odd-part partitions of any n. -/
theorem glaisher_bijection_exists (n : ℕ) :
    ∃ (f : {p : Nat.Partition n // p ∈ Nat.Partition.distincts n} →
           {p : Nat.Partition n // p ∈ Nat.Partition.odds n}),
      Function.Bijective f := by
  sorry

end GlaisherBijection
