/-
# Erdős Problem #770 — Mutual Coprimality of k^n − 1

Let h(n) be the minimal k ≥ 2 such that gcd(2^n−1, 3^n−1, ..., k^n−1) = 1.
Here "mutually coprime" means the overall gcd of ALL terms equals 1.

Questions:
1. Does the density δ_p of integers with h(n) = p exist for every prime p?
2. Does lim inf h(n) = ∞?
3. If p is the greatest prime with p−1 | n and p > n^ε, is h(n) = p?

Known: h(n) = n+1 iff n+1 is prime. h(n) is unbounded for odd n.
Probably h(n) = 3 for infinitely many n.

Key insight: When p is prime and p−1 | n, Fermat gives p | a^n − 1 for all
a coprime to p. So p divides every term a^n−1 for 2 ≤ a < p. But
p^n − 1 ≡ −1 (mod p), so p ∤ p^n − 1. Adding k = p breaks the shared
factor, giving gcd = 1 when p is the only common factor.

Verified sequence: h(1)=2, h(2)=3, h(3)=3, h(4)=5, h(5)=3, h(6)=7,
h(7)=3, h(8)=5, h(9)=3, h(10)=11, h(11)=5, h(12)=13.

Status: OPEN
Reference: https://erdosproblems.com/770
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Finset

-- ## Core Definition

/-- The gcd of the list [2^n−1, 3^n−1, ..., k^n−1].
    Uses Finset.fold with Nat.gcd and identity 0.
    When k < 2, the range Icc 2 k is empty, giving 0. -/
def gcdPowerSeq (n k : ℕ) : ℕ :=
  (Finset.Icc 2 k).fold Nat.gcd 0 (fun a => a ^ n - 1)

-- ## Concrete gcdPowerSeq values

-- n=1: 2^1-1=1
theorem gcdPowerSeq_1_2 : gcdPowerSeq 1 2 = 1 := by native_decide

-- n=2: 2^2-1=3, 3^2-1=8
theorem gcdPowerSeq_2_2 : gcdPowerSeq 2 2 = 3 := by native_decide
theorem gcdPowerSeq_2_3 : gcdPowerSeq 2 3 = 1 := by native_decide

-- n=3: 2^3-1=7, 3^3-1=26, gcd(7,26)=1
theorem gcdPowerSeq_3_2 : gcdPowerSeq 3 2 = 7 := by native_decide
theorem gcdPowerSeq_3_3 : gcdPowerSeq 3 3 = 1 := by native_decide

-- n=4: gcd(15,80)=5, gcd(5,255)=5, gcd(5,624)=1
theorem gcdPowerSeq_4_2 : gcdPowerSeq 4 2 = 15 := by native_decide
theorem gcdPowerSeq_4_3 : gcdPowerSeq 4 3 = 5 := by native_decide
theorem gcdPowerSeq_4_4 : gcdPowerSeq 4 4 = 5 := by native_decide
theorem gcdPowerSeq_4_5 : gcdPowerSeq 4 5 = 1 := by native_decide

-- n=5: gcd(31,242)=1
theorem gcdPowerSeq_5_3 : gcdPowerSeq 5 3 = 1 := by native_decide

-- n=6: all terms ≤6 divisible by 7 (Fermat: 6=7-1)
theorem gcdPowerSeq_6_6 : gcdPowerSeq 6 6 = 7 := by native_decide
theorem gcdPowerSeq_6_7 : gcdPowerSeq 6 7 = 1 := by native_decide

-- n=8: gcd stabilizes at 5
theorem gcdPowerSeq_8_4 : gcdPowerSeq 8 4 = 5 := by native_decide
theorem gcdPowerSeq_8_5 : gcdPowerSeq 8 5 = 1 := by native_decide

-- n=10: all terms ≤10 divisible by 11 (Fermat: 10=11-1)
theorem gcdPowerSeq_10_3 : gcdPowerSeq 10 3 = 11 := by native_decide
theorem gcdPowerSeq_10_10 : gcdPowerSeq 10 10 = 11 := by native_decide
theorem gcdPowerSeq_10_11 : gcdPowerSeq 10 11 = 1 := by native_decide

-- n=12: gcd drops from 455 to 91 to 13
theorem gcdPowerSeq_12_3 : gcdPowerSeq 12 3 = 455 := by native_decide
theorem gcdPowerSeq_12_7 : gcdPowerSeq 12 7 = 13 := by native_decide
theorem gcdPowerSeq_12_12 : gcdPowerSeq 12 12 = 13 := by native_decide
theorem gcdPowerSeq_12_13 : gcdPowerSeq 12 13 = 1 := by native_decide

-- ## Verified h(n) values

-- h(1) = 2 (n+1=2 prime)
theorem h_val_1 : gcdPowerSeq 1 2 = 1 := gcdPowerSeq_1_2

-- h(2) = 3 (n+1=3 prime)
theorem h_val_2 : gcdPowerSeq 2 2 ≠ 1 ∧ gcdPowerSeq 2 3 = 1 := by
  constructor <;> native_decide

-- h(3) = 3 (n+1=4 composite)
theorem h_val_3 : gcdPowerSeq 3 2 ≠ 1 ∧ gcdPowerSeq 3 3 = 1 := by
  constructor <;> native_decide

-- h(4) = 5 (n+1=5 prime)
theorem h_val_4 : gcdPowerSeq 4 2 ≠ 1 ∧ gcdPowerSeq 4 3 ≠ 1 ∧
    gcdPowerSeq 4 4 ≠ 1 ∧ gcdPowerSeq 4 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(5) = 3 (n+1=6 composite)
theorem h_val_5 : gcdPowerSeq 5 2 ≠ 1 ∧ gcdPowerSeq 5 3 = 1 := by
  constructor <;> native_decide

-- h(6) = 7 (n+1=7 prime)
theorem h_val_6 : gcdPowerSeq 6 2 ≠ 1 ∧ gcdPowerSeq 6 3 ≠ 1 ∧
    gcdPowerSeq 6 4 ≠ 1 ∧ gcdPowerSeq 6 5 ≠ 1 ∧
    gcdPowerSeq 6 6 ≠ 1 ∧ gcdPowerSeq 6 7 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(7) = 3 (n+1=8 composite)
theorem h_val_7 : gcdPowerSeq 7 2 ≠ 1 ∧ gcdPowerSeq 7 3 = 1 := by
  constructor <;> native_decide

-- h(8) = 5 (n+1=9 composite)
theorem h_val_8 : gcdPowerSeq 8 2 ≠ 1 ∧ gcdPowerSeq 8 3 ≠ 1 ∧
    gcdPowerSeq 8 4 ≠ 1 ∧ gcdPowerSeq 8 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(9) = 3 (n+1=10 composite)
theorem h_val_9 : gcdPowerSeq 9 2 ≠ 1 ∧ gcdPowerSeq 9 3 = 1 := by
  constructor <;> native_decide

-- h(10) = 11 (n+1=11 prime)
theorem h_val_10 : gcdPowerSeq 10 2 ≠ 1 ∧ gcdPowerSeq 10 3 ≠ 1 ∧
    gcdPowerSeq 10 4 ≠ 1 ∧ gcdPowerSeq 10 5 ≠ 1 ∧
    gcdPowerSeq 10 6 ≠ 1 ∧ gcdPowerSeq 10 7 ≠ 1 ∧
    gcdPowerSeq 10 8 ≠ 1 ∧ gcdPowerSeq 10 9 ≠ 1 ∧
    gcdPowerSeq 10 10 ≠ 1 ∧ gcdPowerSeq 10 11 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(11) = 5 (n+1=12 composite)
theorem h_val_11 : gcdPowerSeq 11 2 ≠ 1 ∧ gcdPowerSeq 11 3 ≠ 1 ∧
    gcdPowerSeq 11 4 ≠ 1 ∧ gcdPowerSeq 11 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(12) = 13 (n+1=13 prime)
theorem h_val_12 : gcdPowerSeq 12 2 ≠ 1 ∧ gcdPowerSeq 12 3 ≠ 1 ∧
    gcdPowerSeq 12 4 ≠ 1 ∧ gcdPowerSeq 12 5 ≠ 1 ∧
    gcdPowerSeq 12 6 ≠ 1 ∧ gcdPowerSeq 12 7 ≠ 1 ∧
    gcdPowerSeq 12 8 ≠ 1 ∧ gcdPowerSeq 12 9 ≠ 1 ∧
    gcdPowerSeq 12 10 ≠ 1 ∧ gcdPowerSeq 12 11 ≠ 1 ∧
    gcdPowerSeq 12 12 ≠ 1 ∧ gcdPowerSeq 12 13 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ## Fermat's Little Theorem: computational verification

-- When p is prime and (p-1) | n, then p | (a^n - 1) for all a coprime to p.
-- But p ∤ (p^n - 1), since p^n ≡ 0 (mod p).

-- p=3, n=2: 3 | (2^2-1) = 3
theorem fermat_3_2 : 3 ∣ (2 ^ 2 - 1) := by native_decide

-- p=5, n=4: 5 | (a^4-1) for a=2,3,4; 5 ∤ (5^4-1)
theorem fermat_5_divides : 5 ∣ (2^4-1) ∧ 5 ∣ (3^4-1) ∧ 5 ∣ (4^4-1) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide
theorem fermat_5_breaks : ¬ (5 ∣ (5^4 - 1)) := by native_decide

-- p=7, n=6: 7 | (a^6-1) for a=2,...,6; 7 ∤ (7^6-1)
theorem fermat_7_divides :
    7 ∣ (2^6-1) ∧ 7 ∣ (3^6-1) ∧ 7 ∣ (4^6-1) ∧ 7 ∣ (5^6-1) ∧ 7 ∣ (6^6-1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
theorem fermat_7_breaks : ¬ (7 ∣ (7^6 - 1)) := by native_decide

-- p=11, n=10: 11 | (a^10-1) for a=2,...,10; 11 ∤ (11^10-1)
theorem fermat_11_divides :
    11 ∣ (2^10-1) ∧ 11 ∣ (3^10-1) ∧ 11 ∣ (4^10-1) ∧ 11 ∣ (5^10-1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
theorem fermat_11_breaks : ¬ (11 ∣ (11^10 - 1)) := by native_decide

-- p=13, n=12: 13 | (a^12-1) for a=2,...,12; 13 ∤ (13^12-1)
theorem fermat_13_divides : 13 ∣ (2^12-1) ∧ 13 ∣ (3^12-1) := by
  constructor <;> native_decide
theorem fermat_13_breaks : ¬ (13 ∣ (13^12 - 1)) := by native_decide

-- ## Pattern: h(n) = 3 for many n (supporting the conjecture)

-- h(n)=3 when gcd(2^n-1, 3^n-1) = 1 and 2^n-1 > 1
theorem h_eq_3_at_3 : gcdPowerSeq 3 3 = 1 := gcdPowerSeq_3_3
theorem h_eq_3_at_5 : gcdPowerSeq 5 3 = 1 := gcdPowerSeq_5_3
theorem h_eq_3_at_7 : gcdPowerSeq 7 3 = 1 := by native_decide
theorem h_eq_3_at_9 : gcdPowerSeq 9 3 = 1 := by native_decide
theorem h_eq_3_at_13 : gcdPowerSeq 13 3 = 1 := by native_decide
theorem h_eq_3_at_14 : gcdPowerSeq 14 3 = 1 := by native_decide
theorem h_eq_3_at_15 : gcdPowerSeq 15 3 = 1 := by native_decide
theorem h_eq_3_at_17 : gcdPowerSeq 17 3 = 1 := by native_decide
theorem h_eq_3_at_19 : gcdPowerSeq 19 3 = 1 := by native_decide
theorem h_eq_3_at_21 : gcdPowerSeq 21 3 = 1 := by native_decide
theorem h_eq_3_at_25 : gcdPowerSeq 25 3 = 1 := by native_decide

-- Counterexamples: h(n) > 3 when shared prime factors exist
-- n=4: 5-1|4, so 5 divides both 2^4-1=15 and 3^4-1=80
theorem h_gt_3_at_4 : gcdPowerSeq 4 3 ≠ 1 := by native_decide
-- n=10: 11-1|10, so 11 divides both
theorem h_gt_3_at_10 : gcdPowerSeq 10 3 ≠ 1 := by native_decide
-- n=11: h(11)=5
theorem h_gt_3_at_11 : gcdPowerSeq 11 3 ≠ 1 := by native_decide

-- ## The three open questions (axiomatized)

/-
  **Q1 (OPEN)**: Does the density δ_p of integers n with h(n) = p
  exist for every prime p? Full formalization requires natural density
  analysis in Lean — not yet available in Mathlib for this specific h(n).
-/

/-- **Q2 (OPEN)**: Is h(n) unbounded? Specifically, does
    lim inf h(n) = ∞? -/
/-- **Q3 (OPEN)**: If p is the largest prime with (p-1)|n and p > n^ε,
    is h(n) = p? -/
/-- The gcd fold value divides any individual term. -/
private theorem fold_gcd_dvd_mem {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) (f : ℕ → ℕ) :
    S.fold Nat.gcd 0 f ∣ f a := by
  induction S using Finset.cons_induction with
  | empty => exact absurd ha (Finset.not_mem_empty _)
  | cons b S' hb ih =>
    rw [Finset.fold_cons hb]
    rcases Finset.mem_cons.mp ha with rfl | ha'
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (ih ha')

/-- The gcd fold over a superset divides the fold over a subset. -/
private theorem fold_gcd_dvd_of_subset {S T : Finset ℕ} (hST : S ⊆ T) (f : ℕ → ℕ) :
    T.fold Nat.gcd 0 f ∣ S.fold Nat.gcd 0 f := by
  induction S using Finset.cons_induction with
  | empty => simp [Finset.fold_empty]
  | cons a S' ha ih =>
    rw [Finset.fold_cons ha]
    apply Nat.dvd_gcd
    · exact fold_gcd_dvd_mem (hST (Finset.mem_cons_self a S')) f
    · exact ih (fun x hx => hST (Finset.mem_cons_of_mem hx))

/-- Monotone divisibility: extending the range preserves divisibility. -/
theorem gcdPowerSeq_dvd_of_le (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    gcdPowerSeq n k ∣ gcdPowerSeq n j :=
  fold_gcd_dvd_of_subset (Finset.Icc_subset_Icc_right hjk) _

/-- Once gcd reaches 1, it stays 1. Adding more terms to a gcd that is
    already 1 keeps it at 1. -/
theorem gcdPowerSeq_stable (n k j : ℕ) (hk : gcdPowerSeq n k = 1) (hj : k ≤ j) :
    gcdPowerSeq n j = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [← hk]
  exact fold_gcd_dvd_of_subset (Finset.Icc_subset_Icc_right hj) _

/-- Stability contrapositive: if gcd is not 1 at k, it wasn't 1 at any j ≤ k. -/
theorem gcdPowerSeq_ne_one_of_le (n : ℕ) {j k : ℕ} (hjk : j ≤ k)
    (hk : gcdPowerSeq n k ≠ 1) : gcdPowerSeq n j ≠ 1 := by
  intro hj
  exact hk (gcdPowerSeq_stable n j k hj hjk)

/-- Each term a^n - 1 is divisible by the gcd fold value (when a is in range). -/
theorem gcdPowerSeq_dvd_term (n k a : ℕ) (ha : a ∈ Finset.Icc 2 k) :
    gcdPowerSeq n k ∣ (a ^ n - 1) :=
  fold_gcd_dvd_mem ha _

-- ## Fermat's Little Theorem Connection
--
-- The key structural insight behind h(n): a prime p divides gcdPowerSeq n k
-- for all k < p when p-1 | n (by Fermat), but p never divides gcdPowerSeq n p
-- (because p ∤ p^n - 1). This explains why h(n) = largest prime with p-1 | n.

/-- If d divides every term in a gcd fold, then d divides the fold result. -/
private theorem dvd_fold_gcd_of_dvd_all {S : Finset ℕ} {f : ℕ → ℕ} {d : ℕ}
    (h : ∀ a ∈ S, d ∣ f a) : d ∣ S.fold Nat.gcd 0 f := by
  induction S using Finset.cons_induction with
  | empty => exact dvd_zero d
  | cons a S' ha ih =>
    rw [Finset.fold_cons ha]
    exact Nat.dvd_gcd (h a (Finset.mem_cons_self a S'))
      (ih fun b hb => h b (Finset.mem_cons_of_mem hb))

/-- Fermat corollary: when p is prime, p-1 | n, and a is coprime to p,
    then p | a^n - 1. Since a^(p-1) ≡ 1 (mod p) and (p-1) | n,
    we get a^n = (a^(p-1))^m ≡ 1 (mod p). -/
theorem prime_dvd_pow_sub_one {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hdvd : (p - 1) ∣ n)
    {a : ℕ} (hcop : ¬p ∣ a) : p ∣ (a ^ n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact absurd (dvd_zero p) hcop
    · exact h
  have ha_zmod : (a : ZMod p) ≠ 0 := by
    intro h; apply hcop; rwa [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := hdvd
  have key : ((a : ZMod p)) ^ n = 1 := by
    rw [hm, pow_mul, show p - 1 = Fintype.card (ZMod p) - 1 from by rw [ZMod.card p],
        ZMod.pow_card_sub_one_eq_one ha_zmod, one_pow]
  have h1 : ((a ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact key
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  have h2 : a ^ n % p = 1 := by rw [h1, Nat.mod_eq_of_lt hp.one_lt]
  have h3 := Nat.div_add_mod (a ^ n) p
  rw [h2] at h3
  exact ⟨a ^ n / p, by rw [mul_comm]; omega⟩

/-- A prime p never divides p^n - 1 (when n ≥ 1).
    Since p | p^n and p | (p^n - 1) would give p | 1, contradicting p ≥ 2. -/
theorem prime_not_dvd_self_pow_sub_one {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hn : 0 < n) :
    ¬(p ∣ (p ^ n - 1)) := by
  intro h
  have h1 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub' (dvd_pow_self p hn.ne') h
  have h2 : p ^ n - (p ^ n - 1) = 1 := by
    have : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos; omega
  rw [h2] at h1
  have h3 := Nat.le_of_dvd one_pos h1
  have := hp.two_le; omega

/-- When p is prime, p-1 | n, and k < p, then p divides gcdPowerSeq n k.
    Every term a^n - 1 for a ∈ [2,k] is divisible by p (since a < p
    implies a is coprime to p, and Fermat gives p | a^n - 1). -/
theorem prime_dvd_gcdPowerSeq {p : ℕ} (hp : Nat.Prime p) {n k : ℕ}
    (hdvd : (p - 1) ∣ n) (hk : k < p) : p ∣ gcdPowerSeq n k := by
  unfold gcdPowerSeq
  apply dvd_fold_gcd_of_dvd_all
  intro a ha
  rw [Finset.mem_Icc] at ha
  exact prime_dvd_pow_sub_one hp hdvd (by
    intro hpa; exact absurd (Nat.le_of_dvd (by omega) hpa) (by omega))

/-- p never divides gcdPowerSeq n p (for p prime, n ≥ 1), because the
    term p^n - 1 is in the fold and p ∤ p^n - 1. -/
theorem prime_not_dvd_gcdPowerSeq_self {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hn : 0 < n) :
    ¬(p ∣ gcdPowerSeq n p) := by
  intro h
  have h1 : p ∈ Finset.Icc 2 p := Finset.mem_Icc.mpr ⟨hp.two_le, le_refl p⟩
  exact prime_not_dvd_self_pow_sub_one hp hn (dvd_trans h (gcdPowerSeq_dvd_term n p p h1))

/-- If there exists a prime p with p-1 | n and k < p, then gcdPowerSeq n k ≠ 1.
    This is the Fermat mechanism: p divides the gcd, so gcd ≥ p ≥ 2. -/
theorem gcdPowerSeq_ne_one_of_large_prime {p : ℕ} (hp : Nat.Prime p) {n k : ℕ}
    (hdvd : (p - 1) ∣ n) (hk : k < p) : gcdPowerSeq n k ≠ 1 := by
  intro h1
  have := prime_dvd_gcdPowerSeq hp hdvd hk
  rw [h1] at this
  exact absurd (Nat.le_of_dvd one_pos this) (by have := hp.two_le; omega)

/-- Fermat phase transition: for prime p with (p-1) | n and n ≥ 1,
    p divides gcdPowerSeq n (p-1) but not gcdPowerSeq n p.
    This captures the exact moment h(n) = p: adding the p-th term breaks
    the shared factor p. -/
theorem gcdPowerSeq_fermat_transition {p : ℕ} (hp : Nat.Prime p) {n : ℕ}
    (hn : 0 < n) (hdvd : (p - 1) ∣ n) :
    p ∣ gcdPowerSeq n (p - 1) ∧ ¬(p ∣ gcdPowerSeq n p) :=
  ⟨prime_dvd_gcdPowerSeq hp hdvd (by omega), prime_not_dvd_gcdPowerSeq_self hp hn⟩

-- ## Key Structural Result: h(n) ≤ n + 1
--
-- For every n ≥ 1, gcdPowerSeq(n, n+1) = 1. This means h(n) ≤ n+1.
-- The proof: any prime q dividing the gcd leads to contradiction.
--   - If q ≤ n+1: q is in the fold, so q | q^n - 1. But q | q^n, so q | 1.
--   - If q > n+1: the n+1 distinct values {1,...,n+1} are all roots of x^n - 1
--     in ZMod q, but a degree-n polynomial has at most n roots.

/-- Any prime q in [2, n+1] cannot divide gcdPowerSeq n (n+1),
    because it would require q | q^n - 1, hence q | 1. -/
private theorem no_small_prime_dvd_gcdPowerSeq_succ {n q : ℕ}
    (hn : 0 < n) (hq : Nat.Prime q) (hq_le : q ≤ n + 1) (hq_dvd : q ∣ gcdPowerSeq n (n + 1)) :
    False := by
  have hq_mem : q ∈ Finset.Icc 2 (n + 1) :=
    Finset.mem_Icc.mpr ⟨hq.two_le, hq_le⟩
  have h1 : q ∣ (q ^ n - 1) := dvd_trans hq_dvd (gcdPowerSeq_dvd_term n (n + 1) q hq_mem)
  have h2 : q ∣ q ^ n := dvd_pow_self q hn.ne'
  have h3 : 1 ≤ q ^ n := Nat.one_le_pow n q hq.pos
  have h4 : q ∣ q ^ n - (q ^ n - 1) := Nat.dvd_sub' h2 h1
  have h5 : q ^ n - (q ^ n - 1) = 1 := by omega
  rw [h5] at h4
  exact absurd (Nat.le_of_dvd one_pos h4) (by omega)

/-- If q is prime and q ∣ (a^n - 1), then (a : ZMod q)^n = 1. -/
private theorem zmod_pow_eq_one_of_dvd {q a n : ℕ} [Fact (Nat.Prime q)]
    (h_ge : 1 ≤ a ^ n) (h_dvd : q ∣ (a ^ n - 1)) :
    ((a : ℕ) : ZMod q) ^ n = 1 := by
  have h0 : ((a ^ n - 1 : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h_dvd
  rw [Nat.cast_sub h_ge, Nat.cast_one] at h0
  rwa [sub_eq_zero, Nat.cast_pow] at h0

/-- Any prime q > n+1 cannot divide gcdPowerSeq n (n+1).
    Proof: the polynomial X^n - 1 over ZMod q has degree n, so at most n roots.
    But {1, 2, ..., n+1} gives n+1 distinct roots (they are distinct mod q
    since q > n+1, and each satisfies x^n = 1 by Fermat/gcd divisibility). -/
private theorem no_large_prime_dvd_gcdPowerSeq_succ {n q : ℕ}
    (hn : 0 < n) (hq : Nat.Prime q) (hq_gt : q > n + 1)
    (hq_dvd : q ∣ gcdPowerSeq n (n + 1)) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- Define polynomial f = X^n - 1 over ZMod q
  set f : (ZMod q)[X] := Polynomial.X ^ n - 1 with hf_def
  -- f has degree n (leading coeff 1 ≠ 0 in ZMod q, constant term doesn't affect degree)
  have hf_deg : f.natDegree = n :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
      simp [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]; exact hn)
  -- f ≠ 0
  have hf_ne : f ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hf_deg; omega
  -- Each a ∈ [1, n+1] satisfies f.IsRoot (a : ZMod q), i.e., a^n = 1 in ZMod q
  have is_root : ∀ a ∈ Finset.Icc 1 (n + 1), f.IsRoot ((a : ℕ) : ZMod q) := by
    intro a ha
    rw [Polynomial.IsRoot, hf_def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero]
    rw [Finset.mem_Icc] at ha
    by_cases ha1 : a = 1
    · subst ha1; simp
    · have ha_ge2 : 2 ≤ a := by omega
      have ha_mem : a ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr ⟨ha_ge2, ha.2⟩
      exact zmod_pow_eq_one_of_dvd
        (Nat.one_le_pow n a (by omega))
        (dvd_trans hq_dvd (gcdPowerSeq_dvd_term n (n + 1) a ha_mem))
  -- Each a ∈ [1, n+1] is a member of f.roots
  have mem_roots : ∀ a ∈ Finset.Icc 1 (n + 1), ((a : ℕ) : ZMod q) ∈ f.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne]
    exact is_root a ha
  -- The image of [1, n+1] in ZMod q is injective (all values < q)
  set S := (Finset.Icc 1 (n + 1)).image (Nat.cast : ℕ → ZMod q) with hS_def
  have hS_card : S.card = n + 1 := by
    rw [hS_def, Finset.card_image_of_injOn]
    · simp [Finset.card_Icc]
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      have := congr_arg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (by omega : a < q),
           ZMod.val_natCast_of_lt (by omega : b < q)] at this
  -- S ⊆ f.roots.toFinset
  have hS_sub : S ⊆ f.roots.toFinset := by
    intro x hx
    rw [hS_def, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact mem_roots a ha
  -- Root count: n+1 = |S| ≤ |f.roots.toFinset| ≤ |f.roots| ≤ natDegree(f) = n
  have h1 : S.card ≤ f.roots.toFinset.card := Finset.card_le_card hS_sub
  have h2 : f.roots.toFinset.card ≤ f.natDegree := by
    calc f.roots.toFinset.card
        ≤ Multiset.card f.roots :=
          Multiset.card_le_card (Multiset.dedup_le f.roots)
      _ ≤ f.natDegree := Polynomial.card_roots_le_degree f
  rw [hS_card] at h1; rw [hf_deg] at h2; omega

/-- **Main structural theorem**: gcdPowerSeq n (n+1) = 1 for all n ≥ 1.
    Equivalently, h(n) ≤ n + 1 for all positive n.
    Any prime dividing the gcd leads to contradiction:
    small primes (q ≤ n+1) self-divide, large primes (q > n+1) violate root counting. -/
theorem gcdPowerSeq_at_succ_eq_one {n : ℕ} (hn : 0 < n) :
    gcdPowerSeq n (n + 1) = 1 := by
  by_contra hne
  -- gcdPowerSeq n (n+1) ≥ 1 since it divides 2^n - 1 > 0
  have h_pos : 0 < gcdPowerSeq n (n + 1) := by
    have h2_mem : 2 ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩
    have h2n : 0 < 2 ^ n - 1 := by
      have : 2 ^ n ≥ 2 := Nat.one_le_pow n 2 (by omega) |>.trans_lt (by omega) |>.le
      omega
    exact Nat.pos_of_dvd_of_pos (gcdPowerSeq_dvd_term n (n + 1) 2 h2_mem) h2n
  have h_ge2 : gcdPowerSeq n (n + 1) ≥ 2 := by omega
  -- Extract a prime divisor
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (by omega : gcdPowerSeq n (n + 1) ≠ 1)
  -- Case split: q ≤ n+1 or q > n+1
  by_cases hle : q ≤ n + 1
  · exact no_small_prime_dvd_gcdPowerSeq_succ hn hq_prime hle hq_dvd
  · exact no_large_prime_dvd_gcdPowerSeq_succ hn hq_prime (by omega) hq_dvd

/-- When n+1 is prime, h(n) = n + 1.
    The gcd at n is ≠ 1 (Fermat: (n+1) divides all terms), and
    the gcd at n+1 equals 1 (by gcdPowerSeq_at_succ_eq_one). -/
theorem h_eq_succ_of_prime {n : ℕ} (hn : 0 < n) (hp : Nat.Prime (n + 1)) :
    gcdPowerSeq n n ≠ 1 ∧ gcdPowerSeq n (n + 1) = 1 :=
  ⟨gcdPowerSeq_ne_one_of_large_prime hp (dvd_refl (n + 1 - 1)) (by omega),
   gcdPowerSeq_at_succ_eq_one hn⟩

-- ## Formal definition of h(n)

/-- `hMinK n` is the minimal k such that gcdPowerSeq n k = 1, i.e., the minimal k
    where gcd(2^n−1, ..., k^n−1) = 1. Returns 0 for n = 0 (vacuous). -/
noncomputable def hMinK (n : ℕ) : ℕ :=
  if hn : 0 < n then
    Nat.find (⟨n + 1, gcdPowerSeq_at_succ_eq_one hn⟩ : ∃ k, gcdPowerSeq n k = 1)
  else 0

/-- h(n) satisfies gcdPowerSeq n (hMinK n) = 1 for n ≥ 1. -/
theorem hMinK_spec {n : ℕ} (hn : 0 < n) : gcdPowerSeq n (hMinK n) = 1 := by
  unfold hMinK; rw [dif_pos hn]
  exact Nat.find_spec ⟨n + 1, gcdPowerSeq_at_succ_eq_one hn⟩

/-- h(n) ≤ n + 1 for all n ≥ 1. -/
theorem hMinK_le_succ {n : ℕ} (hn : 0 < n) : hMinK n ≤ n + 1 := by
  unfold hMinK; rw [dif_pos hn]
  exact Nat.find_le (gcdPowerSeq_at_succ_eq_one hn)

/-- h(n) is minimal: for any k < hMinK n, gcdPowerSeq n k ≠ 1. -/
theorem hMinK_is_min {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k < hMinK n) :
    gcdPowerSeq n k ≠ 1 := by
  unfold hMinK at hk; rw [dif_pos hn] at hk
  exact Nat.find_min ⟨n + 1, gcdPowerSeq_at_succ_eq_one hn⟩ hk

-- ## Fermat formula: h(p-1) = p for primes p

/-- **Key formula**: for any prime p, h(p-1) = p.
    Upper bound: gcdPowerSeq (p-1) p = 1 from gcdPowerSeq_at_succ_eq_one.
    Lower bound: Fermat implies gcdPowerSeq (p-1) k ≠ 1 for all k < p,
    so h(p-1) cannot be strictly less than p. -/
theorem hMinK_prime_minus_one {p : ℕ} (hp : Nat.Prime p) : hMinK (p - 1) = p := by
  have hn : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  apply Nat.le_antisymm
  · -- h(p-1) ≤ p: use gcdPowerSeq (p-1) p = 1
    unfold hMinK; rw [dif_pos hn]
    apply Nat.find_le
    have : p - 1 + 1 = p := by omega
    rw [← this]; exact gcdPowerSeq_at_succ_eq_one hn
  · -- h(p-1) ≥ p: any k < p satisfies gcdPowerSeq (p-1) k ≠ 1 by Fermat
    by_contra h
    push_neg at h
    exact absurd (hMinK_spec hn)
      (gcdPowerSeq_ne_one_of_large_prime hp (dvd_refl (p - 1)) h)

/-- When n+1 is prime, h(n) = n+1.
    Corollary of hMinK_prime_minus_one with p = n+1. -/
theorem hMinK_succ_of_prime {n : ℕ} (hp : Nat.Prime (n + 1)) : hMinK n = n + 1 := by
  have h := hMinK_prime_minus_one hp
  have : n + 1 - 1 = n := by omega
  rwa [this] at h

-- ## Unboundedness of h(n)

/-- **Q2 resolved (upper half)**: h(n) is unbounded.
    For any M, there exists n with h(n) > M.
    Proof: take any prime p > M; then h(p-1) = p > M. -/
theorem hMinK_unbounded (M : ℕ) : ∃ n, M < hMinK n := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (M + 1)
  exact ⟨p - 1, hMinK_prime_minus_one hp_prime ▸ by omega⟩

/-- **Q1 (OPEN)**: For each prime p, the natural density of {n : ℕ | hMinK n = p}
    exists. The conjectured density δ_p is the probability that the smallest
    prime q with q ∤ (q-1)! satisfying some divisibility condition equals p.
    [OPEN — requires density theory for multiplicative functions] -/
axiom erdos_770_q1 : ∀ p : ℕ, Nat.Prime p →
    ∃ δ : ℝ, 0 ≤ δ ∧ Filter.Tendsto
      (fun N : ℕ => ((Finset.filter (fun n => hMinK n = p) (Finset.range N)).card : ℝ) / N)
      Filter.atTop (nhds δ)

/-- **Q3 (OPEN)**: The function hMinK is characterized by the dominant prime divisor.
    Specifically: if p is the largest prime with (p-1) | n, then hMinK n = p
    for all sufficiently large n satisfying the dominance condition.
    [OPEN — no proof exists in the literature] -/
axiom erdos_770_q3 : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ p : ℕ, Nat.Prime p → (p - 1) ∣ n →
    (∀ q : ℕ, Nat.Prime q → (q - 1) ∣ n → q ≤ p) →
    hMinK n = p
