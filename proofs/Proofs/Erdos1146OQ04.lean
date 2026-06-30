/-
  Erdős Problem #1146 — OQ-04
  A verified upper bound on the 3-smooth counting function.

  Erdős #1146 (OPEN) asks whether the 3-smooth numbers
  `B = {2^m · 3^n : m, n ≥ 0}` form an *essential component*.  The delicacy of the
  problem comes entirely from the *size* of `B`: by Ruzsa's theorem an essential
  component must satisfy `|A ∩ [1,N]| ≥ (log N)^{1+c}`, and the 3-smooth numbers
  have counting function on the order of `(log N)²` — right at the threshold.

  The parent file `Erdos1146Problem.lean` records the growth `~ C·(log N)²` as an
  *axiom* (`smooth23_counting`).  This file removes the need for that axiom on the
  **upper-bound side**: it proves, with no axioms and no `sorry`, the elementary
  estimate

      countingFunction smoothNumbers23 N ≤ (Nat.log 2 N + 1)²,

  i.e. `|B ∩ [1,N]| = O((log N)²)`.  The argument is pure lattice-point counting:
  every 3-smooth number `≤ N` is `2^m·3^n` with both `2^m ≤ N` and `2^n ≤ 3^n ≤ N`,
  so both exponents are at most `log₂ N`, giving at most `(log₂ N + 1)²` pairs and
  hence at most that many values.

  This is the honest, infrastructure-free half of the `(log N)²` counting claim
  (the matching lower bound `Ω((log N)²)`, which pins the constant and the exact
  threshold position, is recorded as future work).

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.Erdos37Problem

namespace Erdos1146.OQ04

open Finset Erdos37

/-- The exponent pairs `(m, n)` whose 3-smooth value `2^m·3^n` is a positive
    integer `≤ N`.  Searching `m, n < N+1` is wasteful but harmless: it is a finite
    superset of the genuinely-occurring pairs, which is all the upper bound needs. -/
def pairBound (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => 2 ^ p.1 * 3 ^ p.2 ≤ N)

/-- The 3-smooth numbers in `[1, N]` are exactly the values `2^m·3^n` of the pairs in
    `pairBound N`.  (Unique factorization is *not* needed: this is a set equality, and
    the upper bound only uses `⊆`.) -/
theorem smooth_inter_eq_image (N : ℕ) :
    smoothNumbers23 ∩ Set.Icc 1 N
      = ↑((pairBound N).image (fun p => 2 ^ p.1 * 3 ^ p.2)) := by
  ext k
  simp only [smoothNumbers23, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
    Finset.coe_image, Set.mem_image, Finset.mem_coe, pairBound, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨m, n, rfl⟩, hk1, hkN⟩
    have h2m : 2 ^ m ≤ 2 ^ m * 3 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
    have h3n : 3 ^ n ≤ 2 ^ m * 3 ^ n := Nat.le_mul_of_pos_left _ (by positivity)
    have hmlt : m < N + 1 := by
      have : m < 2 ^ m := Nat.lt_two_pow_self
      omega
    have hnlt : n < N + 1 := by
      have hn2 : n < 2 ^ n := Nat.lt_two_pow_self
      have hn23 : (2 : ℕ) ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
      omega
    exact ⟨(m, n), ⟨⟨hmlt, hnlt⟩, hkN⟩, rfl⟩
  · rintro ⟨⟨m, n⟩, ⟨⟨_, _⟩, hle⟩, rfl⟩
    refine ⟨⟨m, n, rfl⟩, ?_, hle⟩
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- The pair-search box has at most `(log₂ N + 1)²` admissible pairs: any pair with
    `2^m·3^n ≤ N` has both `m ≤ log₂ N` and `n ≤ log₂ N`. -/
theorem pairBound_card_le (N : ℕ) :
    (pairBound N).card ≤ (Nat.log 2 N + 1) ^ 2 := by
  have hsub : pairBound N ⊆
      Finset.range (Nat.log 2 N + 1) ×ˢ Finset.range (Nat.log 2 N + 1) := by
    intro p hp
    simp only [pairBound, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨_, hle⟩ := hp
    have h2m : 2 ^ p.1 ≤ 2 ^ p.1 * 3 ^ p.2 := Nat.le_mul_of_pos_right _ (by positivity)
    have h3n : 3 ^ p.2 ≤ 2 ^ p.1 * 3 ^ p.2 := Nat.le_mul_of_pos_left _ (by positivity)
    have hn23 : (2 : ℕ) ^ p.2 ≤ 3 ^ p.2 := Nat.pow_le_pow_left (by norm_num) p.2
    have hm : p.1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (le_trans h2m hle)
    have hn : p.2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (le_trans (le_trans hn23 h3n) hle)
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  calc (pairBound N).card
      ≤ (Finset.range (Nat.log 2 N + 1) ×ˢ Finset.range (Nat.log 2 N + 1)).card :=
        Finset.card_le_card hsub
    _ = (Nat.log 2 N + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_range, sq]

/-- **Verified upper bound on the 3-smooth counting function.**
    The number of 3-smooth integers in `[1, N]` is at most `(log₂ N + 1)²`, hence
    `|{2^m·3^n} ∩ [1,N]| = O((log N)²)`.  This is the elementary, axiom-free half of
    the parent file's `smooth23_counting` claim, and it is the property that places
    Erdős #1146 exactly at Ruzsa's `(log N)^{1+c}` threshold. -/
theorem smooth23_counting_upper (N : ℕ) :
    countingFunction smoothNumbers23 N ≤ (Nat.log 2 N + 1) ^ 2 := by
  unfold countingFunction
  rw [smooth_inter_eq_image, Set.ncard_coe_finset]
  exact le_trans (Finset.card_image_le) (pairBound_card_le N)

/-- Restated as genuine `O((log N)²)` growth: with the explicit constant `1`, for all `N`,
    `countingFunction smoothNumbers23 N ≤ (Nat.log 2 N + 1)²`.  The bound is uniform in `N`
    (no large-`N` hypothesis), so it certifies the big-O claim outright. -/
theorem smooth23_counting_isBigO :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, countingFunction smoothNumbers23 N ≤ C * (Nat.log 2 N + 1) ^ 2 :=
  ⟨1, one_pos, fun N => by simpa using smooth23_counting_upper N⟩

end Erdos1146.OQ04
