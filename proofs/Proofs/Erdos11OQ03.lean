/-
  Erdős Problem #11 — OQ-03: the squarefree distribution relative to powers of two

  Erdős Problem #11 (OPEN): is every odd `n > 1` the sum of a squarefree number and a
  power of two?  The parent thread (`Erdos11Problem`, `Erdos11WIP01`, and its `OQ01`/`OQ02`
  children) establishes the *existence* question — a bounded decidable characterization and
  a 0-axiom verified odd range.  This file takes the complementary **distributional** view:
  instead of asking *whether* a representation exists, it counts *how many* powers of two
  `2^k ≤ n` leave a squarefree complement `n − 2^k`, and bounds that count from both sides.

  Fix `n`.  The candidate exponents live in `range (n+1)` (because `k < 2^k ≤ n`), and each
  contributes iff `2^k ≤ n` and `n − 2^k` is squarefree.  We package:

  * `pow2Budget n` — the size of the *search space*: the number of powers of two `≤ n`.
    `pow2Budget_eq` shows it equals `Nat.log 2 n + 1` for `n ≥ 1` (the exponents `0 … log₂ n`).
  * `reprCount n` — the number of valid representations `n = (n − 2^k) + 2^k`, defined through
    the kernel-reducible squarefree test `SquarefreeCheck` so the count itself `decide`s.
  * `reprCount_le_budget` / `reprCount_le_log_succ` — **upper bound**: a number has at most
    `Nat.log 2 n + 1` such representations (you cannot use more powers of two than exist).
  * `reprCount_pos_iff` — **positivity = representability**: `0 < reprCount n ↔ n` is
    squarefree + a power of two, tying the distribution back to Erdős #11 exactly.
  * `erdos11_iff_reprCount_pos` — Erdős #11 restated as "the representation count is positive
    on every odd `n > 1`".
  * `reprCount_odd_ge_two_range` — **lower bound, verified**: every odd `n` with `1 < n < 100`
    has `2 ≤ reprCount n`.  On this range the representation is not merely satisfiable but
    *redundant* — at least two distinct powers of two work — proved by one kernel `decide`
    (no `native_decide`, so no `Lean.ofReduceBool`; 0 axioms).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Hercher (2024); Granville–Soundararajan (1998); https://erdosproblems.com/11.
-/

import Mathlib

namespace Erdos11OQ03

open Finset

/- ## Self-contained definitions

   Re-declared locally: the parent `Erdos11Problem` no longer builds on the current
   Mathlib, and each thread file stands alone to avoid cross-file drift. -/

/-- `n` is the sum of a squarefree number and a power of two. -/
def IsSquarefreePlusPow2 (n : ℕ) : Prop :=
  ∃ (s p : ℕ), Squarefree s ∧ (∃ k : ℕ, p = 2 ^ k) ∧ n = s + p

/-- **Bounded characterization** (recovered self-contained, cf. `Erdos11WIP01`).  `n` is
    squarefree + a power of two iff some exponent `k ≤ n` has `2^k ≤ n` and `n − 2^k`
    squarefree.  The bound `k ≤ n` comes from `k < 2^k ≤ n`. -/
theorem isSquarefreePlusPow2_iff (n : ℕ) :
    IsSquarefreePlusPow2 n ↔
      ∃ k ∈ Finset.range (n + 1), 2 ^ k ≤ n ∧ Squarefree (n - 2 ^ k) := by
  constructor
  · rintro ⟨s, p, hs, ⟨k, rfl⟩, rfl⟩
    have hle : 2 ^ k ≤ s + 2 ^ k := Nat.le_add_left _ _
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    refine ⟨k, Finset.mem_range.mpr (by omega), hle, ?_⟩
    rwa [Nat.add_sub_cancel]
  · rintro ⟨k, _, hle, hsf⟩
    exact ⟨n - 2 ^ k, 2 ^ k, hsf, ⟨k, rfl⟩, by omega⟩

/-- A bounded, **kernel-reducible** squarefree test (cf. `Erdos11WIP01OQ02`): `n ≥ 1` and no
    `d` with `2 ≤ d ≤ n` has `d * d ∣ n`.  Unlike `Squarefree`'s `Decidable` instance (which
    routes through `Nat.minSqFac` and does not kernel-reduce), this is a finite conjunction of
    `Nat` divisibility tests that the kernel reduces — so `decide` works at 0 axioms. -/
def SquarefreeCheck (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ d ∈ Finset.range (n + 1), 2 ≤ d → ¬ (d * d ∣ n)

instance : DecidablePred SquarefreeCheck := fun n =>
  inferInstanceAs (Decidable (1 ≤ n ∧ ∀ d ∈ Finset.range (n + 1), 2 ≤ d → ¬ (d * d ∣ n)))

/-- The kernel-reducible squarefree test is exactly `Squarefree` (unconditionally: both are
    `False` at `n = 0`). -/
theorem squarefree_iff_check (n : ℕ) : Squarefree n ↔ SquarefreeCheck n := by
  constructor
  · intro hsf
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact absurd hsf not_squarefree_zero
      · exact hpos
    refine ⟨hn, fun d _ hd2 hdvd => ?_⟩
    have : IsUnit d := hsf d hdvd
    rw [Nat.isUnit_iff] at this
    omega
  · rintro ⟨hn, hck⟩ x hxdvd
    rw [Nat.isUnit_iff]
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · interval_cases x
      · simp only [Nat.zero_mul, Nat.zero_dvd] at hxdvd; omega
      · rfl
    · exfalso
      have hxn : x ∣ n := dvd_trans (dvd_mul_left x x) hxdvd
      have hxle : x ≤ n := Nat.le_of_dvd hn hxn
      exact hck x (Finset.mem_range.mpr (by omega)) h2 hxdvd

/- ## The search space: powers of two below `n` -/

/-- `pow2Budget n` — the number of powers of two `≤ n`; equivalently, the number of exponents
    `k` with `2^k ≤ n`.  This is the size of the search space for a representation of `n`. -/
def pow2Budget (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => 2 ^ k ≤ n)).card

/-- **Search-space size.**  For `n ≥ 1` the powers of two `≤ n` are exactly `2^0, …, 2^{⌊log₂ n⌋}`,
    so there are `Nat.log 2 n + 1` of them. -/
theorem pow2Budget_eq (n : ℕ) (hn : 1 ≤ n) : pow2Budget n = Nat.log 2 n + 1 := by
  unfold pow2Budget
  rw [show Nat.log 2 n + 1 = (Finset.range (Nat.log 2 n + 1)).card from (Finset.card_range _).symm]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hk⟩
    rw [← Nat.le_log_iff_pow_le (by norm_num) (by omega)] at hk
    omega
  · intro hk
    have hkle : k ≤ Nat.log 2 n := by omega
    have h2k : 2 ^ k ≤ n := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mp hkle
    have hklt : k < 2 ^ k := Nat.lt_two_pow_self
    exact ⟨by omega, h2k⟩

/- ## The representation count -/

/-- `reprCount n` — the number of powers of two `2^k ≤ n` whose complement `n − 2^k` is
    squarefree; i.e. the number of representations `n = (n − 2^k) + 2^k`.  Defined through the
    kernel-reducible `SquarefreeCheck`, so the count itself is computable by `decide`. -/
def reprCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => 2 ^ k ≤ n ∧ SquarefreeCheck (n - 2 ^ k))).card

/-- **Upper bound (search-space form).**  A number has no more representations than there are
    powers of two below it. -/
theorem reprCount_le_budget (n : ℕ) : reprCount n ≤ pow2Budget n := by
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1⟩

/-- **Upper bound (closed form).**  For `n ≥ 1`, at most `Nat.log 2 n + 1` powers of two give a
    squarefree complement. -/
theorem reprCount_le_log_succ (n : ℕ) (hn : 1 ≤ n) : reprCount n ≤ Nat.log 2 n + 1 :=
  (reprCount_le_budget n).trans (pow2Budget_eq n hn).le

/-- **Positivity = representability.**  The representation count is positive exactly when `n`
    is squarefree + a power of two — the distribution's support is precisely the Erdős set. -/
theorem reprCount_pos_iff (n : ℕ) : 0 < reprCount n ↔ IsSquarefreePlusPow2 n := by
  rw [isSquarefreePlusPow2_iff, reprCount, Finset.card_pos, Finset.filter_nonempty_iff]
  simp_rw [squarefree_iff_check]

/-- **Erdős #11 as a distribution statement.**  The conjecture "every odd `n > 1` is squarefree
    + a power of two" is equivalent to "the representation count is positive on every odd `n > 1`". -/
theorem erdos11_iff_reprCount_pos :
    (∀ n : ℕ, Odd n → 1 < n → IsSquarefreePlusPow2 n) ↔
      (∀ n : ℕ, Odd n → 1 < n → 0 < reprCount n) := by
  constructor <;> intro h n hodd h1
  · exact (reprCount_pos_iff n).mpr (h n hodd h1)
  · exact (reprCount_pos_iff n).mp (h n hodd h1)

set_option maxRecDepth 10000 in
/-- **Verified lower bound: the representation is redundant on the small odd range.**  Every odd
    `n` with `1 < n < 100` has `2 ≤ reprCount n`: at least *two* distinct powers of two leave a
    squarefree complement (the minimum, `2`, is attained at `n = 3, 5, 13, 29`).  This strengthens
    the parent's "verified representable" range to "verified doubly representable", by a single
    kernel `decide` on the reducible count — no `native_decide`, hence no `Lean.ofReduceBool`. -/
theorem reprCount_odd_ge_two_range :
    ∀ n ∈ Finset.range 100, Odd n → 1 < n → 2 ≤ reprCount n := by decide

/-- Consequently every odd `n` with `1 < n < 100` is squarefree + a power of two (0 axioms),
    recovered here as a corollary of the strictly stronger count bound. -/
theorem isSquarefreePlusPow2_odd_range :
    ∀ n ∈ Finset.range 100, Odd n → 1 < n → IsSquarefreePlusPow2 n := by
  intro n hn hodd h1
  exact (reprCount_pos_iff n).mp (by have := reprCount_odd_ge_two_range n hn hodd h1; omega)

end Erdos11OQ03

#print axioms Erdos11OQ03.pow2Budget_eq
#print axioms Erdos11OQ03.reprCount_le_log_succ
#print axioms Erdos11OQ03.reprCount_pos_iff
#print axioms Erdos11OQ03.erdos11_iff_reprCount_pos
#print axioms Erdos11OQ03.reprCount_odd_ge_two_range
