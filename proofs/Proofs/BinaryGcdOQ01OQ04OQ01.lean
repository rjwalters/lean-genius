/-
  Binary GCD: exact step count for the `a = 1` slice (bit-length closed form)
  Open Question OQ-01 of `binary-gcd-oq-01-oq-04`.

  The parent `BinaryGcdOQ01OQ04` proved that the single family `(1, 2^n - 1)`
  takes exactly `n` steps, witnessing that the `O(log b)` upper bound is tight.
  That leaves open: *which* inputs are the worst case? This file gives the
  COMPLETE answer for the `a = 1` slice — an exact closed form for every `b`,
  not just `b = 2^n - 1`.

  **Main result `binaryGcdSteps_one_eq_log_succ`.**
  For every `b ≥ 1`,
      binaryGcdSteps 1 b = Nat.log 2 b + 1,
  i.e. the step count is exactly the *binary bit-length* of `b`. The proof
  rests on a uniform one-step reduction valid in BOTH parities:
      binaryGcdSteps 1 (b+1) = 1 + binaryGcdSteps 1 ((b+1)/2)
  (`binaryGcdSteps_one_succ`). Whether `b+1` is even (the `a`-odd/`b`-even
  branch halves `b`) or odd (the subtract-then-halve branch sends
  `b ↦ (b-1)/2 = ⌊b/2⌋`), the recursion is the same bit-shift, so the count
  is the number of shifts needed to reach `0` — the bit-length.

  **Consequences.**
  * `binaryGcdSteps_one_eq_dyadic`: every `b` with `2^n ≤ b < 2^(n+1)` (the
    `(n+1)`-bit numbers) takes exactly `n+1` steps — so the cost depends ONLY
    on the bit-length, and the worst case among `b < 2^N` is achieved by the
    ENTIRE top dyadic block `[2^(N-1), 2^N)`, not a single input.
  * `binaryGcdSteps_one_mono`: the count is monotone non-decreasing in `b`.
  * `binaryGcdSteps_one_pow2_sub_one`: recovers the parent's
    `binaryGcdSteps 1 (2^n - 1) = n` as a one-line corollary
    (`Nat.log 2 (2^n - 1) = n - 1`).

  This characterises the `a = 1` worst case completely; the full
  two-argument worst-case set remains open (see future work).

  References:
  - Stein (1967), Binary GCD Algorithm
  - BinaryGcdOQ01.lean (upper bound), BinaryGcdOQ01OQ04.lean (the (1,2^n-1) family)
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Proofs.BinaryGcdOQ01
import Proofs.BinaryGcdOQ01OQ04

namespace BinaryGcdOQ01OQ04OQ01

open BinaryGcdOQ01 Nat

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE UNIFORM ONE-STEP REDUCTION (BOTH PARITIES)
-- ═══════════════════════════════════════════════════════════════════

/-- **Uniform one-step lemma.** For every `b`,
      `binaryGcdSteps 1 (b+1) = 1 + binaryGcdSteps 1 ((b+1)/2)`.

    With `a = 1` (odd), the algorithm never takes an `a`-even branch. If
    `b+1` is even it halves `b+1`; if `b+1` is odd then `1 ≤ b+1` forces the
    final subtract-then-halve branch `b ↦ (b+1-1)/2`, which equals `(b+1)/2`
    because `b+1` is odd. Either way the next state is `(1, ⌊(b+1)/2⌋)`. -/
theorem binaryGcdSteps_one_succ (b : ℕ) :
    binaryGcdSteps 1 (b + 1) = 1 + binaryGcdSteps 1 ((b + 1) / 2) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, binaryGcdSteps.eq_3]
  by_cases hpar : (b + 1) % 2 = 0
  · -- `b+1` even: the `a`-odd / `b`-even branch halves `b+1`.
    rw [if_neg (show (0 + 1) % 2 ≠ 0 from by norm_num), if_pos hpar]
  · -- `b+1` odd: skip the `b`-even branch and the `a > b` branch (`1 > b+1` is false).
    rw [if_neg (show (0 + 1) % 2 ≠ 0 from by norm_num), if_neg hpar,
        if_neg (show ¬(0 + 1 > b + 1) from by omega)]
    congr 2
    omega

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE BIT-LENGTH CLOSED FORM
-- ═══════════════════════════════════════════════════════════════════

/-- **Main theorem.** For every `b ≥ 1`, the binary-GCD step count of the
    `a = 1` slice is exactly the binary bit-length of `b`:
      `binaryGcdSteps 1 b = Nat.log 2 b + 1`. -/
theorem binaryGcdSteps_one_eq_log_succ :
    ∀ b : ℕ, 1 ≤ b → binaryGcdSteps 1 b = Nat.log 2 b + 1 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    rcases Nat.lt_or_ge b 2 with hlt | hge
    · -- base case `b = 1`
      obtain rfl : b = 1 := by omega
      rw [show (1 : ℕ) = 0 + 1 from rfl, binaryGcdSteps_one_succ]
      simp [Nat.log_one_right]
    · -- inductive step `b ≥ 2`: peel one bit
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [binaryGcdSteps_one_succ b']
      have hlt' : (b' + 1) / 2 < b' + 1 := by omega
      have hpos' : 1 ≤ (b' + 1) / 2 := by omega
      rw [ih ((b' + 1) / 2) hlt' hpos']
      have hlogdiv : Nat.log 2 ((b' + 1) / 2) = Nat.log 2 (b' + 1) - 1 :=
        Nat.log_div_base 2 (b' + 1)
      have hlogpos : 0 < Nat.log 2 (b' + 1) := Nat.log_pos (by norm_num) (by omega)
      omega

-- ═══════════════════════════════════════════════════════════════════
-- PART III: WORST-CASE CHARACTERISATION OF THE a = 1 SLICE
-- ═══════════════════════════════════════════════════════════════════

/-- **The cost depends only on the bit-length.** Every `b` in the dyadic
    block `[2^n, 2^(n+1))` — i.e. every `(n+1)`-bit number — takes exactly
    `n + 1` steps. Hence the worst case among `b < 2^N` is not one input but
    the entire top block `[2^(N-1), 2^N)`. -/
theorem binaryGcdSteps_one_eq_dyadic {n b : ℕ}
    (hlo : 2 ^ n ≤ b) (hhi : b < 2 ^ (n + 1)) :
    binaryGcdSteps 1 b = n + 1 := by
  have hb : 1 ≤ b := (Nat.one_le_two_pow).trans hlo
  rw [binaryGcdSteps_one_eq_log_succ b hb,
    Nat.log_eq_of_pow_le_of_lt_pow hlo hhi]

/-- **Monotonicity.** The `a = 1` step count is non-decreasing in `b`
    (immediate from the bit-length form and `Nat.log` monotonicity). -/
theorem binaryGcdSteps_one_mono {b₁ b₂ : ℕ} (h1 : 1 ≤ b₁) (h : b₁ ≤ b₂) :
    binaryGcdSteps 1 b₁ ≤ binaryGcdSteps 1 b₂ := by
  rw [binaryGcdSteps_one_eq_log_succ b₁ h1,
    binaryGcdSteps_one_eq_log_succ b₂ (h1.trans h)]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: RECOVERING THE PARENT FAMILY (1, 2^n - 1)
-- ═══════════════════════════════════════════════════════════════════

/-- `Nat.log 2 (2^n - 1) = n - 1` for `n ≥ 1`: the predecessor of a power of
    two has exactly `n` bits with value `< 2^n`, so its log is `n - 1`. -/
theorem log_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Nat.log 2 (2 ^ n - 1) = n - 1 := by
  have hge : 2 ^ (n - 1) ≤ 2 ^ n - 1 := by
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  have hlt : 2 ^ n - 1 < 2 ^ ((n - 1) + 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have : (n - 1) + 1 = n := by omega
    rw [this]; omega
  exact Nat.log_eq_of_pow_le_of_lt_pow hge hlt

/-- **Recovers the parent result.** The family `(1, 2^n - 1)` takes exactly
    `n` steps — now a one-line corollary of the bit-length closed form. -/
theorem binaryGcdSteps_one_pow2_sub_one {n : ℕ} (hn : 1 ≤ n) :
    binaryGcdSteps 1 (2 ^ n - 1) = n := by
  have hb : 1 ≤ 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  rw [binaryGcdSteps_one_eq_log_succ _ hb, log_two_pow_sub_one hn]
  omega

-- ═══════════════════════════════════════════════════════════════════
-- PART V: SYMBOLIC CROSS-CHECKS (axiom-free)
-- ═══════════════════════════════════════════════════════════════════

/-- The whole dyadic block `[4, 8)` (the 3-bit numbers `4,5,6,7`) takes the
    same step count — so the worst case below `8` is an entire block, not a
    single input. Derived from `binaryGcdSteps_one_eq_dyadic` (no `decide`). -/
example : binaryGcdSteps 1 4 = binaryGcdSteps 1 7 := by
  rw [binaryGcdSteps_one_eq_dyadic (n := 2) (by norm_num) (by norm_num),
      binaryGcdSteps_one_eq_dyadic (n := 2) (by norm_num) (by norm_num)]

/-- `(1, 7) = (1, 2^3 - 1)` takes exactly `3` steps, via the parent-recovering
    corollary — a symbolic spot check of the closed form. -/
example : binaryGcdSteps 1 7 = 3 := by
  have : (7 : ℕ) = 2 ^ 3 - 1 := by norm_num
  rw [this, binaryGcdSteps_one_pow2_sub_one (by norm_num)]

end BinaryGcdOQ01OQ04OQ01
