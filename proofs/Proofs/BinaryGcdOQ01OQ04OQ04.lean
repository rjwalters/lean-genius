/-
  Binary GCD: the diagonal slice `a = b` — the first interior slice, in closed form
  Open Question OQ-04 of `binary-gcd-oq-01-oq-04`.

  The parent settled one worst-case witness `(1, 2^n - 1)`; sibling OQ-01 gave
  the complete `a = 1` axis slice `binaryGcdSteps 1 b = Nat.log 2 b + 1` (the
  binary bit-length); sibling OQ-02 added symmetry and transposed that to the
  `b = 1` axis slice; sibling OQ-03 pinned the *average* of the `a = 1` row at a
  `Θ(log N)`. All of those live on the axes `a = 1` or `b = 1`. OQ-02 explicitly
  left open whether the interior pairs `a, b > 1` can beat the axis, and asked
  for the behaviour off the axes. This file settles the very first interior
  slice — the **diagonal** `a = b` — completely.

  **Main result `binaryGcdSteps_diag`.**
      binaryGcdSteps n n = padicValNat 2 n + 1     for every n ≥ 1,
  i.e. the diagonal step count is exactly the **2-adic valuation** of `n`
  plus one — the number of trailing binary zeros of `n`, plus one. This is
  the exact mirror of the axis law (bit-length `Nat.log 2 n + 1`), now with
  the *valuation* `padicValNat 2 n` in place of the *logarithm*.

  The reason is a clean one-step recursion on the diagonal:
  * if `n` is odd, both arguments are equal odds, so Stein's odd/odd rule
    subtracts them to `0` in a single step: `binaryGcdSteps n n = 1`;
  * if `n` is even, both arguments are even, so the even/even rule halves
    both: `binaryGcdSteps n n = 1 + binaryGcdSteps (n/2) (n/2)`.
  Iterating the halving strips one factor of `2` per step until an odd number
  is reached, whence the count is `v₂(n) + 1`.

  **Constructive form and corollaries.**
  * `binaryGcdSteps_diag_two_pow_mul`: for odd `m`,
    `binaryGcdSteps (2^k * m) (2^k * m) = k + 1` — the same statement written
    out over the unique factorisation `n = 2^k · m`, proved by a direct
    induction on `k` with no valuation machinery.
  * `binaryGcdSteps_diag_two_pow`: `binaryGcdSteps (2^k) (2^k) = k + 1`.
  * `binaryGcdSteps_diag_le_log`: `binaryGcdSteps n n ≤ Nat.log 2 n + 1`,
    since `v₂(n) ≤ log₂(n)`.
  * `binaryGcdSteps_diag_le_axis`: `binaryGcdSteps n n ≤ binaryGcdSteps 1 n` —
    the diagonal **never exceeds the axis slice**. This answers OQ-02's open
    question for the diagonal: the interior diagonal pairs are *cheaper* than
    the `a = 1` axis, so the worst case does not migrate onto the diagonal.

  All results are axiom-free (only the foundational `propext`/`Classical.choice`/
  `Quot.sound`), 0 sorries; no `decide` / `native_decide`.

  References:
  - Stein (1967), Binary GCD Algorithm
  - BinaryGcdOQ01.lean (definition + upper bound),
    BinaryGcdOQ01OQ04OQ01.lean (the `a = 1` axis slice closed form),
    BinaryGcdOQ01OQ04OQ02.lean (symmetry + the `b = 1` axis slice),
    BinaryGcdOQ01OQ04OQ03.lean (the `a = 1` average is `Θ(log N)`)
-/
import Mathlib
import Proofs.BinaryGcdOQ01
import Proofs.BinaryGcdOQ01OQ04OQ01

namespace BinaryGcdOQ01OQ04OQ04

open BinaryGcdOQ01 Nat

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE ONE-STEP DIAGONAL REDUCTIONS
-- ═══════════════════════════════════════════════════════════════════

/-- **Odd diagonal step.** When `n` is odd, the two equal odd arguments hit
    Stein's odd/odd branch, which subtracts the smaller from the larger; here
    the difference is `0`, so the algorithm terminates in a single step:
      `binaryGcdSteps n n = 1`. -/
theorem binaryGcdSteps_diag_odd {n : ℕ} (ho : n % 2 = 1) :
    binaryGcdSteps n n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [binaryGcdSteps.eq_3,
      if_neg (by omega : ¬ (m + 1) % 2 = 0),
      if_neg (by omega : ¬ (m + 1) % 2 = 0),
      if_neg (by omega : ¬ m + 1 > m + 1)]
  simp

/-- **Even diagonal step.** When `n ≥ 1` is even, both arguments are even, so
    Stein's even/even branch halves both:
      `binaryGcdSteps n n = 1 + binaryGcdSteps (n/2) (n/2)`. -/
theorem binaryGcdSteps_diag_even {n : ℕ} (he : n % 2 = 0) (hn : 1 ≤ n) :
    binaryGcdSteps n n = 1 + binaryGcdSteps (n / 2) (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [binaryGcdSteps.eq_3, if_pos he, if_pos he]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE DIAGONAL CLOSED FORM  (2-adic valuation)
-- ═══════════════════════════════════════════════════════════════════

/-- **Main theorem.** For every `n ≥ 1`, the diagonal step count is the
    2-adic valuation of `n` plus one:
      `binaryGcdSteps n n = padicValNat 2 n + 1`.
    Compare the axis law `binaryGcdSteps 1 n = Nat.log 2 n + 1`: the diagonal
    replaces the bit-length (logarithm) by the number of trailing zeros
    (valuation). -/
theorem binaryGcdSteps_diag :
    ∀ n : ℕ, 1 ≤ n → binaryGcdSteps n n = padicValNat 2 n + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with he | ho
    · -- `n` even: halve and recurse; the valuation drops by exactly one.
      have he2 : n % 2 = 0 := Nat.even_iff.mp he
      have hdvd : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero he2
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hpos : 1 ≤ n / 2 := by omega
      rw [binaryGcdSteps_diag_even he2 hn, ih (n / 2) hlt hpos]
      have hval : padicValNat 2 (n / 2) = padicValNat 2 n - 1 := padicValNat.div hdvd
      have hge : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd (by omega) hdvd
      omega
    · -- `n` odd: one step, valuation `0`.
      have ho2 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [binaryGcdSteps_diag_odd ho2]
      have : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      omega

-- ═══════════════════════════════════════════════════════════════════
-- PART III: CONSTRUCTIVE FORM OVER THE FACTORISATION  n = 2^k · m
-- ═══════════════════════════════════════════════════════════════════

/-- **Constructive diagonal law.** Writing `n = 2^k · m` with `m` odd, the
    diagonal takes exactly `k + 1` steps. Proved by a direct induction on `k`
    from the one-step reductions — no valuation machinery. -/
theorem binaryGcdSteps_diag_two_pow_mul {m : ℕ} (hm : m % 2 = 1) :
    ∀ k : ℕ, binaryGcdSteps (2 ^ k * m) (2 ^ k * m) = k + 1 := by
  intro k
  induction k with
  | zero => simpa using binaryGcdSteps_diag_odd (n := m) hm
  | succ k ih =>
    have hx : 0 < 2 ^ k * m := Nat.mul_pos (pow_pos (by norm_num) k) (by omega)
    have hrw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [hrw, binaryGcdSteps_diag_even (by omega) (by omega)]
    have hdiv : 2 * (2 ^ k * m) / 2 = 2 ^ k * m := by omega
    rw [hdiv, ih]
    omega

/-- The pure powers of two on the diagonal: `binaryGcdSteps (2^k) (2^k) = k + 1`. -/
theorem binaryGcdSteps_diag_two_pow (k : ℕ) :
    binaryGcdSteps (2 ^ k) (2 ^ k) = k + 1 := by
  simpa using binaryGcdSteps_diag_two_pow_mul (m := 1) (by norm_num) k

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE DIAGONAL NEVER EXCEEDS THE AXIS SLICE
-- ═══════════════════════════════════════════════════════════════════

/-- The diagonal cost is bounded by the bit-length: `binaryGcdSteps n n ≤
    Nat.log 2 n + 1`, because `v₂(n) ≤ log₂(n)`. -/
theorem binaryGcdSteps_diag_le_log (n : ℕ) (hn : 1 ≤ n) :
    binaryGcdSteps n n ≤ Nat.log 2 n + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [binaryGcdSteps_diag n hn]
  exact Nat.add_le_add_right (padicValNat_le_nat_log n) 1

/-- **The diagonal never beats the axis.** For every `n ≥ 1`,
      `binaryGcdSteps n n ≤ binaryGcdSteps 1 n`.
    Since the `a = 1` axis slice equals the bit-length `Nat.log 2 n + 1`
    (sibling OQ-01) and the diagonal equals the smaller valuation `v₂(n) + 1`,
    the interior diagonal is *cheaper* than the axis. This answers OQ-02's
    open question for the diagonal: the worst case does not migrate onto it. -/
theorem binaryGcdSteps_diag_le_axis (n : ℕ) (hn : 1 ≤ n) :
    binaryGcdSteps n n ≤ binaryGcdSteps 1 n := by
  rw [BinaryGcdOQ01OQ04OQ01.binaryGcdSteps_one_eq_log_succ n hn]
  exact binaryGcdSteps_diag_le_log n hn

-- ═══════════════════════════════════════════════════════════════════
-- PART V: SYMBOLIC CROSS-CHECKS (axiom-free, no decide)
-- ═══════════════════════════════════════════════════════════════════

/-- `8 = 2^3` is on the diagonal `4` steps deep, via the power-of-two form. -/
example : binaryGcdSteps 8 8 = 4 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, binaryGcdSteps_diag_two_pow]

/-- Every odd `n` takes a single diagonal step. -/
example : binaryGcdSteps 5 5 = 1 := binaryGcdSteps_diag_odd (by norm_num)

/-- `12 = 2^2 · 3` (with `3` odd) takes `3` steps — the constructive form. -/
example : binaryGcdSteps 12 12 = 3 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h, binaryGcdSteps_diag_two_pow_mul (m := 3) (by norm_num)]

/-- The diagonal at `12` matches the general valuation closed form. -/
example : binaryGcdSteps 12 12 = padicValNat 2 12 + 1 :=
  binaryGcdSteps_diag 12 (by norm_num)

end BinaryGcdOQ01OQ04OQ04
