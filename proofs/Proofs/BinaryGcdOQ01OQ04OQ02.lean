/-
  Binary GCD: symmetry of the step count, and the `b = 1` slice closed form
  Open Question OQ-02 of `binary-gcd-oq-01-oq-04`.

  The sibling `BinaryGcdOQ01OQ04OQ01` characterised the `a = 1` slice
  completely: `binaryGcdSteps 1 b = Nat.log 2 b + 1` (the binary bit-length).
  It explicitly left open "the full two-argument worst-case set". A first
  structural step toward that is the basic symmetry of the cost function,
  which is *not* recorded in any sibling file even though the algorithm treats
  its two arguments symmetrically.

  **Main result `binaryGcdSteps_comm`.**
      binaryGcdSteps a b = binaryGcdSteps b a   for all a b.
  Proved by strong induction on `a + b`: in every branch of the recursion the
  two unfoldings of `binaryGcdSteps (a+1) (b+1)` and `binaryGcdSteps (b+1) (a+1)`
  reduce to recursive calls that are mirror images of each other, closed by the
  induction hypothesis. The even/even, even/odd, odd/even branches map onto
  their transposes directly; the odd/odd branch subtracts the smaller from the
  larger in both orientations, so the `a > b` case of one side is the `b < a`
  case of the other.

  **Consequences (free from symmetry + the sibling's `a = 1` analysis).**
  * `binaryGcdSteps_one_right_eq_log_succ`: `binaryGcdSteps a 1 = Nat.log 2 a + 1`
    for every `a ≥ 1` — the `b = 1` slice is the same bit-length closed form.
  * `binaryGcdSteps_one_right_eq_dyadic`: the `b = 1` cost depends only on the
    bit-length of `a` (constant on each dyadic block `[2^n, 2^(n+1))`).
  * `binaryGcdSteps_one_right_mono`: monotone non-decreasing in `a`.
  * `binaryGcdSteps_one_right_pow2_sub_one`: `binaryGcdSteps (2^n - 1) 1 = n`.

  All results are axiom-free (only the foundational `propext`/`Classical.choice`/
  `Quot.sound`), 0 sorries.

  References:
  - Stein (1967), Binary GCD Algorithm
  - BinaryGcdOQ01.lean (definition + upper bound),
    BinaryGcdOQ01OQ04OQ01.lean (the `a = 1` slice closed form)
-/
import Mathlib
import Proofs.BinaryGcdOQ01
import Proofs.BinaryGcdOQ01OQ04OQ01

namespace BinaryGcdOQ01OQ04OQ02

open BinaryGcdOQ01 Nat

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SYMMETRY OF THE BINARY-GCD STEP COUNT
-- ═══════════════════════════════════════════════════════════════════

/-- Fueled strong-induction core of symmetry. -/
private theorem binaryGcdSteps_comm_aux :
    ∀ n a b : ℕ, a + b ≤ n → binaryGcdSteps a b = binaryGcdSteps b a := by
  intro n
  induction n with
  | zero =>
    intro a b h
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    rfl
  | succ n ih =>
    intro a b h
    rcases a with _ | a'
    · -- a = 0
      simp [binaryGcdSteps]
    · rcases b with _ | b'
      · -- b = 0
        simp [binaryGcdSteps]
      · -- a = a'+1, b = b'+1: unfold both orientations and match branches
        rw [binaryGcdSteps.eq_3, binaryGcdSteps.eq_3]
        rcases lt_trichotomy a' b' with hlt | rfl | hgt
        · -- a < b: the `a > b` branches are contradictory, the rest are transposes
          split_ifs <;> first | (exfalso; omega) | (congr 1; apply ih; omega)
        · -- a = b: both orientations unfold to the identical if-tree
          rfl
        · -- a > b: symmetric to the first case
          split_ifs <;> first | (exfalso; omega) | (congr 1; apply ih; omega)

/-- **Symmetry.** The binary-GCD step count is symmetric in its two arguments:
    `binaryGcdSteps a b = binaryGcdSteps b a`. -/
theorem binaryGcdSteps_comm (a b : ℕ) :
    binaryGcdSteps a b = binaryGcdSteps b a :=
  binaryGcdSteps_comm_aux (a + b) a b le_rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE b = 1 SLICE (mirror of the a = 1 closed form)
-- ═══════════════════════════════════════════════════════════════════

/-- **The `b = 1` slice closed form.** For every `a ≥ 1`,
    `binaryGcdSteps a 1 = Nat.log 2 a + 1` — the same bit-length law as the
    `a = 1` slice, now via symmetry. -/
theorem binaryGcdSteps_one_right_eq_log_succ (a : ℕ) (ha : 1 ≤ a) :
    binaryGcdSteps a 1 = Nat.log 2 a + 1 := by
  rw [binaryGcdSteps_comm, BinaryGcdOQ01OQ04OQ01.binaryGcdSteps_one_eq_log_succ a ha]

/-- The `b = 1` cost depends only on the bit-length of `a`: every `a` in the
    dyadic block `[2^n, 2^(n+1))` takes exactly `n + 1` steps. -/
theorem binaryGcdSteps_one_right_eq_dyadic {n a : ℕ}
    (hlo : 2 ^ n ≤ a) (hhi : a < 2 ^ (n + 1)) :
    binaryGcdSteps a 1 = n + 1 := by
  rw [binaryGcdSteps_comm, BinaryGcdOQ01OQ04OQ01.binaryGcdSteps_one_eq_dyadic hlo hhi]

/-- Monotonicity of the `b = 1` slice in `a`. -/
theorem binaryGcdSteps_one_right_mono {a₁ a₂ : ℕ} (h1 : 1 ≤ a₁) (h : a₁ ≤ a₂) :
    binaryGcdSteps a₁ 1 ≤ binaryGcdSteps a₂ 1 := by
  rw [binaryGcdSteps_comm a₁ 1, binaryGcdSteps_comm a₂ 1]
  exact BinaryGcdOQ01OQ04OQ01.binaryGcdSteps_one_mono h1 h

/-- The family `(2^n - 1, 1)` takes exactly `n` steps — the transpose of the
    parent worst-case family `(1, 2^n - 1)`. -/
theorem binaryGcdSteps_one_right_pow2_sub_one {n : ℕ} (hn : 1 ≤ n) :
    binaryGcdSteps (2 ^ n - 1) 1 = n := by
  rw [binaryGcdSteps_comm, BinaryGcdOQ01OQ04OQ01.binaryGcdSteps_one_pow2_sub_one hn]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: SYMBOLIC CROSS-CHECKS (axiom-free)
-- ═══════════════════════════════════════════════════════════════════

/-- Symmetry on a concrete asymmetric pair, derived (no `decide`). -/
example : binaryGcdSteps 12 8 = binaryGcdSteps 8 12 := binaryGcdSteps_comm 12 8

/-- The transposed worst-case `(7, 1) = (2^3 - 1, 1)` takes `3` steps. -/
example : binaryGcdSteps 7 1 = 3 := by
  have : (7 : ℕ) = 2 ^ 3 - 1 := by norm_num
  rw [this, binaryGcdSteps_one_right_pow2_sub_one (by norm_num)]

end BinaryGcdOQ01OQ04OQ02
