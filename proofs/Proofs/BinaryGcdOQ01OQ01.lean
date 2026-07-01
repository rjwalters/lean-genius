/-
  Binary GCD OQ-01-OQ-01: Total bit-operation cost model for Stein's algorithm.

  The parent file `BinaryGcdOQ01` counts the *number of reduction steps*
  (`binaryGcdSteps`) and bounds it by `2*(log₂ a + log₂ b) + 2` (a Lamé-style
  bound). That is a *unit-cost* model: every step is charged one unit,
  regardless of how large the operands are.

  This file supplies the missing *total cost model* asked for by the open
  question. A single reduction step of the binary GCD — halving an even
  operand, subtracting the smaller odd operand from the larger, or the
  parity/comparison test that selects the branch — touches every bit of the
  current pair `(a, b)`. Its honest bit-operation cost is therefore
  `Nat.size a + Nat.size b`, the combined bit-length of the two operands.
  Accumulating this over the whole recursion gives `binaryGcdCost`.

  Worked example (a = 12, b = 8), following the five reductions of
  `binaryGcdSteps 12 8 = 5`:

      (12,8) both even   cost size 12 + size 8 = 4+4 = 8 → (6,4)
      (6,4)  both even   cost size 6  + size 4 = 3+3 = 6 → (3,2)
      (3,2)  odd/even    cost size 3  + size 2 = 2+2 = 4 → (3,1)
      (3,1)  odd/odd     cost size 3  + size 1 = 2+1 = 3 → (1,1)
      (1,1)  odd/odd     cost size 1  + size 1 = 1+1 = 2 → (1,0)

  so `binaryGcdCost 12 8 = 8+6+4+3+2 = 23`, well under the step count 5 times
  the initial bit-length 8 (= 40), and under the quadratic bound below.

  Main results.

  * `binaryGcdCost_le_steps_mul_size`
        binaryGcdCost a b ≤ binaryGcdSteps a b * (Nat.size a + Nat.size b)
    Neither operand ever grows along the recursion (each step halves or
    subtracts), so every step is at least as cheap as the first. The total
    cost is thus bounded by the step count times the *initial* bit-length.

  * `binaryGcdCost_le_quadratic`
        binaryGcdCost a b
          ≤ (2*(log₂ a + log₂ b) + 2) * (log₂ a + log₂ b + 2)
    Composing with the parent's step bound yields the classical
    O((log N)²) total bit-complexity of the binary GCD (Brent 1976,
    Knuth TAOCP 4.5.2).

  All results are axiom-free (only the foundational
  propext / Classical.choice / Quot.sound), 0 sorries, no `native_decide`.

  References:
  - Stein (1967), Binary GCD Algorithm
  - Brent (1976), analysis of the binary GCD
  - Knuth, TAOCP 4.5.2
  - BinaryGcdOQ01.lean (step count `binaryGcdSteps` + Lamé-style bound)
-/
import Mathlib
import Proofs.BinaryGcdOQ01

namespace BinaryGcdOQ01OQ01

open Nat BinaryGcdOQ01

/-- Total bit-operation cost of Stein's binary GCD: each reduction step on the
    current pair `(a, b)` costs `Nat.size a + Nat.size b` bit operations. The
    branch structure mirrors `binaryGcdSteps` exactly. -/
def binaryGcdCost (a b : ℕ) : ℕ :=
  match a, b with
  | 0, _ => 0
  | _, 0 => 0
  | a' + 1, b' + 1 =>
      (Nat.size (a' + 1) + Nat.size (b' + 1)) +
      (if (a' + 1) % 2 = 0 then
          if (b' + 1) % 2 = 0 then
            binaryGcdCost ((a' + 1) / 2) ((b' + 1) / 2)
          else
            binaryGcdCost ((a' + 1) / 2) (b' + 1)
        else if (b' + 1) % 2 = 0 then
          binaryGcdCost (a' + 1) ((b' + 1) / 2)
        else if a' + 1 > b' + 1 then
          binaryGcdCost ((a' + 1 - (b' + 1)) / 2) (b' + 1)
        else
          binaryGcdCost (a' + 1) ((b' + 1 - (a' + 1)) / 2))
  termination_by a + b
  decreasing_by all_goals omega

@[simp] theorem binaryGcdCost_zero_left (b : ℕ) : binaryGcdCost 0 b = 0 :=
  binaryGcdCost.eq_1 b

@[simp] theorem binaryGcdCost_zero_right (a : ℕ) : binaryGcdCost a 0 = 0 := by
  cases a with
  | zero => exact binaryGcdCost.eq_1 0
  | succ a' => exact binaryGcdCost.eq_2 _ (by omega)

/-! ## The core cost bound

Total cost ≤ (step count) × (initial bit-length). The engine is a fuelled
strong induction on `a + b`; in every branch the recursive operands are ≤ the
current operands, so `Nat.size` (monotone) cannot increase, making each step no
more expensive than the first. -/

private theorem binaryGcdCost_le_aux :
    ∀ n a b : ℕ, a + b ≤ n →
      binaryGcdCost a b ≤ binaryGcdSteps a b * (Nat.size a + Nat.size b) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp
  | succ n ih =>
    intro a b h
    rcases a with _ | a'
    · simp
    rcases b with _ | b'
    · simp
    rw [binaryGcdCost.eq_3, binaryGcdSteps.eq_3]
    set S := Nat.size (a' + 1) + Nat.size (b' + 1) with hS
    -- Generic closer for one branch: reduced operands `ra rb` with proofs that
    -- they are ≤ the current operands.
    have close : ∀ ra rb : ℕ, ra + rb ≤ n →
        ra ≤ a' + 1 → rb ≤ b' + 1 →
        S + binaryGcdCost ra rb ≤ (1 + binaryGcdSteps ra rb) * S := by
      intro ra rb hfuel hra hrb
      have ihb := ih ra rb hfuel
      have hmono : Nat.size ra + Nat.size rb ≤ S := by
        have e1 : Nat.size ra ≤ Nat.size (a' + 1) := Nat.size_le_size hra
        have e2 : Nat.size rb ≤ Nat.size (b' + 1) := Nat.size_le_size hrb
        omega
      have step2 : binaryGcdSteps ra rb * (Nat.size ra + Nat.size rb)
          ≤ binaryGcdSteps ra rb * S := by gcongr
      have hexp : (1 + binaryGcdSteps ra rb) * S = S + binaryGcdSteps ra rb * S := by ring
      omega
    split_ifs with h1 h2 h3 h4
    · exact close ((a' + 1) / 2) ((b' + 1) / 2) (by omega)
        (Nat.div_le_self _ _) (Nat.div_le_self _ _)
    · exact close ((a' + 1) / 2) (b' + 1) (by omega)
        (Nat.div_le_self _ _) le_rfl
    · exact close (a' + 1) ((b' + 1) / 2) (by omega)
        le_rfl (Nat.div_le_self _ _)
    · exact close ((a' + 1 - (b' + 1)) / 2) (b' + 1) (by omega)
        (le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) le_rfl
    · exact close (a' + 1) ((b' + 1 - (a' + 1)) / 2) (by omega)
        le_rfl (le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _))

/-- **Total cost model.** The total bit-operation cost of Stein's binary GCD is
    bounded by the number of reduction steps times the initial combined
    bit-length `Nat.size a + Nat.size b`. -/
theorem binaryGcdCost_le_steps_mul_size (a b : ℕ) :
    binaryGcdCost a b ≤ binaryGcdSteps a b * (Nat.size a + Nat.size b) :=
  binaryGcdCost_le_aux (a + b) a b le_rfl

/-- **Quadratic total bit-complexity.** For positive inputs the total
    bit-operation cost of the binary GCD is `O((log₂ a + log₂ b)²)`: it is
    bounded by `(2·(log₂ a + log₂ b) + 2) · (log₂ a + log₂ b + 2)`. This is the
    classical `O((log N)²)` bit complexity (Brent 1976, Knuth TAOCP 4.5.2),
    now derived from the step bound plus the per-step bit cost. -/
theorem binaryGcdCost_le_quadratic (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    binaryGcdCost a b ≤
      (2 * (Nat.log 2 a + Nat.log 2 b) + 2) * (Nat.log 2 a + Nat.log 2 b + 2) := by
  have hsteps := binaryGcdSteps_le_log a b ha hb
  have hsize : Nat.size a + Nat.size b ≤ Nat.log 2 a + Nat.log 2 b + 2 := by
    have e1 : Nat.size a ≤ Nat.log 2 a + 1 := by
      rw [Nat.size_le]; exact Nat.lt_pow_succ_log_self (by norm_num) a
    have e2 : Nat.size b ≤ Nat.log 2 b + 1 := by
      rw [Nat.size_le]; exact Nat.lt_pow_succ_log_self (by norm_num) b
    omega
  calc binaryGcdCost a b
      ≤ binaryGcdSteps a b * (Nat.size a + Nat.size b) :=
        binaryGcdCost_le_steps_mul_size a b
    _ ≤ (2 * (Nat.log 2 a + Nat.log 2 b) + 2) * (Nat.log 2 a + Nat.log 2 b + 2) := by
        gcongr

end BinaryGcdOQ01OQ01
