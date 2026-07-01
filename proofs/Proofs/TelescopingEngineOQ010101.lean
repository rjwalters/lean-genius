/-
  The Universal Telescoping Engine  (generalizing the factorial telescoping sum)

  Source / context: open-question generalization of the gallery entry
    "Factorial Telescoping Sum:  ∑_{k=1}^{n} k·k! = (n+1)! − 1"
  (`factorial-telescoping-sum-oq-01`).  That entry proves one concrete telescoping
  identity by a bespoke induction.  The open question asks:

    Generalize the telescoping engine to
        ∑_{k} (a_{k+1} − a_k)  =  a_{n+1} − a_1
    over an arbitrary (commutative) group, and *recover* the factorial identity
    as the instance a_k = k!.

  Status: VERIFIED target (0 sorries, 0 axioms, no native_decide).

  What this file does:
    1. States the universal additive telescoping law over *any* abelian group,
       both over `range n` (a thin wrapper on Mathlib's `Finset.sum_range_sub`)
       and over the interval `[1,n]` in the exact `a_{n+1} − a_1` shape of the OQ.
    2. Records the multiplicative dual over any commutative group
       (telescoping *products* `∏ a_{k+1}/a_k = a_{n+1}/a_1`).
    3. Recovers the factorial identity `∑_{k=1}^{n} k·k! = (n+1)! − 1` as the
       single instance `a_k = (k! : ℤ)`, then transfers it back to ℕ so that the
       recovered statement is *literally* the gallery parent's identity.

  The point is structural: the parent's hand-rolled induction is not special —
  it is one evaluation of a universal law, with the telescoping cancellation
  supplied once and for all by the abelian-group engine.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Finset

namespace TelescopingEngine

/-! ### The universal additive telescoping law (arbitrary abelian group) -/

variable {G : Type*} [AddCommGroup G]

/-- **Telescoping over `range n`.**  In any abelian group,
    `∑_{i<n} (a(i+1) − a i) = a n − a 0`.

    This is the engine in its cleanest form; it is exactly Mathlib's
    `Finset.sum_range_sub`, exposed here under a telescoping-specific name. -/
theorem telescope_range (a : ℕ → G) (n : ℕ) :
    ∑ i ∈ range n, (a (i + 1) - a i) = a n - a 0 :=
  Finset.sum_range_sub a n

/-- **Telescoping over the interval `[1,n]`.**  In any abelian group,
    `∑_{k=1}^{n} (a(k+1) − a k) = a(n+1) − a 1`.

    This is the exact shape asked for by the open question: the lower index is
    `k = 1` and the collapsed value is `a_{n+1} − a_1`. -/
theorem telescope_Icc (a : ℕ → G) (n : ℕ) :
    ∑ k ∈ Icc 1 n, (a (k + 1) - a k) = a (n + 1) - a 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      abel

/-! ### The multiplicative dual (arbitrary commutative group) -/

/-- **Telescoping products over `[1,n]`.**  In any commutative group,
    `∏_{k=1}^{n} (a(k+1) / a k) = a(n+1) / a 1`.

    The multiplicative mirror of `telescope_Icc`; together they show the engine
    is really a statement about a group operation, not about numbers. -/
theorem telescope_prod_Icc {H : Type*} [CommGroup H] (a : ℕ → H) (n : ℕ) :
    ∏ k ∈ Icc 1 n, (a (k + 1) / a k) = a (n + 1) / a 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      group

/-! ### Recovering the factorial identity as an instance -/

/-- The factorial difference, over ℤ: `(k+1)! − k! = k·k!`.
    This is the pointwise cancellation term that makes `a_k = k!` telescope. -/
theorem factorial_diff (k : ℕ) :
    ((k + 1)! : ℤ) - (k ! : ℤ) = (k : ℤ) * (k ! : ℤ) := by
  have : ((k + 1)! : ℤ) = (k + 1 : ℤ) * (k ! : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [this]; ring

/-- **Factorial identity over ℤ, as a telescoping instance.**
    Setting `a_k = (k! : ℤ)` in `telescope_Icc` gives
    `∑_{k=1}^{n} k·k! = (n+1)! − 1`. -/
theorem sum_Icc_mul_factorial_int (n : ℕ) :
    ∑ k ∈ Icc 1 n, ((k : ℤ) * (k ! : ℤ)) = ((n + 1)! : ℤ) - 1 := by
  have h := telescope_Icc (fun k => ((k ! : ℤ))) n
  calc ∑ k ∈ Icc 1 n, ((k : ℤ) * (k ! : ℤ))
      = ∑ k ∈ Icc 1 n, (((k + 1)! : ℤ) - (k ! : ℤ)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [factorial_diff]
    _ = ((n + 1)! : ℤ) - (1 ! : ℤ) := h
    _ = ((n + 1)! : ℤ) - 1 := by norm_num

/-- **Recovered gallery identity (over ℕ).**  `∑_{k=1}^{n} k·k! = (n+1)! − 1`.

    This is verbatim the statement of the parent entry
    `factorial-telescoping-sum-oq-01`, now obtained purely as the `a_k = k!`
    instance of the universal telescoping engine rather than by a bespoke
    induction. -/
theorem sum_Icc_mul_factorial (n : ℕ) :
    ∑ k ∈ Icc 1 n, k * k ! = (n + 1)! - 1 := by
  have hz := sum_Icc_mul_factorial_int n
  have key : ((∑ k ∈ Icc 1 n, k * k ! : ℕ) : ℤ) = ((n + 1)! : ℤ) - 1 := by
    push_cast
    exact hz
  have hpos : 1 ≤ (n + 1)! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  omega

-- Sanity checks (small concrete values), matching the parent entry.
example : ∑ k ∈ Icc 1 4, k * k ! = 119 := by decide   -- 5! − 1 = 119
example : ∑ k ∈ Icc 1 5, k * k ! = 719 := by decide    -- 6! − 1 = 719

end TelescopingEngine
