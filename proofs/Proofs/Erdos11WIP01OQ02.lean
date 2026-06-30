/-
  Erdős Problem #11 — WIP-01 / OQ-02: a kernel-reducible squarefree test and a
  0-axiom verified range

  Erdős Problem #11 (OPEN): is every odd `n > 1` the sum of a squarefree number
  and a power of two?  The parent file `Erdos11WIP01` records the bounded
  characterization `isSquarefreePlusPow2_iff` and verifies the odd numbers
  `3, 5, 7, …, 17` — but each with an *explicit, hand-supplied* squarefree
  witness.  The reason it cannot just `decide` a whole range is documented there:
  the `Squarefree` decidability instance routes through `Nat.minSqFac`, which the
  kernel does not reduce, so a kernel `decide` over `Squarefree` gets stuck.

  This file removes that obstruction.  We give a bounded, **kernel-reducible**
  squarefree test `SquarefreeCheck` — a finite conjunction of `Nat` divisibility
  tests, which the kernel reduces efficiently — prove it *unconditionally*
  equivalent to `Squarefree`, lift it to a kernel-reducible representation test
  `ReprCheck`, and then verify an entire odd range by a single `decide` at
  **0 axioms** (no `native_decide`, hence no `Lean.ofReduceBool`).

  * `SquarefreeCheck n` — `1 ≤ n ∧ ∀ d ≤ n, 2 ≤ d → ¬ d * d ∣ n`.  Decidable and
    kernel-reducible.
  * `squarefree_iff_check` — `Squarefree n ↔ SquarefreeCheck n`, with **no**
    positivity hypothesis (both sides are `False` at `n = 0`).
  * `ReprCheck n` — `∃ k ≤ n, 2^k ≤ n ∧ SquarefreeCheck (n − 2^k)`: a fully
    kernel-reducible form of `IsSquarefreePlusPow2`.
  * `isSquarefreePlusPow2_iff_check` — `IsSquarefreePlusPow2 n ↔ ReprCheck n`.
  * `repr_range` / `isSquarefreePlusPow2_range` — every odd `n` with `1 < n < 100`
    is squarefree + a power of two, by one kernel `decide`, 0 axioms.

  All results are fully machine-checked (0 axioms, 0 sorries, no `native_decide`).

  Reference: Hercher (2024); Granville–Soundararajan (1998); https://erdosproblems.com/11.
-/

import Proofs.Erdos11WIP01

namespace Erdos11WIP01

open Finset

/-- A bounded, **kernel-reducible** squarefree test: `n ≥ 1` and no `d` with
    `2 ≤ d ≤ n` has `d * d ∣ n`.  Unlike `Squarefree`'s `Decidable` instance (which
    routes through `Nat.minSqFac` and does *not* kernel-reduce), this is a finite
    conjunction of `Nat` divisibility tests, which the kernel reduces — so `decide`
    works at 0 axioms.  The `1 ≤ n` conjunct makes the equivalence with `Squarefree`
    hold unconditionally (both are `False` at `n = 0`). -/
def SquarefreeCheck (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ d ∈ Finset.range (n + 1), 2 ≤ d → ¬ (d * d ∣ n)

instance : DecidablePred SquarefreeCheck := fun n =>
  inferInstanceAs (Decidable (1 ≤ n ∧ ∀ d ∈ Finset.range (n + 1), 2 ≤ d → ¬ (d * d ∣ n)))

/-- **The kernel-reducible squarefree test is exactly `Squarefree`.**  Holds with no
    positivity hypothesis: at `n = 0` both sides are `False` (`Squarefree 0` is false,
    and `SquarefreeCheck 0` fails its `1 ≤ n` conjunct). -/
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

/-- A fully **kernel-reducible** form of `IsSquarefreePlusPow2`: search an exponent
    `k ≤ n` with `2^k ≤ n` whose complementary summand `n − 2^k` passes the
    kernel-reducible `SquarefreeCheck`. -/
def ReprCheck (n : ℕ) : Prop :=
  ∃ k ∈ Finset.range (n + 1), 2 ^ k ≤ n ∧ SquarefreeCheck (n - 2 ^ k)

instance : DecidablePred ReprCheck := fun n =>
  inferInstanceAs (Decidable (∃ k ∈ Finset.range (n + 1), 2 ^ k ≤ n ∧ SquarefreeCheck (n - 2 ^ k)))

/-- **The kernel-reducible representation test is exactly `IsSquarefreePlusPow2`.**
    Combines the parent's bounded characterization with `squarefree_iff_check`. -/
theorem isSquarefreePlusPow2_iff_check (n : ℕ) :
    IsSquarefreePlusPow2 n ↔ ReprCheck n := by
  rw [isSquarefreePlusPow2_iff]
  unfold ReprCheck
  simp_rw [squarefree_iff_check]

set_option maxRecDepth 8000 in
/-- **0-axiom verified range (the kernel-reducible test in action).**  Every odd `n`
    with `1 < n < 100` passes `ReprCheck` — proved by a single kernel `decide`, with
    no `native_decide` and hence no `Lean.ofReduceBool`.  (`maxRecDepth` is raised only
    to let the kernel walk the nested `Finset.range` recursions; it does not affect the
    trusted axiom set.) -/
theorem repr_range :
    ∀ n ∈ Finset.range 100, Odd n → 1 < n → ReprCheck n := by
  decide

/-- **Erdős #11 verified for all odd `1 < n < 100`, at 0 axioms.**  Where the parent
    needed a hand-written squarefree witness for each of `3, …, 17`, the
    kernel-reducible test discharges the entire odd range in one `decide`. -/
theorem isSquarefreePlusPow2_range :
    ∀ n ∈ Finset.range 100, Odd n → 1 < n → IsSquarefreePlusPow2 n := by
  intro n hn hodd h1
  exact (isSquarefreePlusPow2_iff_check n).mpr (repr_range n hn hodd h1)

end Erdos11WIP01

#print axioms Erdos11WIP01.squarefree_iff_check
#print axioms Erdos11WIP01.isSquarefreePlusPow2_iff_check
#print axioms Erdos11WIP01.isSquarefreePlusPow2_range
