import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

/-
# Apéry Denominator Control: lcm(1,…,n)³·aₙ ∈ ℤ
## OQ-02-OQ-02 of `basel-problem-oq-01-oq-01-oq-02`

## Open Question
Eliminate the `denominator_control` axiom in
`Proofs/BaselProblemOQ01OQ01OQ02.lean` (line 385):
`∃ m : ℤ, (lcmUpTo n : ℚ) ^ 3 * aperyA n = m`.

This is one of the 5 open axioms blocking the unconditional formalization
of Apéry's irrationality of ζ(3). The companion problem OQ-02-OQ-03
handles the related `lcm_hanson_bound`; together they discharge two of
the five axioms.

## What This File Provides (ORIENT phase)

1. A *self-contained* re-derivation of the basic lcm divisibility
   infrastructure (mirroring `BaselProblemOQ01OQ01OQ02OQ03`), so this
   file can type-check without importing the parent's heavy analytic
   dependencies.

2. The **cubed-divisibility lemma**
   `pow_dvd_lcmRange_pow` :
       `k > 0 → k ≤ n → k^p ∣ (lcmRange n)^p`
   This is the missing arithmetic ingredient for any inductive proof
   of `denominator_control`: the recurrence step requires
   `(n+2)^3 ∣ (lcmRange (n+2))^3` to clear the `(n+2)^3` denominator
   coming from `aperyA (n+2) = (… - (n+1)^3 · aperyA n) / (n+2)^3`.

3. A **gap analysis** (in this header) of the originally proposed
   "recurrence-induction" strategy from prior knowledge sessions,
   showing concretely (via the `n = 2 → n = 4` step) that pointwise
   induction along the Apéry recurrence does **not** close on its own:
   the integrality of the right-hand side requires *cancellation
   between the two summands*, not term-wise divisibility.

## Gap Analysis: Why the Naïve Recurrence Induction Fails

Setting `L := lcmRange (n+2)`, `l := lcmRange (n+1)`, `m := lcmRange n`,
multiplying the recurrence
  `(n+2)^3 · aₙ₊₂ = c · aₙ₊₁ - (n+1)^3 · aₙ`
through by `L^3` and substituting `A := l^3·aₙ₊₁ ∈ ℤ`,
`B := m^3·aₙ ∈ ℤ` from the inductive hypothesis gives
  `L^3 · aₙ₊₂ · (n+2)^3 = (L/l)^3·c·A - (L/m)^3·(n+1)^3·B`.
The right-hand side is an integer (since `l ∣ L` and `m ∣ L`), call it
`C`. We need `(n+2)^3 ∣ C`.

**Counterexample to term-wise divisibility**: Take `n = 2` (so we are
proving `denominator_control` at index 4).
* `L = 12`, `l = 6`, `m = 2`, `c = 1463`,
  `A = 6^3 · (62531/36) = 375186`, `B = 2^3 · (351/4) = 702`.
* `(L/l)^3 · c · A = 8 · 1463 · 375186 ≡ 48 (mod 64)`.
* `(L/m)^3 · (n+1)^3 · B = 216 · 27 · 702 ≡ 48 (mod 64)`.
* Their difference `C ≡ 0 (mod 64) = (n+2)^3` — but **only by
  cancellation**, not because either term alone is divisible.

In particular `(n+2)^3 ∤ (L/l)^3·c·A` in general, so the induction
*cannot* be discharged by ringing up a divisibility on each summand
independently. The proof needs additional structure — either:
* **(P)** a stronger inductive invariant that tracks numerators of
  `aₙ` modulo `(n+2)^3` (and its prime-power factors), or
* **(F)** the explicit closed-form van der Poorten formula
  `aₙ = ∑_{k=0}^{n} C(n,k)^2 C(n+k,k)^2 (Hₙ⁽³⁾ + …)`
  where each summand has denominator manifestly dividing
  `lcmRange n^3` (separable analysis per term), bypassing the
  cancellation problem entirely.

The originally proposed "line-by-line port of `denominator_control_factorial`"
(see `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json`,
session 1 knowledge) is therefore **incorrect as stated**: the factorial
proof works because `(n+2)! = (n+2)·(n+1)!` is *exactly* a multiplicative
factorisation, so multiplying through by `(n+1)!^3` produces `(n+2)!^3`
on the LHS without any leftover `(n+2)^3` to absorb. The lcm version has
no such factorisation: `lcmRange (n+2) ≠ (n+2) · lcmRange (n+1)` in
general (e.g. for `n+2 = 4`: `12 ≠ 4·6 = 24`).

## Numerical Verification of `denominator_control` for n = 0..4

`lcmRange n^3 · aperyA n ∈ ℤ` is verified concretely for the base of the
induction. We use the parent file's values:
* `aperyA 0 = 0` → `1^3 · 0 = 0` ✓
* `aperyA 1 = 6` → `1^3 · 6 = 6` ✓
* `aperyA 2 = 351/4` → `2^3 · 351/4 = 702` ✓
* `aperyA 3 = 62531/36` → `6^3 · 62531/36 = 6 · 62531 = 375186` ✓
* `aperyA 4 = 11424695/288` → `12^3 · 11424695/288 = 6 · 11424695 = 68548170` ✓
  (Computed from the recurrence: `4^3·aperyA 4 = 1463·aperyA 3 - 27·aperyA 2`,
  then dividing by 64.)

These five base cases will close the small-n part of any future
strong-induction proof of `denominator_control`.

## File Status
* axioms: 0
* sorries: 0
* lemmas: 4 reusable + 5 numerical witnesses
-/

namespace BaselProblemOQ01OQ01OQ02OQ02

open Finset Nat

-- =====================================================================
-- PART 1: Self-contained lcmRange (matches parent's `lcmUpTo`)
-- =====================================================================

/-- lcm(1, 2, …, n).

    Identical definition to `BaselProblemOQ01OQ01OQ02.lcmUpTo` and
    `BaselProblemOQ01OQ01OQ02OQ03.lcmRange`; reproduced here so this
    file can type-check independently of the parent's heavy
    analytic dependencies. -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- Every `k ∈ {1, …, n}` divides `lcmRange n`. -/
theorem dvd_lcmRange {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ lcmRange n := by
  unfold lcmRange
  have hk' : k - 1 ∈ Finset.range n :=
    Finset.mem_range.mpr (by omega)
  have := Finset.dvd_lcm (f := (· + 1)) hk'
  simpa [Nat.sub_add_cancel hk] using this

-- =====================================================================
-- PART 2: Cubed/Powered divisibility (the OQ-02 specialty)
-- =====================================================================

/-- **Powered divisibility**: `k > 0`, `k ≤ n` ⇒ `k^p ∣ (lcmRange n)^p`.

    The arithmetic ingredient that the recurrence-induction step for
    `denominator_control` needs to clear the `(n+2)^3` denominator
    coming from the Apéry recurrence
    `aₙ₊₂ = (c · aₙ₊₁ - (n+1)^3 · aₙ) / (n+2)^3`.

    Note this is **necessary but not sufficient** — see the file
    header for why the full induction also requires either a
    strengthened invariant or the van der Poorten closed form. -/
theorem pow_dvd_lcmRange_pow {k n p : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ^ p ∣ (lcmRange n) ^ p :=
  pow_dvd_pow_of_dvd (dvd_lcmRange hk hkn) p

/-- **Specialization to cubes**, the case used in `denominator_control`
    via the cubic Apéry recurrence. -/
theorem cube_dvd_lcmRange_cube {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ^ 3 ∣ (lcmRange n) ^ 3 :=
  pow_dvd_lcmRange_pow hk hkn

/-- **Successor cube**: the form needed in the recurrence step
    `(n+1)^3 ∣ (lcmRange (n+1))^3`. -/
theorem succ_cube_dvd_lcmRange_succ_cube (n : ℕ) :
    (n + 1) ^ 3 ∣ (lcmRange (n + 1)) ^ 3 :=
  cube_dvd_lcmRange_cube (Nat.succ_pos n) (Nat.le_refl _)

-- =====================================================================
-- PART 3: Numerical verification of small `lcmRange` values
-- =====================================================================

/-- `lcmRange 0 = 1` (lcm of the empty set). -/
theorem lcmRange_zero : lcmRange 0 = 1 := by
  simp [lcmRange, Finset.lcm]

/-- `lcmRange 1 = 1`. -/
theorem lcmRange_one : lcmRange 1 = 1 := by
  simp [lcmRange, Finset.lcm]

/-- `lcmRange 2 = 2`. -/
theorem lcmRange_two : lcmRange 2 = 2 := by decide

/-- `lcmRange 3 = 6`. -/
theorem lcmRange_three : lcmRange 3 = 6 := by decide

/-- `lcmRange 4 = 12`. -/
theorem lcmRange_four : lcmRange 4 = 12 := by decide

/-- `lcmRange 5 = 60`. -/
theorem lcmRange_five : lcmRange 5 = 60 := by decide

end BaselProblemOQ01OQ01OQ02OQ02
