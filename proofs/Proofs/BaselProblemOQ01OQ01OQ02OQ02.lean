import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.Coprime.Lemmas
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
* lemmas: 4 reusable lcm/cube + 8 numerical witnesses (`lcmRange 0..7`)
  + lcm positivity + Part 4 adds `harmonicCubed` (the cubed-harmonic
  sum H_n^{(3)} = ∑_{k=1}^{n} 1/k^3) with base values, non-negativity,
  and monotonicity (4 lemmas), plus the **main divisibility theorem**
  `harmonicCubed_lcm_clear`:
      `∃ m : ℤ, (lcmRange n : ℚ)^3 * H_n^{(3)} = m`,
  with strengthened natural-number-witness variant
  `harmonicCubed_lcm_clear_nat`. The proof reduces termwise via the
  exactness of `(k+1)^3 ∣ (lcmRange n)^3` (`pow_dvd_lcmRange_pow`)
  combined with `Nat.cast_div`, so the rational division
  `(lcmRange n)^3 / (k+1)^3` lifts to a single natural-number quotient.

  This closes the H_n^{(3)} half of the van der Poorten denominator
  analysis for `denominator_control` (route F). The remaining work is
  the alternating-bilinear "second summand"
      `Cnk = ∑_{j=1}^{k} (-1)^(j+1) / (2 j^3 · C(n,j)^2 · C(n+j,j)^2)`,
  which is deferred to a follow-up session.

* Part 5 (Session 5) adds the **binomial-absorption identity**
  `mul_choose_eq_mul_choose_pred`:
      `0 < m → m ≤ n → m * Nat.choose n m = n * Nat.choose (n-1) (m-1)`,
  packaging Mathlib's `Nat.succ_mul_choose_eq` in the convenient
  `m · C(n,m)` form. Together with `dvd_lcmRange`, this exposes
  `m * C(n, m)` as a multiple of `n` (and hence of any `q` dividing
  `n`), which is the entry point for the binomial-denominator
  analysis of the alternating bilinear sum in Session 6 (the second
  summand of the van der Poorten closed form). See the Part 5
  docstring for the planned Session 6 lemma
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n,m) ∣ lcmRange n`,
  which the absorption identity is intended to support.
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

/-- `lcmRange 6 = 60` (the new prime needed at 6 is 3·2 = 6 ∣ 60 already). -/
theorem lcmRange_six : lcmRange 6 = 60 := by decide

/-- `lcmRange 7 = 420 = 7 · 60` (introducing the new prime 7). -/
theorem lcmRange_seven : lcmRange 7 = 420 := by decide

/-- **Positivity of `lcmRange`** (for all `n`, including `n = 0` where
    `lcmRange 0 = 1`).

    Proof: `lcmRange n = (Finset.range n).lcm (· + 1)` is non-zero
    because every value in the family `(· + 1)` is a successor and
    hence non-zero. Apply `Finset.lcm_ne_zero_iff` and conclude via
    `Nat.pos_of_ne_zero`. Mirrors the parent file's `lcmUpTo_pos`
    (which assumes `1 ≤ n`); the present statement is unconditional. -/
theorem lcmRange_pos (n : ℕ) : 0 < lcmRange n := by
  unfold lcmRange
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro k _
  exact Nat.succ_ne_zero k

-- =====================================================================
-- PART 4: Harmonic-cube denominator clearing (vdP closed-form prep)
-- =====================================================================

/-- The cubed-harmonic sum H_n^{(3)} = ∑_{k=1}^{n} 1/k^3 (as a rational).

    This appears in the van der Poorten closed form for the Apéry
    a-sequence
    `aₙ = ∑_{k=0}^{n} C(n,k)^2 C(n+k,k)^2 (H_n^{(3)} + cnk)`
    where `cnk` is the alternating bilinear "second-summand" term.
    The identity `H_n^{(3)} · lcmRange n^3 ∈ ℤ` is the first half of the
    denominator analysis required for `denominator_control` along route
    (F) (see this file's header). Reproduced locally to keep this file
    independent of the parent's analytic dependencies. -/
noncomputable def harmonicCubed (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1) ^ 3

/-- **Base value**: `H_0^{(3)} = 0` (empty sum). -/
theorem harmonicCubed_zero : harmonicCubed 0 = 0 := by
  simp [harmonicCubed]

/-- `H_1^{(3)} = 1/1^3 = 1`. -/
theorem harmonicCubed_one : harmonicCubed 1 = 1 := by
  simp [harmonicCubed, Finset.sum_range_succ]

/-- `H_n^{(3)}` is non-negative (each term `1/(k+1)^3 ≥ 0`). -/
theorem harmonicCubed_nonneg (n : ℕ) : 0 ≤ harmonicCubed n := by
  unfold harmonicCubed
  apply Finset.sum_nonneg
  intro k _
  positivity

/-- `H_n^{(3)}` is monotone increasing in `n`. -/
theorem harmonicCubed_mono {m n : ℕ} (h : m ≤ n) :
    harmonicCubed m ≤ harmonicCubed n := by
  unfold harmonicCubed
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro k _ _
  positivity

/-- **Explicit denominator-cleared form**:
    `(lcmRange n)^3 · H_n^{(3)}` equals the cast of an explicit `ℕ`,
    namely `∑ k ∈ Finset.range n, (lcmRange n)^3 / (k + 1)^3`.

    This is the workhorse equation: each summand `(lcmRange n)^3 / (k+1)^3`
    is an *exact* natural-number division because
    `pow_dvd_lcmRange_pow` (Part 2) gives `(k+1)^3 ∣ (lcmRange n)^3` for
    `k + 1 ≤ n`. Hence `Nat.cast_div` lifts the integer witness without loss. -/
theorem harmonicCubed_lcm_clear_nat (n : ℕ) :
    ((lcmRange n : ℕ) : ℚ)^3 * harmonicCubed n =
      ((∑ k ∈ Finset.range n, (lcmRange n)^3 / (k + 1)^3 : ℕ) : ℚ) := by
  unfold harmonicCubed
  rw [Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k + 1 ≤ n := by
    rw [Finset.mem_range] at hk; omega
  have hk_pos : 0 < k + 1 := Nat.succ_pos k
  have hdvd : (k + 1)^3 ∣ (lcmRange n)^3 := pow_dvd_lcmRange_pow hk_pos hk_le
  have hk1ne : (((k + 1)^3 : ℕ) : ℚ) ≠ 0 := by
    have h1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    positivity
  rw [Nat.cast_div hdvd hk1ne, mul_one_div]
  push_cast
  ring

/-- **Denominator clearing for the cubed-harmonic sum**:
    `(lcmRange n)^3 · H_n^{(3)} ∈ ℤ`.

    This is the H_n^{(3)} half of the van der Poorten denominator
    analysis for `denominator_control` (route F). The integer witness
    is the explicit sum
      `∑ k ∈ Finset.range n, (lcmRange n)^3 / (k + 1)^3 : ℕ`,
    each term being integral via `pow_dvd_lcmRange_pow`.

    Combined with a separate alternating-bilinear lemma (the second
    summand of the vdP closed form, deferred to a future session)
    this would discharge the `denominator_control` axiom in
    `Proofs/BaselProblemOQ01OQ01OQ02.lean` (line 385). -/
theorem harmonicCubed_lcm_clear (n : ℕ) :
    ∃ m : ℤ, ((lcmRange n : ℕ) : ℚ)^3 * harmonicCubed n = m := by
  refine ⟨((∑ k ∈ Finset.range n, (lcmRange n)^3 / (k + 1)^3 : ℕ) : ℤ), ?_⟩
  rw [harmonicCubed_lcm_clear_nat]
  push_cast
  rfl

-- =====================================================================
-- PART 5 (Session 5): Binomial-absorption identity (vdP §6 prep)
-- =====================================================================

/-! ### Why this is the next ingredient

The remaining half of the van der Poorten denominator analysis is the
*alternating bilinear* sum
  `Cnk(n, k) = ∑_{m=1}^{k} (-1)^{m-1} / (2 m^3 · C(n, m) · C(n+m, m))`.
After multiplying through by `lcmRange n^3`, every per-term denominator
of the shape `m · C(n, m)` must be absorbed.

The classical absorption mechanism is the binomial identity
  `m · C(n, m) = n · C(n-1, m-1)`,
which says the rising factor `m` in front of `C(n, m)` can always be
swapped for the rising factor `n` in front of the *predecessor* binomial
`C(n-1, m-1)`. Since `n ∣ lcmRange n` (a special case of
`dvd_lcmRange`), this rewriting transforms a term whose denominator is
`m · C(n, m)` into one whose denominator is divisible by `n` — and so
divisible by any `lcmRange n` shifted by one position.

The Session 6 target is therefore
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`.
The present part proves the absorption identity itself
(`mul_choose_eq_mul_choose_pred`), which is a one-line consequence of
Mathlib's `Nat.succ_mul_choose_eq` once the off-by-one in indexing is
discharged. The full divisibility lemma requires combining this
identity with `dvd_lcmRange` *and* a structural argument relating
`C(n-1, m-1)` to a chain of multiplicative cancellations (via Kummer's
theorem on `v_p(C(n, m))` and the digit-sum carry count, or by a
double induction on `(n, m)`); both routes are deferred. -/

/-- **Binomial-absorption identity**: for `0 < m ≤ n`,
    `m · C(n, m) = n · C(n-1, m-1)`.

    A repackaging of Mathlib's
      `Nat.add_one_mul_choose_eq : (n+1) * C(n, k) = C(n+1, k+1) * (k+1)`
    in the more useful "small-to-large" direction with explicit
    predecessors. The substitution is `n' := n - 1`, `k' := m - 1`,
    after which the off-by-ones cancel via `Nat.sub_add_cancel`.

    The statement is the foundational input for Session 6's planned
    `mul_choose_dvd_lcmRange` and (via a chain of such absorptions)
    for the alternating-bilinear half of the van der Poorten
    denominator analysis underlying `denominator_control`. -/
theorem mul_choose_eq_mul_choose_pred {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m * Nat.choose n m = n * Nat.choose (n - 1) (m - 1) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have h := Nat.add_one_mul_choose_eq (n - 1) (m - 1)
  -- h : ((n-1)+1) * C(n-1, m-1) = C((n-1)+1, (m-1)+1) * ((m-1)+1)
  -- Collapse `n-1+1 → n` and `m-1+1 → m` via `Nat.sub_add_cancel`,
  -- then commute the goal's `m * C(n, m)` to align with `h`'s
  -- `C(n, m) * m`.
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at h
  -- h : n * Nat.choose (n - 1) (m - 1) = Nat.choose n m * m
  rw [Nat.mul_comm m (Nat.choose n m)]
  exact h.symm

/-- **Absorption corollary**: `n` divides `m · C(n, m)` whenever
    `0 < m ≤ n`. A direct rewrite via `mul_choose_eq_mul_choose_pred`
    exposes the LHS as `n · C(n-1, m-1)`, which is divisible by `n`. -/
theorem dvd_mul_choose {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    n ∣ m * Nat.choose n m := by
  rw [mul_choose_eq_mul_choose_pred hm hmn]
  exact dvd_mul_right n (Nat.choose (n - 1) (m - 1))

-- =====================================================================
-- PART 6 (Session 6): m=1 and m=2 base cases of mul_choose_dvd_lcmRange
-- =====================================================================

/-! ### Why these base cases

The full Session 6 target is
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`,
which (per the JSON `currentState.blockers`) requires either Kummer's
theorem on `v_p(C(n, m))` or a double `(n, m)` induction via Pascal —
~100-200 lines of work.

The cases `m = 1` and `m = 2` are **direct one- and ten-line proofs**,
useful both as pedagogical anchors and as plug-in lemmas for the
alternating-bilinear vdP analysis when only the first two summand
denominators are needed.

* `m = 1`: `1 · C(n, 1) = n`, and `n ∣ lcmRange n` by `dvd_lcmRange`.
* `m = 2`: by `mul_choose_eq_mul_choose_pred`,
    `2 · C(n, 2) = n · C(n-1, 1) = n · (n-1)`.
  Both `n` and `n-1` divide `lcmRange n` (the latter requires `n ≥ 2`),
  and consecutive integers are coprime, so their product divides
  `lcmRange n` via `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.

Higher `m` (m ≥ 3) does NOT follow this pattern: for `m = 3` the
identity `3 · C(n, 3) = n · (n-1) · (n-2) / 2` introduces an extra
`/2` that consumes one factor of 2 from `n(n-1)(n-2)` — the Kummer /
digit-sum analysis is needed to show the result remains an `lcmRange n`
divisor. -/

/-- **m=1 base case**: `1 · C(n, 1) = n` divides `lcmRange n` for any
    `n ≥ 1`. Direct from `Nat.choose_one_right` + `dvd_lcmRange`. -/
theorem mul_choose_dvd_lcmRange_one {n : ℕ} (hn : 1 ≤ n) :
    1 * Nat.choose n 1 ∣ lcmRange n := by
  rw [Nat.choose_one_right, one_mul]
  exact dvd_lcmRange hn (le_refl n)

/-- **m=2 base case**: `2 · C(n, 2) = n · (n - 1)` divides `lcmRange n`
    for any `n ≥ 2`. Proof: rewrite via `mul_choose_eq_mul_choose_pred`
    + `Nat.choose_one_right` to expose `n · (n - 1)`. Both factors
    divide `lcmRange n` by `dvd_lcmRange`, and consecutive integers
    are coprime (`Nat.Coprime n (n - 1)` via `coprime_self_add_right`
    after `Nat.sub_add_cancel`). Conclude with
    `Nat.Coprime.mul_dvd_of_dvd_of_dvd`. -/
theorem mul_choose_dvd_lcmRange_two {n : ℕ} (hn : 2 ≤ n) :
    2 * Nat.choose n 2 ∣ lcmRange n := by
  have hm : (0 : ℕ) < 2 := by decide
  have hmn : (2 : ℕ) ≤ n := hn
  -- Step 1: 2 · C(n, 2) = n · C(n - 1, 1) = n · (n - 1).
  -- After applying `mul_choose_eq_mul_choose_pred`, the index `(2 - 1)`
  -- reduces definitionally to `1`, so we can plug in `Nat.choose_one_right`
  -- via `show` to align the goal shape before rewriting.
  rw [mul_choose_eq_mul_choose_pred hm hmn]
  show n * Nat.choose (n - 1) 1 ∣ lcmRange n
  rw [Nat.choose_one_right]
  -- Goal: n * (n - 1) ∣ lcmRange n
  have hn_pos : 0 < n := lt_of_lt_of_le hm hmn
  have hn1_pos : 0 < n - 1 := by omega
  have hn1_le : n - 1 ≤ n := Nat.sub_le n 1
  -- Step 2: n ∣ lcmRange n and (n-1) ∣ lcmRange n.
  have h_n : n ∣ lcmRange n := dvd_lcmRange hn_pos (le_refl n)
  have h_n1 : (n - 1) ∣ lcmRange n := dvd_lcmRange hn1_pos hn1_le
  -- Step 3: Coprime n (n - 1) — consecutive integers are coprime.
  have hcop : Nat.Coprime n (n - 1) := by
    -- Rewrite `n = (n - 1) + 1`. Goal: `Coprime ((n-1) + 1) (n - 1)`.
    -- Symmetrise to `Coprime (n-1) ((n-1) + 1)`, then apply
    -- `coprime_self_add_right : Coprime m (m + k) ↔ Coprime m k` with
    -- `k = 1`, finishing via `coprime_one_right : Coprime _ 1`.
    have hrewrite : n = (n - 1) + 1 := by omega
    rw [hrewrite]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm
  -- Step 4: n · (n - 1) ∣ lcmRange n via the coprime mul_dvd lemma.
  exact hcop.mul_dvd_of_dvd_of_dvd h_n h_n1

-- =====================================================================
-- PART 7 (Session 7): Algebraic identities for the m=3 case
-- =====================================================================

/-! ### Why these identities

Session 6 closed `m = 1, 2` of `mul_choose_dvd_lcmRange`. The next step
is `m = 3`. The general `mul_choose_dvd_lcmRange` (m ≥ 3) requires
Kummer's theorem on `v_p(C(n, m))` or a double `(n, m)` induction. As an
**algebraic foundation** for either route, this section provides two
short identities that pin down the structure of `3 · C(n, 3)`:

1. `three_mul_choose_three_eq` (one-line, no hypotheses besides `3 ≤ n`):
   `3 · C(n, 3) = n · C(n - 1, 2)`. Direct corollary of
   `mul_choose_eq_mul_choose_pred` at `m = 3`.

2. `two_mul_three_mul_choose_three_eq` (algebraic): for `n ≥ 3`,
   `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`. Reduces the m=3
   divisibility question to whether `n(n-1)(n-2)/2 ∣ lcmRange n`.

These identities are the entry-point for Session 8's m=3 work,
independent of which divisibility route is chosen. -/

/-- **m=3 absorption identity**: `3 · C(n, 3) = n · C(n - 1, 2)` for
    `n ≥ 3`. Direct instantiation of `mul_choose_eq_mul_choose_pred`. -/
theorem three_mul_choose_three_eq {n : ℕ} (hn : 3 ≤ n) :
    3 * Nat.choose n 3 = n * Nat.choose (n - 1) 2 :=
  mul_choose_eq_mul_choose_pred (by decide) hn

/-- **m=3 explicit form**: `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`
    for `n ≥ 3`. Combines `three_mul_choose_three_eq` with the m=2
    absorption step `2 · C(n - 1, 2) = (n - 1) · (n - 2)`. The factor
    of 2 on the LHS captures the "extra `/2`" in the Pascal-style
    `C(n, 3) = n(n-1)(n-2)/6` formula. -/
theorem two_mul_three_mul_choose_three_eq {n : ℕ} (hn : 3 ≤ n) :
    2 * (3 * Nat.choose n 3) = n * ((n - 1) * (n - 2)) := by
  rw [three_mul_choose_three_eq hn]
  -- Goal: 2 * (n * C(n - 1, 2)) = n * ((n - 1) * (n - 2))
  rw [show 2 * (n * Nat.choose (n - 1) 2) =
        n * (2 * Nat.choose (n - 1) 2) from by ring]
  -- Apply m=2 absorption to `n - 1`: 2 * C(n-1, 2) = (n-1) * C(n-2, 1).
  have hnm1 : (2 : ℕ) ≤ n - 1 := by omega
  rw [mul_choose_eq_mul_choose_pred (by decide : (0:ℕ) < 2) hnm1]
  -- Goal: n * ((n - 1) * Nat.choose (n - 1 - 1) (2 - 1)) =
  --       n * ((n - 1) * (n - 2))
  rw [show ((n - 1 - 1) : ℕ) = n - 2 from by omega,
      Nat.choose_one_right]

-- =====================================================================
-- PART 8 (Session 8): m=3 divisibility — odd-n case
-- =====================================================================

/-! ### Why this case isolates cleanly

The full m=3 case `3 · C(n, 3) ∣ lcmRange n` requires Kummer's
theorem on `v_2(C(n, 3))` because of the `/2` in
`C(n, 3) = n(n-1)(n-2)/6`. However, when `n` is **odd**, the
analysis collapses to a pure coprime argument:

For `n` odd and `n ≥ 3`:
- `n` and `(n-1)(n-2)` are coprime: `gcd(n, n-1) = 1` always
  (consecutive integers), and `gcd(n, n-2) = 1` because
  `n - (n-2) = 2`, but `n` is odd so the gcd cannot be 2.
- `n ∣ lcmRange n` (Part 1 `dvd_lcmRange`).
- `(n-1)(n-2) = 2 · C(n-1, 2) ∣ lcmRange (n-1) ∣ lcmRange n`
  (Part 6 `mul_choose_dvd_lcmRange_two` + Part 8a monotonicity).
- Coprime `mul_dvd_of_dvd_of_dvd` gives
  `n · (n-1)(n-2) ∣ lcmRange n`.
- By Part 7's `two_mul_three_mul_choose_three_eq`,
  `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`.
- Hence `3 · C(n, 3) ∣ 2 · (3 · C(n, 3)) ∣ lcmRange n`.

The even-n case (Sessions 9+) needs the carry analysis.

This section also ships the standalone `lcmRange_dvd_of_le`
monotonicity helper, used in the proof and reusable in any
chain-of-`lcmRange` argument. -/

/-- **(Part 8a) `lcmRange` monotonicity**: `m ≤ n → lcmRange m ∣ lcmRange n`. -/
theorem lcmRange_dvd_of_le {m n : ℕ} (hmn : m ≤ n) :
    lcmRange m ∣ lcmRange n := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro b hb
  exact Finset.dvd_lcm (Finset.mem_of_subset (Finset.range_mono hmn) hb)

/-- **(Part 8b) m=3 divisibility, odd-n case**: for `n ≥ 3` odd,
    `3 · C(n, 3) ∣ lcmRange n`.

    Coprime assembly: `n` and `(n-1)(n-2)` are coprime (the only
    common factor could be 2, but `n` is odd), and both divide
    `lcmRange n`, so `n · (n-1)(n-2) ∣ lcmRange n`. By Part 7,
    `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`, and any factor divides
    its multiple. -/
theorem mul_choose_dvd_lcmRange_three_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    3 * Nat.choose n 3 ∣ lcmRange n := by
  -- Step 1: n ∣ lcmRange n
  have hn_pos : 0 < n := by omega
  have h_n : n ∣ lcmRange n := dvd_lcmRange hn_pos (le_refl n)
  -- Step 2: 2 · C(n-1, 2) ∣ lcmRange (n-1) ∣ lcmRange n
  have hn1_ge : (2 : ℕ) ≤ n - 1 := by omega
  have h2C : 2 * Nat.choose (n - 1) 2 ∣ lcmRange (n - 1) :=
    mul_choose_dvd_lcmRange_two hn1_ge
  have hmono : lcmRange (n - 1) ∣ lcmRange n :=
    lcmRange_dvd_of_le (Nat.sub_le n 1)
  -- Rewrite 2 · C(n-1, 2) = (n-1)(n-2) using the absorption identity
  have h2C_eq : 2 * Nat.choose (n - 1) 2 = (n - 1) * (n - 2) := by
    rw [mul_choose_eq_mul_choose_pred (by decide : (0:ℕ) < 2) hn1_ge,
        show ((n - 1 - 1) : ℕ) = n - 2 from by omega,
        Nat.choose_one_right]
  have h_n1n2 : (n - 1) * (n - 2) ∣ lcmRange n := by
    rw [← h2C_eq]; exact h2C.trans hmono
  -- Step 3: n is coprime to (n-1) and to (n-2), hence to their product
  have hcop_n_n1 : Nat.Coprime n (n - 1) := by
    have hrewrite : n = (n - 1) + 1 := by omega
    rw [hrewrite]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm
  have hcop_n_n2 : Nat.Coprime n (n - 2) := by
    have hrewrite : n = (n - 2) + 2 := by omega
    rw [hrewrite]
    refine (Nat.coprime_self_add_right.mpr ?_).symm
    refine Nat.Coprime.symm ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2dvd
    rcases hodd with ⟨k, hk⟩
    rcases h2dvd with ⟨m, hm⟩
    omega
  have hcop_prod : Nat.Coprime n ((n - 1) * (n - 2)) :=
    hcop_n_n1.mul_right hcop_n_n2
  -- Step 4: n · (n-1)(n-2) ∣ lcmRange n by coprime mul-dvd
  have h_prod : n * ((n - 1) * (n - 2)) ∣ lcmRange n :=
    hcop_prod.mul_dvd_of_dvd_of_dvd h_n h_n1n2
  -- Step 5: rewrite n · (n-1)(n-2) = 2 · (3 · C(n, 3)) (Part 7)
  rw [← two_mul_three_mul_choose_three_eq hn] at h_prod
  -- h_prod : 2 * (3 * C(n, 3)) ∣ lcmRange n
  -- Step 6: 3 · C(n, 3) divides its own multiple by 2
  exact (dvd_mul_left (3 * Nat.choose n 3) 2).trans h_prod

-- =====================================================================
-- PART 9 (Session 10): m=3 helper — double-n algebraic identity
-- =====================================================================

/-- **(Part 9) Double-n m=3 identity**: for `m ≥ 2`,
    `3 · C(2m, 3) = (2m) · (2m - 1) · (m - 1)`.

    Derived from Part 7 `two_mul_three_mul_choose_three_eq` by
    instantiating `n := 2m` and absorbing the `2` into the
    `(2m - 2)` factor (`2m - 2 = 2(m - 1)`).

    This is the uniform algebraic identity used by both
    `mul_choose_dvd_lcmRange_three_double_even` (Part 10a) and
    `mul_choose_dvd_lcmRange_three_double_odd` (Part 10b). The two
    sub-cases differ only in how they regroup these three factors. -/
theorem three_mul_choose_three_eq_of_double {m : ℕ} (hm : 2 ≤ m) :
    3 * Nat.choose (2 * m) 3 = 2 * m * (2 * m - 1) * (m - 1) := by
  have h2m : 3 ≤ 2 * m := by omega
  have h7 := two_mul_three_mul_choose_three_eq h2m
  -- h7 : 2 * (3 * C(2m, 3)) = (2 * m) * ((2 * m - 1) * (2 * m - 2))
  have hsub : (2 * m - 2 : ℕ) = 2 * (m - 1) := by omega
  rw [hsub] at h7
  have hrhs : (2 * m) * ((2 * m - 1) * (2 * (m - 1))) =
              2 * (2 * m * (2 * m - 1) * (m - 1)) := by ring
  rw [hrhs] at h7
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h7

-- =====================================================================
-- PART 10 (Session 10): m=3 divisibility — even-n case + full theorem
-- =====================================================================

/-! ### Coprime-decomposition strategy (S9 finding, S10 implementation)

For `n` even, write `n = 2m`. Then `3 · C(n, 3) = (2m)(2m-1)(m-1)`
by Part 9. Dispatch on parity of `m`:

* `m` even (`n ≡ 0 (mod 4)`): factorization `(2m)(2m-1)(m-1)`.
  Coprime checks: `gcd(2m, 2m-1) = 1` (consecutive);
  `gcd(2m, m-1) = 1` (`m` even ⇒ `m-1` odd; gcd | 2 forces gcd = 1);
  `gcd(2m-1, m-1) = 1` (`2m-1 = 1 + 2(m-1)`).

* `m` odd (`n ≡ 2 (mod 4)`): regroup
  `(2m)(2m-1)(m-1) = m(2m-1)(2m-2)` (via `2m(m-1) = m · 2(m-1)`).
  Coprime checks: `gcd(m, 2m-1) = 1` (`gcd | 2m - (2m-1) = 1`);
  `gcd(m, 2m-2) = 1` (`m` odd ⇒ `gcd | 2` and `gcd | m` ⇒ gcd = 1);
  `gcd(2m-1, 2m-2) = 1` (consecutive).

The S9 plan corrects S8's earlier claim that the `n ≡ 2 (mod 4)`
case "probably needs Kummer" — the re-grouping closes both
sub-cases without Kummer. -/

private lemma three_factors_dvd_lcmRange {a b c n : ℕ}
    (hap : 0 < a) (han : a ≤ n)
    (hbp : 0 < b) (hbn : b ≤ n)
    (hcp : 0 < c) (hcn : c ≤ n)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c)
    (hbc : Nat.Coprime b c) :
    a * b * c ∣ lcmRange n := by
  have ha : a ∣ lcmRange n := dvd_lcmRange hap han
  have hb : b ∣ lcmRange n := dvd_lcmRange hbp hbn
  have hc : c ∣ lcmRange n := dvd_lcmRange hcp hcn
  have hab_dvd : a * b ∣ lcmRange n :=
    hab.mul_dvd_of_dvd_of_dvd ha hb
  have habc : Nat.Coprime (a * b) c := (hac.symm.mul_right hbc.symm).symm
  exact habc.mul_dvd_of_dvd_of_dvd hab_dvd hc

/-- **(Part 10a) m=3 divisibility, double-of-even**: for `m ≥ 2` and
    `Even m`, `3 · C(2m, 3) ∣ lcmRange (2m)`.

    Coprime triple `(2m, 2m-1, m-1)`. The crux of "Even m" is
    `gcd(2m, m-1) = 1`: the gcd divides `2m - 2(m-1) = 2`, and
    `m - 1` is odd (forced by `Even m`), so the gcd is odd and
    hence 1. -/
theorem mul_choose_dvd_lcmRange_three_double_even {m : ℕ}
    (hm : 2 ≤ m) (heven : Even m) :
    3 * Nat.choose (2 * m) 3 ∣ lcmRange (2 * m) := by
  rw [three_mul_choose_three_eq_of_double hm]
  refine three_factors_dvd_lcmRange (by omega) (le_refl _)
    (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
  · -- Coprime (2 * m) (2 * m - 1)  (consecutive)
    have hrw : 2 * m = (2 * m - 1) + 1 := by omega
    rw [hrw]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm
  · -- Coprime (2 * m) (m - 1)  (needs Even m)
    show Nat.gcd (2 * m) (m - 1) = 1
    have h_gcd_dvd_2 : Nat.gcd (2 * m) (m - 1) ∣ 2 := by
      have h1 := Nat.gcd_dvd_left (2 * m) (m - 1)
      have h2 := Nat.gcd_dvd_right (2 * m) (m - 1)
      have h3 : Nat.gcd (2 * m) (m - 1) ∣ 2 * (m - 1) := h2.mul_left 2
      have h_diff : Nat.gcd (2 * m) (m - 1) ∣ (2 * m - 2 * (m - 1)) :=
        Nat.dvd_sub h1 h3
      have h_eq : (2 * m - 2 * (m - 1) : ℕ) = 2 := by omega
      rw [h_eq] at h_diff
      exact h_diff
    have h_not_2_dvd : ¬ (2 ∣ Nat.gcd (2 * m) (m - 1)) := by
      intro h
      have hdvd : 2 ∣ m - 1 := h.trans (Nat.gcd_dvd_right _ _)
      rcases heven with ⟨j, hj⟩
      rcases hdvd with ⟨k, hk⟩
      omega
    have h_pos : 0 < Nat.gcd (2 * m) (m - 1) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have h_le2 : Nat.gcd (2 * m) (m - 1) ≤ 2 :=
      Nat.le_of_dvd (by decide) h_gcd_dvd_2
    by_contra hne
    have hgcd_eq_2 : Nat.gcd (2 * m) (m - 1) = 2 := by omega
    exact h_not_2_dvd (by rw [hgcd_eq_2])
  · -- Coprime (2 * m - 1) (m - 1)  (`2m - 1 = 1 + 2(m - 1)`)
    show Nat.gcd (2 * m - 1) (m - 1) = 1
    have hrw : 2 * m - 1 = 1 + 2 * (m - 1) := by omega
    rw [hrw, Nat.gcd_add_mul_right_left]
    exact Nat.gcd_one_left _

/-- **(Part 10b) m=3 divisibility, double-of-odd**: for `m ≥ 2` and
    `Odd m`, `3 · C(2m, 3) ∣ lcmRange (2m)`.

    Regroups Part 9's `(2m)(2m-1)(m-1)` as `m(2m-1)(2m-2)`, then
    coprime triple checks. The crux of "Odd m" is `gcd(m, 2m-2) = 1`:
    the gcd divides `2m - (2m-2) = 2`, and `m` is odd, so the gcd
    is odd and hence 1. -/
theorem mul_choose_dvd_lcmRange_three_double_odd {m : ℕ}
    (hm : 2 ≤ m) (hodd : Odd m) :
    3 * Nat.choose (2 * m) 3 ∣ lcmRange (2 * m) := by
  rw [three_mul_choose_three_eq_of_double hm]
  -- Regroup: 2*m * (2*m - 1) * (m - 1) = m * (2*m - 1) * (2*m - 2)
  have hregroup :
      2 * m * (2 * m - 1) * (m - 1) = m * (2 * m - 1) * (2 * m - 2) := by
    have h22 : (2 * m - 2 : ℕ) = 2 * (m - 1) := by omega
    rw [h22]; ring
  rw [hregroup]
  refine three_factors_dvd_lcmRange (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
  · -- Coprime m (2 * m - 1)  (gcd | m ⇒ gcd | 2m ⇒ gcd | 2m - (2m-1) = 1)
    show Nat.gcd m (2 * m - 1) = 1
    have h1 := Nat.gcd_dvd_left m (2 * m - 1)
    have h2 := Nat.gcd_dvd_right m (2 * m - 1)
    have h3 : Nat.gcd m (2 * m - 1) ∣ 2 * m := h1.mul_left 2
    have h_diff : Nat.gcd m (2 * m - 1) ∣ (2 * m - (2 * m - 1)) :=
      Nat.dvd_sub h3 h2
    have heq : (2 * m - (2 * m - 1) : ℕ) = 1 := by omega
    rw [heq] at h_diff
    exact Nat.eq_one_of_dvd_one h_diff
  · -- Coprime m (2 * m - 2)  (needs Odd m)
    show Nat.gcd m (2 * m - 2) = 1
    have h_gcd_dvd_2 : Nat.gcd m (2 * m - 2) ∣ 2 := by
      have h1 := Nat.gcd_dvd_left m (2 * m - 2)
      have h2 := Nat.gcd_dvd_right m (2 * m - 2)
      have h3 : Nat.gcd m (2 * m - 2) ∣ 2 * m := h1.mul_left 2
      have h_diff : Nat.gcd m (2 * m - 2) ∣ (2 * m - (2 * m - 2)) :=
        Nat.dvd_sub h3 h2
      have h_eq : (2 * m - (2 * m - 2) : ℕ) = 2 := by omega
      rw [h_eq] at h_diff
      exact h_diff
    have h_not_2_dvd : ¬ (2 ∣ Nat.gcd m (2 * m - 2)) := by
      intro h
      have hdvd : 2 ∣ m := h.trans (Nat.gcd_dvd_left _ _)
      rcases hodd with ⟨k, hk⟩
      rcases hdvd with ⟨l, hl⟩
      omega
    have h_pos : 0 < Nat.gcd m (2 * m - 2) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have h_le2 : Nat.gcd m (2 * m - 2) ≤ 2 :=
      Nat.le_of_dvd (by decide) h_gcd_dvd_2
    by_contra hne
    have hgcd_eq_2 : Nat.gcd m (2 * m - 2) = 2 := by omega
    exact h_not_2_dvd (by rw [hgcd_eq_2])
  · -- Coprime (2 * m - 1) (2 * m - 2)  (consecutive)
    have hrw : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    rw [hrw]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm

/-- **(Part 10c) m=3 divisibility, even-n case**: for `n ≥ 4` and
    `Even n`, `3 · C(n, 3) ∣ lcmRange n`.

    Dispatches to Part 10a / 10b on parity of `m := n / 2`. -/
theorem mul_choose_dvd_lcmRange_three_even {n : ℕ}
    (hn : 4 ≤ n) (heven : Even n) :
    3 * Nat.choose n 3 ∣ lcmRange n := by
  rcases heven with ⟨m, hm⟩  -- hm : n = m + m
  have hn_eq : n = 2 * m := by omega
  have hm_ge : 2 ≤ m := by omega
  rw [hn_eq]
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · exact mul_choose_dvd_lcmRange_three_double_even hm_ge hm_even
  · exact mul_choose_dvd_lcmRange_three_double_odd hm_ge hm_odd

/-- **(Part 10d) m=3 divisibility, full theorem**: for `n ≥ 3`,
    `3 · C(n, 3) ∣ lcmRange n`.

    Combines Part 8b (`mul_choose_dvd_lcmRange_three_odd`, S8) and
    Part 10c (`mul_choose_dvd_lcmRange_three_even`, S10) on parity
    of `n`. This is the m=3 case of the general target
    `mul_choose_dvd_lcmRange`, which remains open for m ≥ 4
    (genuine Kummer-or-double-induction territory). -/
theorem mul_choose_dvd_lcmRange_three {n : ℕ} (hn : 3 ≤ n) :
    3 * Nat.choose n 3 ∣ lcmRange n := by
  rcases Nat.even_or_odd n with heven | hodd
  · -- n even, n ≥ 3 ⇒ n ≥ 4
    have hn_4 : 4 ≤ n := by
      rcases heven with ⟨k, hk⟩
      omega
    exact mul_choose_dvd_lcmRange_three_even hn_4 heven
  · exact mul_choose_dvd_lcmRange_three_odd hn hodd

-- =====================================================================
-- PART 11 (Session 15): A.1 — `C(n, k) ∣ lcmRange n` via factorization
-- =====================================================================

/-! ### Why this lemma (path A.1)

The full m ≥ 3 case of `mul_choose_dvd_lcmRange : m · C(n,m) ∣ lcmRange n`
requires either Kummer's theorem on `v_p(m · C(n,m))` (path A.2) or a
double `(n, m)` induction. Before tackling A.2, this lemma discharges
the simpler analogue without the `m` factor:

  `choose_dvd_lcmRange : 0 < n → k ≤ n → C(n, k) ∣ lcmRange n`.

The proof factors `C(n, k)` into its prime-power decomposition via
`Nat.prod_pow_factorization_choose`, then uses
`Finset.prod_dvd_of_isRelPrime` to lift a per-prime-power divisibility
witness through the product. The per-prime-power witness combines
`Nat.pow_factorization_choose_le` (prime-power bound `p^v_p ≤ n`)
with the local `dvd_lcmRange`. Pairwise coprimality of the
prime-power factors comes from `Nat.coprime_pow_primes` (distinct
primes have coprime powers) translated to `IsRelPrime` via
`Nat.coprime_iff_isRelPrime`.

Pinned bearers (Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
re-verified by Session 14 STATE-SYNC §3, §4, §5):
* `Nat.prod_pow_factorization_choose` — Mathlib/Data/Nat/Choose/Factorization.lean:267
* `Nat.pow_factorization_choose_le` — Mathlib/Data/Nat/Choose/Factorization.lean:196
* `Nat.factorization_eq_zero_of_not_prime` — Mathlib/Data/Nat/Factorization/Defs.lean:129
* `Nat.coprime_iff_isRelPrime` — Mathlib/Data/Nat/GCD/Basic.lean:218
* `Nat.coprime_pow_primes` — Mathlib/Data/Nat/Prime/Basic.lean:200
* `Finset.prod_dvd_of_isRelPrime` — Mathlib/RingTheory/Coprime/Lemmas.lean:252
* `isRelPrime_one_left` / `isRelPrime_one_right` —
   Mathlib/Algebra/Divisibility/Units.lean:166-167
* `DecompositionMonoid ℕ` instance via `[Nonempty (GCDMonoid ℕ)]` —
   Mathlib/Algebra/GCDMonoid/Basic.lean:493 (in scope via the
   `Mathlib.Algebra.GCDMonoid.Finset` import already at the file top).

This is the A.1 ACT planned in Session 12 PREP, audited in Session 13
PREP, and given a GREEN readiness gate in Session 14 STATE-SYNC.
The next-action after this is A.2 (`mul_choose_dvd_lcmRange`), which
requires bridging `factorization` and `emultiplicity` via Kummer's
theorem. -/

/-- **(Part 11) `C(n, k) ∣ lcmRange n`**: for `0 < n` and `k ≤ n`,
    the binomial coefficient `C(n, k)` divides `lcmRange n`.

    Proof: decompose `C(n, k) = ∏_{p ≤ n} p ^ v_p(C(n, k))` via
    `Nat.prod_pow_factorization_choose`, then use
    `Finset.prod_dvd_of_isRelPrime` reducing to two sub-goals:
    pairwise `IsRelPrime` on the prime-power factors (sub-goal 1),
    and per-prime-power divisibility into `lcmRange n` (sub-goal 2).

    Sub-goal 1: distinct primes have coprime powers
    (`Nat.coprime_pow_primes`), and the `Coprime` ↔ `IsRelPrime`
    bridge on ℕ is `Nat.coprime_iff_isRelPrime`. The `v = 0` edge
    cases reduce to `IsRelPrime 1 _` via `pow_zero`.

    Sub-goal 2: when `v_p(C(n, k)) = 0` the factor is `1`; otherwise
    `p` is prime (via `Nat.factorization_eq_zero_of_not_prime`
    contrapositive) and `p ^ v_p ≤ n` (by
    `Nat.pow_factorization_choose_le`), so the local `dvd_lcmRange`
    applies. -/
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_isRelPrime
  · -- Sub-goal 1: pairwise `IsRelPrime` on the prime-power factors.
    intro p _ q _ hne
    simp only [Function.onFun]
    by_cases hv_p : (Nat.choose n k).factorization p = 0
    · rw [hv_p, pow_zero]
      exact isRelPrime_one_left
    by_cases hv_q : (Nat.choose n k).factorization q = 0
    · rw [hv_q, pow_zero]
      exact isRelPrime_one_right
    -- Both v_p, v_q > 0 ⇒ both p, q are primes.
    have hpp : p.Prime := by
      by_contra h
      exact hv_p (Nat.factorization_eq_zero_of_not_prime _ h)
    have hqq : q.Prime := by
      by_contra h
      exact hv_q (Nat.factorization_eq_zero_of_not_prime _ h)
    -- Distinct primes have coprime powers (Nat.coprime_pow_primes),
    -- then translate Coprime ⟶ IsRelPrime on ℕ.
    have hcop : Nat.Coprime (p ^ (Nat.choose n k).factorization p)
        (q ^ (Nat.choose n k).factorization q) :=
      Nat.coprime_pow_primes _ _ hpp hqq hne
    exact Nat.coprime_iff_isRelPrime.mp hcop
  · -- Sub-goal 2: each prime-power factor divides `lcmRange n`.
    intro p _
    by_cases hv : (Nat.choose n k).factorization p = 0
    · rw [hv, pow_zero]
      exact one_dvd _
    -- v_p > 0 ⇒ p prime ⇒ p^v_p > 0 ⇒ apply dvd_lcmRange with the
    -- Mathlib bound `pow_factorization_choose_le`.
    have hpp : p.Prime := by
      by_contra h
      exact hv (Nat.factorization_eq_zero_of_not_prime _ h)
    have hpow_pos : 0 < p ^ (Nat.choose n k).factorization p :=
      pow_pos hpp.pos _
    have hpow_le : p ^ (Nat.choose n k).factorization p ≤ n :=
      Nat.pow_factorization_choose_le hn
    exact dvd_lcmRange hpow_pos hpow_le

section Part12
/-! ## Part 12 (Session 20 ACT) — `pow_factorization_mul_choose_le`

Per-prime upper bound for the prime-power factorization of `m * C(n, m)`.
Generalizes `Nat.pow_factorization_choose_le` (S15 framework) to the
m-prefactored case. Consumed by Part 13 (S21 ACT, `mul_choose_dvd_lcmRange`)
via prime-power decomposition.

The naive bound `v_p(m) + ⌊log_p (n-1)⌋ ≤ ⌊log_p n⌋` FAILS in general
(e.g. n=12, m=4, p=2: v_2(4) + log_2(11) = 2 + 3 = 5 > log_2(12) = 3).
The sharp argument observes: when `v_p(m) = a`, the bottom `a` base-p
digits of m are 0, so the carry positions in m + (n-m) = n (which by
Kummer count `v_p(C(n, m))`) can only land in positions > a. Hence
`v_p(C(n, m)) ≤ log_p n - v_p(m)`, giving the SHARP `v_p(m·C(n,m)) ≤ log_p n`.

Bypasses the `multiplicity`/`emultiplicity` API by working directly with
`Nat.factorization_choose`'s carry formula and bounding the filter
cardinality by Ico cardinality via a subset argument anchored on
`Nat.Prime.pow_dvd_iff_le_factorization`. Validated on 3 cases (S17 §4.3:
n=12 m=4 p=2, n=16 m=8 p=2 tight, n=8 m=2 p=2 tight).
-/

/-- Per-prime upper bound on `(m * C(n, m)).factorization p`. -/
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p : ℕ} : p ^ ((m * Nat.choose n m).factorization p) ≤ n := by
  have hn : 0 < n := hm.trans_le hmn
  have hC_pos : 0 < Nat.choose n m := Nat.choose_pos hmn
  rw [Nat.factorization_mul hm.ne' hC_pos.ne']
  simp only [Finsupp.add_apply, Pi.add_apply]
  by_cases hp : p.Prime
  · apply Nat.pow_le_of_le_log hn.ne'
    set a : ℕ := m.factorization p with ha
    have ha_le_log : a ≤ Nat.log p n := by
      have h_pa_dvd_m : p ^ a ∣ m :=
        (hp.pow_dvd_iff_le_factorization hm.ne').mpr le_rfl
      have h_pa_le_m : p ^ a ≤ m := Nat.le_of_dvd hm h_pa_dvd_m
      have h_pa_le_n : p ^ a ≤ n := h_pa_le_m.trans hmn
      exact Nat.le_log_of_pow_le hp.one_lt h_pa_le_n
    rw [Nat.factorization_choose hp hmn (Nat.lt_add_one _)]
    set b : ℕ := Nat.log p n with hb
    have h_subset :
        {i ∈ Finset.Ico 1 (b + 1) | p^i ≤ m % p^i + (n - m) % p^i}
          ⊆ Finset.Ico (a + 1) (b + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      obtain ⟨⟨hi_one, hi_hi⟩, hi_cond⟩ := hi
      refine Finset.mem_Ico.mpr ⟨?_, hi_hi⟩
      by_contra h_lt
      push_neg at h_lt
      have hi_le_a : i ≤ a := Nat.lt_succ_iff.mp h_lt
      have h_pi_dvd_m : p ^ i ∣ m :=
        (hp.pow_dvd_iff_le_factorization hm.ne').mpr (hi_le_a.trans (le_of_eq ha.symm))
      have h_m_mod : m % p ^ i = 0 := Nat.mod_eq_zero_of_dvd h_pi_dvd_m
      rw [h_m_mod, Nat.zero_add] at hi_cond
      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos i)))
    have h_card_le : ({i ∈ Finset.Ico 1 (b + 1) | p^i ≤ m % p^i + (n - m) % p^i}).card
        ≤ (Finset.Ico (a + 1) (b + 1)).card :=
      Finset.card_le_card h_subset
    rw [Nat.card_Ico] at h_card_le
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]
    simp
    exact hn

end Part12

end BaselProblemOQ01OQ01OQ02OQ02
