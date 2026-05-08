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

end BaselProblemOQ01OQ01OQ02OQ02
