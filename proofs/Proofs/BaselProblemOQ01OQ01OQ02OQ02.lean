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
* lemmas: 4 reusable + 6 numerical witnesses + Part 4 adds
  `harmonicCubed` (the cubed-harmonic sum H_n^{(3)} = ∑_{k=1}^{n} 1/k^3)
  with base values, non-negativity, monotonicity (4 lemmas), the
  `harmonicCubed_succ` recurrence, and the numerical witness
  `harmonicCubed_two = 9/8`.
* Part 5 (session 4) adds the **per-term integrality bridge**:
  `lcmRange_pow_eq_mul`, `term_lcm_clear_nat`, `term_lcm_clear_cube_nat`,
  `term_lcm_clear_int` — the precise per-term identity that bypasses
  the `Nat.cast_div`/`push_cast` issue that exceeded session 3's
  Docker build time. Together these scaffold the main divisibility
  theorem `harmonicCubed_lcm_clear` for a follow-up session via
  induction on `n` using `harmonicCubed_succ` + the per-term lemmas.
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

/-- **Recurrence**: `H_{n+1}^{(3)} = H_n^{(3)} + 1/(n+1)^3`.

    This is the inductive-step identity for any proof of
    `harmonicCubed_lcm_clear` by induction on `n`: the new contribution
    `1/(n+1)^3` is exactly cleared by the new factor in `lcmRange (n+1)^3`
    via `succ_cube_dvd_lcmRange_succ_cube`. -/
theorem harmonicCubed_succ (n : ℕ) :
    harmonicCubed (n + 1) = harmonicCubed n + (1 : ℚ) / (n + 1) ^ 3 := by
  unfold harmonicCubed
  rw [Finset.sum_range_succ]

/-- `H_2^{(3)} = 1 + 1/8 = 9/8`. -/
theorem harmonicCubed_two : harmonicCubed 2 = 9 / 8 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, harmonicCubed_succ, harmonicCubed_one]
  norm_num

-- =====================================================================
-- PART 5: Per-term integrality (the bridge to harmonicCubed_lcm_clear)
-- =====================================================================

/-- **Per-term integrality (Nat-witness form)**: `0 < k`, `k ≤ n` ⇒
    `∃ m : ℕ, (lcmRange n)^p = m * k^p`.

    This is just `pow_dvd_lcmRange_pow` repackaged with the witness `m`
    extracted explicitly and the multiplication on the *outside* of `k^p`,
    which is the orientation needed for the per-term rational identity
    below. -/
theorem lcmRange_pow_eq_mul {k n p : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∃ m : ℕ, (lcmRange n) ^ p = m * k ^ p := by
  obtain ⟨m, hm⟩ := pow_dvd_lcmRange_pow (p := p) hk hkn
  exact ⟨m, by rw [hm]; ring⟩

/-- **Per-term rational integrality**: `0 < k`, `k ≤ n` ⇒
    `(lcmRange n : ℚ)^p / (k : ℚ)^p ∈ ℕ`.

    This is *exactly* the per-term identity that the next session needs
    to compose `harmonicCubed_lcm_clear` from `Finset.sum_div` (or by
    induction via `harmonicCubed_succ` + this lemma). It bypasses the
    `Nat.cast_div`/`push_cast` issue documented in session 3 by working
    directly with the multiplicative form `(lcmRange n)^p = m * k^p` and
    casting through `Nat → ℚ` (avoiding the `ℕ → ℤ → ℚ` chain that
    `push_cast` aggressively rewrites via `Int.ofNat_div`). -/
theorem term_lcm_clear_nat {k n p : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∃ m : ℕ, (lcmRange n : ℚ) ^ p / (k : ℚ) ^ p = (m : ℚ) := by
  obtain ⟨m, hm⟩ := lcmRange_pow_eq_mul (p := p) hk hkn
  refine ⟨m, ?_⟩
  have hkne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hkpne : (k : ℚ) ^ p ≠ 0 := pow_ne_zero _ hkne
  have hQ : (lcmRange n : ℚ) ^ p = (m : ℚ) * (k : ℚ) ^ p := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hm
    push_cast at this
    exact this
  rw [hQ, mul_div_assoc, div_self hkpne, mul_one]

/-- **Per-term rational integrality (cube form)**: the `p = 3` specialization
    used in `harmonicCubed_lcm_clear`. -/
theorem term_lcm_clear_cube_nat {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∃ m : ℕ, (lcmRange n : ℚ) ^ 3 / (k : ℚ) ^ 3 = (m : ℚ) :=
  term_lcm_clear_nat hk hkn

/-- **Per-term integrality, integer-witness form** for direct combination
    with the `∃ m : ℤ, …` shape used in the parent's
    `denominator_control_factorial`. -/
theorem term_lcm_clear_int {k n p : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∃ m : ℤ, (lcmRange n : ℚ) ^ p / (k : ℚ) ^ p = (m : ℚ) := by
  obtain ⟨m, hm⟩ := term_lcm_clear_nat (p := p) hk hkn
  exact ⟨(m : ℤ), by rw [hm]; push_cast; rfl⟩

/- **Next session target**: prove
   `∃ m : ℤ, (lcmRange n : ℚ)^3 * harmonicCubed n = m`. With
   `term_lcm_clear_cube_nat` now available, the proof is a clean
   induction on `n`:
   - Base `n = 0`: `(lcmRange 0 : ℚ)^3 * harmonicCubed 0 = 1 * 0 = 0`.
   - Step `n → n+1`: use `harmonicCubed_succ` and the structural
     divisibility `lcmRange n ∣ lcmRange (n+1)` (sibling file
     `BaselProblemOQ01OQ01OQ02OQ03.lcmRange_dvd_lcmRange_of_le`, or
     prove a local copy) to lift the IH `(lcmRange n)^3 * harmonicCubed n
     = m` to `(lcmRange (n+1))^3 * harmonicCubed n = q^3 · m` (an
     integer multiple), then add the new term
     `(lcmRange (n+1))^3 / (n+1)^3 = m₂` from `term_lcm_clear_cube_nat`.

   This is the H_n^{(3)} half of the van der Poorten denominator
   analysis for `denominator_control` (route F). Combined with a
   separate alternating-bilinear lemma it discharges the `denominator_control`
   axiom in `Proofs/BaselProblemOQ01OQ01OQ02.lean` (line 385). -/

end BaselProblemOQ01OQ01OQ02OQ02
