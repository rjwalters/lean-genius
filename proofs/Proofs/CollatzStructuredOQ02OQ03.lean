/-
# OQ-02 OQ-03: Tao's 2019 Almost-All Bound — A Feasibility Anchor

Open question OQ-03 of `collatz-structured-oq-02` (Collatz Cycles):

  "Can Tao's 2019 almost-all result (logarithmic density 1) be formalized in Lean
   using Mathlib's measure theory and ergodic theory libraries?"

Tao (2019, *Forum Math. Pi*, "Almost all orbits of the Collatz map attain almost
bounded values") proved: for every `f : ℕ → ℝ` with `f n → ∞`, the set of starting
values `n` whose orbit minimum `Col_min(n)` drops below `f n` has **logarithmic
density 1**.  This subsumes the classical Terras/Korec "almost all have finite
stopping time" statements and pushes the bound from "below `n`" down to "below any
slowly growing `f`".

## What resists formalization (honest assessment)

Tao's proof is genuinely analytic and is **out of reach of a direct Lean proof
today** (BLOCKED, >> 1000 lines):

  * It runs the Collatz/Syracuse dynamics against a carefully chosen family of
    measures on the 3-adics / on residue classes, and controls the evolution of
    those measures (a transport/coupling argument), establishing that the pushed
    forward measures concentrate.
  * The quantitative heart is a **stable point estimate** obtained from a
    `3`-adic large-deviation / entropy bound, combined with a Fourier-analytic
    input.  Mathlib currently has the general measure-theory and `Tendsto`
    plumbing used below, but not the specialised concentration/transport
    estimates Tao needs; building those is the real cost.

So, mirroring the sibling files `CollatzStructuredOQ02OQ01.lean` (which axiomatized
the Eliahou bound) and `CollatzStructuredOQ02OQ02.lean` (which proved Eliahou's
algebraic core and isolated the finite-check residue), this file:

  * gives a **precise, machine-checkable statement** of Tao's theorem
    (`tao_2019`) so the open question is no longer informal, and the
    "logarithmic density 1" target is pinned down as `HasLogDensityOne`;
  * proves, **unconditionally and axiom-free**, that three large explicit families
    of starting values already satisfy the "drops below itself" conclusion — the
    even numbers, the powers of two, and the odd residue class `n ≡ 1 (mod 4)`
    (`n ≥ 5`) — so the elementary part of the almost-all picture is real Lean
    content, not scaffolding on the axiom.  The even numbers and the class
    `1 + 4ℕ` together already cover three-quarters of the integers via elementary
    dynamics, and the `mod 4` family is the first that exercises the non-trivial
    `3n+1` branch of the map.

References:
- Tao, T. (2019). "Almost all orbits of the Collatz map attain almost bounded
  values." *Forum Math. Pi* 8, e9.
- Terras, R. (1976). "A stopping time problem on the positive integers."
- Korec, I. (1994). "A density estimate for the 3x+1 problem."
-/
import Mathlib

namespace CollatzStructuredOQ02OQ03

open Filter

/-! ## Part I: The Collatz map (self-contained) -/

/-- The Collatz function: `n ↦ n/2` if even, `n ↦ 3n+1` if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- The Collatz map sends positive numbers to positive numbers: `n/2 ≥ 1` for a
positive even `n` and `3n+1 ≥ 1` always.  This keeps `0` out of every orbit. -/
theorem collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

/-- Positivity propagates along the whole orbit: no iterate of a positive start
is ever `0`. -/
theorem collatz_iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact collatz_pos ih

/-! ## Part II: Three explicit families that drop below their start

These are the unconditional, axiom-free part of the almost-all picture: whatever
Tao's analytic argument gives for *almost all* `n`, the even numbers, the powers
of two, and the odd residue class `n ≡ 1 (mod 4)` (`n ≥ 5`) are handled by
elementary explicit dynamics. -/

/-- `n` *attains a value below itself*: some positive number of Collatz steps
takes `n` to a strictly smaller value.  This is the "finite stopping time"
event whose almost-all behaviour Tao controls. -/
def AttainsBelow (n : ℕ) : Prop := ∃ k, 0 < k ∧ collatz^[k] n < n

/-- Every positive **even** number drops below itself in a single step. -/
theorem even_attainsBelow {n : ℕ} (hn : 1 ≤ n) (he : n % 2 = 0) : AttainsBelow n :=
  ⟨1, one_pos, by
    rw [Function.iterate_one, collatz_even he]
    exact Nat.div_lt_self hn (by norm_num)⟩

/-- A power of two collapses to `1` after exactly that many steps:
`collatz^[k] (2^k) = 1`. -/
theorem pow_two_reaches_one (k : ℕ) : collatz^[k] (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hstep : collatz (2 ^ (k + 1)) = 2 ^ k := by
      rw [pow_succ']
      exact collatz_two_mul (2 ^ k)
    rw [hstep, ih]

/-- Every power of two `2^k` with `k ≥ 1` drops below itself (all the way to 1). -/
theorem pow_two_attainsBelow {k : ℕ} (hk : 1 ≤ k) : AttainsBelow (2 ^ k) := by
  refine ⟨k, hk, ?_⟩
  rw [pow_two_reaches_one]
  have h2 : (2 : ℕ) ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
  omega

/-- Every `n ≡ 1 (mod 4)` with `n ≥ 5` drops below itself in exactly three steps:
`4m+1 ↦ 12m+4 ↦ 6m+2 ↦ 3m+1`, and `3m+1 < 4m+1` once `m ≥ 1`.  Unlike the even
numbers and the powers of two, this is a *positive-density* (one-quarter) family of
genuinely **odd** starting values, so it adds new unconditional content beyond the
trivially-even cases: the first Collatz step here is the non-trivial `3n+1` branch. -/
theorem mod_four_one_attainsBelow {n : ℕ} (hn : 5 ≤ n) (h : n % 4 = 1) :
    AttainsBelow n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  refine ⟨3, by norm_num, ?_⟩
  have step1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; ring
  have step2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have step3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      step1, step2, step3]
  omega

/-- Packaging: every positive `n` that is **even** or lies in `1 + 4ℕ` (with `n ≥ 5`)
attains a value below itself.  Together these cover three-quarters of the integers,
all handled by elementary dynamics with no appeal to Tao's axiom. -/
theorem even_or_mod_four_one_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : AttainsBelow n := by
  rcases h with he | ⟨h5, h1⟩
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h5 h1

/-! ## Part III: The orbit minimum and logarithmic density -/

/-- The **orbit minimum** of `n`: the infimum of the values visited by the
Collatz orbit of `n` (including `n` itself).  `Col_min` in Tao's notation. -/
noncomputable def colMin (n : ℕ) : ℕ := sInf {m | ∃ k, collatz^[k] n = m}

/-- The orbit minimum never exceeds the starting value (`k = 0` visits `n`). -/
theorem colMin_le_self (n : ℕ) : colMin n ≤ n :=
  Nat.sInf_le ⟨0, Function.iterate_zero_apply collatz n⟩

/-- The orbit of a power of two reaches `1`, so its orbit minimum is `≤ 1`. -/
theorem colMin_pow_two_le_one (k : ℕ) : colMin (2 ^ k) ≤ 1 :=
  Nat.sInf_le ⟨k, pow_two_reaches_one k⟩

/-- The orbit minimum of a positive start is itself positive: `0` never occurs in
the orbit (`collatz_iterate_pos`), and the orbit is non-empty, so its infimum is
`≥ 1`. -/
theorem colMin_pos {n : ℕ} (hn : 0 < n) : 0 < colMin n := by
  unfold colMin
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Nat.sInf_eq_zero] at h
  rcases h with h0 | hempty
  · obtain ⟨k, hk⟩ := h0
    have := collatz_iterate_pos hn k
    rw [hk] at this
    exact absurd this (lt_irrefl 0)
  · have hmem : n ∈ {m | ∃ k, collatz^[k] n = m} :=
      ⟨0, Function.iterate_zero_apply collatz n⟩
    rw [hempty] at hmem
    exact hmem

/-- Sharpening `colMin_pow_two_le_one`: the orbit minimum of `2^k` is **exactly**
`1` (the orbit hits `1` and, being positive, never goes lower). -/
theorem colMin_pow_two_eq_one (k : ℕ) : colMin (2 ^ k) = 1 := by
  have hle := colMin_pow_two_le_one k
  have hpos := colMin_pos (n := 2 ^ k) (by positivity)
  omega

/-- **Bridge between Parts II and III.**  Any number that attains a value below
itself has orbit minimum strictly below its start: `colMin n < n`.  This connects
the explicit drop-below families to Tao's `Col_min` predicate (the `f n = n`
specialisation). -/
theorem attainsBelow_colMin_lt {n : ℕ} (h : AttainsBelow n) : colMin n < n := by
  obtain ⟨k, _, hlt⟩ := h
  refine lt_of_le_of_lt ?_ hlt
  exact Nat.sInf_le ⟨k, rfl⟩

/-- Consequently the entire three-quarters family of Part II — the even numbers
and the odd class `1 + 4ℕ` (`n ≥ 5`) — has orbit minimum strictly below the start,
unconditionally and without Tao's axiom. -/
theorem even_or_mod_four_one_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_attainsBelow hn h)

/-- The logarithmic-density partial average of a set `S` up to `N`:
`(∑_{n≤N, n∈S} 1/n) / (∑_{n≤N} 1/n)`. -/
noncomputable def logDensity (S : Set ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, S.indicator (fun m => (1 : ℝ) / m) n)
    / (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n)

/-- `S` has **logarithmic density one** if its partial averages tend to `1`. -/
def HasLogDensityOne (S : Set ℕ) : Prop :=
  Tendsto (logDensity S) atTop (nhds 1)

/-! ## Part IV: Tao's theorem (axiomatized, deep)

The precise statement of Tao (2019).  This is the result whose formalization the
open question asks about; we record it as a single axiom and document above why a
direct Lean proof is currently out of reach.  No theorem in this file is derived
from it — the content of Parts II–III stands on its own. -/

/--
**Tao (2019):** for every `f : ℕ → ℝ` tending to infinity, the set of positive
starting values whose orbit minimum is eventually below `f n` has logarithmic
density one.  Taking `f n = n` recovers "almost all `n` have finite stopping
time"; the strength of the theorem is that `f` may grow arbitrarily slowly.
-/
axiom tao_2019 :
    ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
      HasLogDensityOne {n : ℕ | 0 < n ∧ (colMin n : ℝ) < f n}

end CollatzStructuredOQ02OQ03
