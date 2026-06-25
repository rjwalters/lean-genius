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
  * proves, **unconditionally and axiom-free**, that two large explicit families
    of starting values already satisfy the "drops below itself" conclusion — the
    even numbers and the powers of two — so the elementary part of the
    almost-all picture is real Lean content, not scaffolding on the axiom.

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

theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-! ## Part II: Two explicit families that drop below their start

These are the unconditional, axiom-free part of the almost-all picture: whatever
Tao's analytic argument gives for *almost all* `n`, the even numbers and the
powers of two are handled by elementary one-line dynamics. -/

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
