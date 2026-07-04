/-
  Nth Root Irrationality OQ-02-OQ-02:
  Ergonomic valuation criterion for mixed prime exponents

  The parent file `NthRootIrrationalOQ02.lean` proves the *raw* valuation
  criterion

      not_perfect_pow_of_factorization :
        ¬ n ∣ m.factorization p  →  ¬ ∃ k, k ^ n = m,

  and packages it into two ergonomic corollaries.  But its user-facing composite
  helper `not_perfect_pow_of_sq_not_dvd` fires only when a prime divides `m`
  *exactly once* (`p ∣ m`, `p² ∤ m`, i.e. exponent `1`).  That is a convenient
  but narrow trigger: it misses radicands all of whose prime exponents are `≥ 2`
  yet not all divisible by `n`.  The canonical example is

      72 = 2³ · 3²,      √72 irrational,

  where the blocking prime is `2` with exponent `3` (odd), while `3` has the
  benign even exponent `2`.  Prime `2` satisfies `2² ∣ 72`, so the exponent-`1`
  lemma does not apply, and prime `3` has an exponent divisible by `n = 2`, so it
  does not block.  The raw criterion *can* certify `√72` (via `v_2(72) = 3`), but
  there is no ergonomic bridge to it in the parent.

  This file supplies that bridge.  The idea: for a concrete radicand, the exact
  `p`-adic valuation `v_p(m) = e` is certified by the two *size-independent*
  divisibility `decide`s

      p ^ e ∣ m       and       ¬ p ^ (e+1) ∣ m,

  which pin `m.factorization p = e` through Mathlib's
  `Nat.Prime.pow_dvd_iff_le_factorization`.  From `n ∤ e` the raw criterion then
  fires.  This handles every "some exponent not a multiple of `n`" radicand — the
  exponent-`1` corollary of the parent becomes the special case `e = 1`.

  Results (0 axioms, 0 sorries):
  - irrational_nthRoot_of_exists_factorization  (headline: the ∃-form criterion,
    matching the problem's formal statement `(∃ p, n ∤ v_p(m)) → Irrational ⁿ√m`)
  - not_perfect_pow_of_factorization_eq         (the ergonomic exponent-`e`
    criterion via a divisibility window)
  - irrational_nthRoot_of_factorization_eq      (its irrationality corollary)
  - Concrete corollaries the parent's exponent-`1` lemma cannot reach:
    √72, √288, √500, ∛72, ∛108 — and a re-derivation of √12 showing the `e = 1`
    case is subsumed.
-/

import Mathlib
import Proofs.NthRootIrrational
import Proofs.NthRootIrrationalOQ02

set_option maxHeartbeats 1000000

namespace NthRootIrrationalOQ02OQ02

open NthRootIrrational NthRootIrrationalOQ02

/-! ## Part 1: The valuation criterion in existential form

The problem's formal statement is `(∃ p prime, n ∤ v_p(m)) → Irrational (ⁿ√m)`.
The parent's raw `not_perfect_pow_of_factorization` already contains the
mathematical content; here we simply package it into the exact existential shape,
fed through the base `irrational_nthRoot`.  (When `m = 0` the hypothesis is
vacuous, since `n ∣ 0 = m.factorization p` for every `p`.) -/

/-- **Headline valuation criterion.**  If *some* prime `p` has a `p`-adic
valuation `v_p(m) = m.factorization p` that is not divisible by `n`, then `ⁿ√m`
is irrational.  This is the honest, complete form of the irrationality test:
it fires for every radicand that is not a perfect `n`-th power, without any
restriction on the sizes of the other exponents. -/
theorem irrational_nthRoot_of_exists_factorization {m n : ℕ} (hn : 1 < n)
    (h : ∃ p, ¬ n ∣ m.factorization p) : Irrational (nthRoot n m) := by
  obtain ⟨p, hp⟩ := h
  exact irrational_nthRoot n m hn
    (not_perfect_pow_int (not_perfect_pow_of_factorization hp))

/-! ## Part 2: The ergonomic exponent-`e` criterion

Computing `m.factorization p` on a literal is awkward; instead we certify the
exact exponent `e` by a *divisibility window* `p ^ e ∣ m ∧ ¬ p ^ (e+1) ∣ m`.
Both halves are cheap `decide`s whose cost is independent of the magnitude of
`m`, so the criterion scales to large radicands and large exponents alike. -/

/-- **Exponent-`e` not-a-perfect-power criterion.**  Suppose the prime `p`
appears in `m` to exponent exactly `e`, witnessed by the divisibility window
`p ^ e ∣ m` and `¬ p ^ (e+1) ∣ m`.  If `n ∤ e`, then `m` is not a perfect
`n`-th power.  Taking `e = 1` recovers the parent's `not_perfect_pow_of_sq_not_dvd`,
but `e` is now arbitrary, so mixed-exponent radicands such as `72 = 2³ · 3²`
are covered. -/
theorem not_perfect_pow_of_factorization_eq {m n p e : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpe : p ^ e ∣ m) (hpe1 : ¬ p ^ (e + 1) ∣ m) (hndvd : ¬ n ∣ e) :
    ¬ ∃ k : ℕ, k ^ n = m := by
  have hval : m.factorization p = e := by
    have h1 : e ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization hm).mp hpe
    have h2 : ¬ (e + 1 ≤ m.factorization p) := fun h =>
      hpe1 ((hp.pow_dvd_iff_le_factorization hm).mpr h)
    omega
  exact not_perfect_pow_of_factorization (by rw [hval]; exact hndvd)

/-! ## Part 3: Irrationality from the exponent-`e` criterion -/

/-- **Irrationality via a single blocking prime of exponent `e`.**  If `p` appears
in `m` to exponent exactly `e` (a divisibility window) and `n ∤ e`, then `ⁿ√m` is
irrational. -/
theorem irrational_nthRoot_of_factorization_eq {m n p e : ℕ} (hn : 1 < n)
    (hp : p.Prime) (hm : m ≠ 0) (hpe : p ^ e ∣ m) (hpe1 : ¬ p ^ (e + 1) ∣ m)
    (hndvd : ¬ n ∣ e) : Irrational (nthRoot n m) :=
  irrational_nthRoot n m hn
    (not_perfect_pow_int (not_perfect_pow_of_factorization_eq hp hm hpe hpe1 hndvd))

/-! ## Part 4: Concrete corollaries the exponent-`1` lemma cannot reach

Each radicand below has *every* prime exponent `≥ 2`, so the parent's
`irrational_nthRoot_of_sq_not_dvd` (which needs a prime of exponent exactly `1`)
does not apply.  The blocking prime is named explicitly via `(p := …) (e := …)`;
the three divisibility side-conditions are `decide`s. -/

/-- `√72` irrational — `72 = 2³ · 3²`.  Blocked by `2` at exponent `3` (odd):
`8 ∣ 72`, `16 ∤ 72`, `2 ∤ 3`.  Prime `3` has the benign even exponent `2`, and
`2² ∣ 72` rules out the parent's exponent-`1` lemma.  This is the canonical
radicand the narrow corollary silently excludes. -/
theorem irrational_sqrt_72 : Irrational (nthRoot 2 72) :=
  irrational_nthRoot_of_factorization_eq (m := 72) (n := 2) (p := 2) (e := 3)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

/-- `√288` irrational — `288 = 2⁵ · 3²`.  Blocked by `2` at exponent `5`:
`32 ∣ 288`, `64 ∤ 288`, `2 ∤ 5`. -/
theorem irrational_sqrt_288 : Irrational (nthRoot 2 288) :=
  irrational_nthRoot_of_factorization_eq (m := 288) (n := 2) (p := 2) (e := 5)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

/-- `√500` irrational — `500 = 2² · 5³`.  Here the square factor `2²` is benign;
the blocking prime is `5` at exponent `3`: `125 ∣ 500`, `625 ∤ 500`, `2 ∤ 3`. -/
theorem irrational_sqrt_500 : Irrational (nthRoot 2 500) :=
  irrational_nthRoot_of_factorization_eq (m := 500) (n := 2) (p := 5) (e := 3)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

/-- `∛72` irrational — `72 = 2³ · 3²`, cube root.  Now `2³` is benign (`3 ∣ 3`),
and the blocking prime is `3` at exponent `2`: `9 ∣ 72`, `27 ∤ 72`, `3 ∤ 2`.
The *same* radicand `72` is blocked by a *different* prime depending on `n` —
exactly what the exponent-`1` lemma cannot express. -/
theorem irrational_cbrt_72 : Irrational (nthRoot 3 72) :=
  irrational_nthRoot_of_factorization_eq (m := 72) (n := 3) (p := 3) (e := 2)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

/-- `∛108` irrational — `108 = 2² · 3³`.  The cube factor `3³` is benign; the
blocking prime is `2` at exponent `2`: `4 ∣ 108`, `8 ∤ 108`, `3 ∤ 2`. -/
theorem irrational_cbrt_108 : Irrational (nthRoot 3 108) :=
  irrational_nthRoot_of_factorization_eq (m := 108) (n := 3) (p := 2) (e := 2)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

/-! ### Subsumption of the exponent-`1` case

The parent's exponent-`1` corollary is the special case `e = 1` of the criterion
above, so nothing is lost by generalizing.  For instance `√12` (`12 = 2² · 3`,
blocked by `3` at exponent `1`) is still a one-liner here. -/

/-- `√12` irrational via the general criterion at `e = 1` (`12 = 2² · 3`, blocked
by `3`): `3 ∣ 12`, `9 ∤ 12`, `2 ∤ 1`.  Demonstrates that the exponent-`1` trigger
of the parent is recovered as a special case. -/
theorem irrational_sqrt_12 : Irrational (nthRoot 2 12) :=
  irrational_nthRoot_of_factorization_eq (m := 12) (n := 2) (p := 3) (e := 1)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

end NthRootIrrationalOQ02OQ02

-- Axiom audit (kept as a comment; uncomment locally to re-verify): the results below
-- depend only on `propext / Classical.choice / Quot.sound` — no `sorryAx`, no
-- `Lean.ofReduceBool` (the `decide`s are kernel-checked, not `native_decide`).
-- #print axioms NthRootIrrationalOQ02OQ02.irrational_nthRoot_of_exists_factorization
-- #print axioms NthRootIrrationalOQ02OQ02.irrational_sqrt_72
