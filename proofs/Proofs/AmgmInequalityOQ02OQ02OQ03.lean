/-
  Muirhead's Inequality via Majorization — The Two-Variable Bunching Step
  Research: amgm-inequality-oq-02-oq-02-oq-03

  The parent formalization `amgm-inequality-oq-02-oq-02`
  (`Proofs.AmgmInequalityOQ02`, `Proofs.AmgmInequalityOQ02OQ02`) proves
  Newton's log-concavity and the Maclaurin step Mₖ(x) ≥ Mₖ₊₁(x) for the
  elementary symmetric means.  Maclaurin's chain is a special case of the
  Muirhead / Hardy–Littlewood–Pólya inequality, which orders the power-sum
  symmetric means

      [a](x) = (1/n!) · Σ_{σ ∈ Sₙ} ∏ᵢ xᵢ^{a_{σ(i)}}

  by *majorization* on the exponent vector a.  The open question OQ-03 asks
  to formalize this majorization ordering.

  The engine of Muirhead's theorem is the **atomic bunching step**: a single
  "Robin-Hood" transfer between two coordinates, which is precisely the
  two-variable inequality.  The full n-variable statement follows by iterating
  this step along the sequence of T-transforms that carries the majorizing
  vector down to the majorized one (Muirhead's lemma: a ⪰ b iff b is reachable
  from a by finitely many such transfers).

  This file proves that atomic step in full generality (0 axioms, 0 sorries),
  isolating the single algebraic identity on which all of Muirhead rests:

      x^{q+α} y^{q+β} + x^{q+β} y^{q+α}   ≤   x^{q+α+β} y^{q} + x^{q} y^{q+α+β}

  which holds for all x, y ≥ 0 and all q, α, β ∈ ℕ because the difference
  factors as

      x^q y^q · (x^α − y^α)(x^β − y^β)  ≥  0.

  Main results:
  1. `same_sign_pow`      — (x^α − y^α)(x^β − y^β) ≥ 0 for x, y ≥ 0
  2. `bunching_identity`  — the exact factorization above (pure `ring`)
  3. `muirhead_swap`      — the atomic bunching inequality (unconditional)
  4. `Majorizes2` / `muirhead_two_var`
                          — two-variable Muirhead in majorization form
  5. `amgm_two_var`, `muirhead_3_1_vs_2_2`
                          — sample corollaries (AM–GM and a genuine transfer)

  Scope note (honesty): this file settles the two-variable case only — the
  atomic transfer that is the heart of Muirhead's theorem.  The general
  n-variable Muirhead inequality, which composes these transfers via the
  permutation-pairing argument, is left for a follow-up problem.

  References:
  - Hardy, Littlewood, Pólya "Inequalities" (1934) §2.18 (Muirhead's theorem)
  - Muirhead, R. F. "Some methods applicable to identities and inequalities of
    symmetric algebraic functions of n letters" (1903)
  - AmgmInequalityOQ02OQ02.lean (Newton / Maclaurin parent)
-/

import Mathlib

open Finset

namespace MuirheadBunching

/-!
## Part I: Same-sign power products

For non-negative `x, y` the two factors `x^α − y^α` and `x^β − y^β` always
have the same sign (both determined by whether `x ≤ y`), so their product is
non-negative.  This is the sole inequality input to the whole development.
-/

/-- For `x, y ≥ 0` and any natural exponents `α, β`, the product
`(x^α − y^α)(x^β − y^β)` is non-negative: both factors share the sign of
`x − y`. -/
theorem same_sign_pow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (α β : ℕ) :
    0 ≤ (x ^ α - y ^ α) * (x ^ β - y ^ β) := by
  rcases le_total x y with h | h
  · -- x ≤ y ⇒ both factors ≤ 0 ⇒ product ≥ 0
    have hα : x ^ α ≤ y ^ α := by gcongr
    have hβ : x ^ β ≤ y ^ β := by gcongr
    nlinarith [hα, hβ]
  · -- y ≤ x ⇒ both factors ≥ 0 ⇒ product ≥ 0
    have hα : y ^ α ≤ x ^ α := by gcongr
    have hβ : y ^ β ≤ x ^ β := by gcongr
    nlinarith [hα, hβ]

/-!
## Part II: The bunching identity and the atomic swap

The difference between the "more spread" pair `(q+α+β, q)` and the "less
spread" pair `(q+α, q+β)` is an exact algebraic identity — no inequality yet.
-/

/-- The exact factorization underlying Muirhead's atomic step.  Pure algebra,
closed by `ring` (which expands the natural-number exponent sums). -/
theorem bunching_identity (x y : ℝ) (q α β : ℕ) :
    x ^ (q + α + β) * y ^ q + x ^ q * y ^ (q + α + β)
        - (x ^ (q + α) * y ^ (q + β) + x ^ (q + β) * y ^ (q + α))
      = x ^ q * y ^ q * ((x ^ α - y ^ α) * (x ^ β - y ^ β)) := by
  ring

/-- **Atomic bunching inequality** (the engine of Muirhead's theorem).

For `x, y ≥ 0` and any `q, α, β ∈ ℕ`, spreading the exponent pair from
`(q+α, q+β)` out to `(q+α+β, q)` can only *increase* the symmetric sum:

  `x^{q+α} y^{q+β} + x^{q+β} y^{q+α} ≤ x^{q+α+β} y^q + x^q y^{q+α+β}`.

No ordering hypothesis on `α, β` is needed: the difference is a non-negative
multiple of `same_sign_pow`. -/
theorem muirhead_swap (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (q α β : ℕ) :
    x ^ (q + α) * y ^ (q + β) + x ^ (q + β) * y ^ (q + α)
      ≤ x ^ (q + α + β) * y ^ q + x ^ q * y ^ (q + α + β) := by
  have key : 0 ≤ x ^ q * y ^ q * ((x ^ α - y ^ α) * (x ^ β - y ^ β)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hx q) (pow_nonneg hy q))
      (same_sign_pow x y hx hy α β)
  have hid := bunching_identity x y q α β
  linarith [key, hid]

/-!
## Part III: Two-variable Muirhead in majorization form

We package the atomic step as an honest majorization statement for pairs of
natural exponents.  `Majorizes2 a b c d` says the ordered pair `(a, b)`
majorizes `(c, d)`; the theorem then says the symmetric sum for the dominant
pair is at least that for the dominated one.
-/

/-- `Majorizes2 a b c d` : the exponent pair `(a, b)` (with `a ≥ b`) majorizes
the pair `(c, d)` (with `c ≥ d`).  For pairs of equal sum this is exactly
`c ≤ a` (equivalently `max` dominates `max`). -/
structure Majorizes2 (a b c d : ℕ) : Prop where
  /-- the first pair is written largest-first -/
  fst_ordered : b ≤ a
  /-- the second pair is written largest-first -/
  snd_ordered : d ≤ c
  /-- majorization preserves the total -/
  sum_eq : a + b = c + d
  /-- the dominant coordinate of `(a,b)` dominates that of `(c,d)` -/
  dom : c ≤ a

/-- **Two-variable Muirhead inequality.**  If `(a, b)` majorizes `(c, d)`,
then for all `x, y ≥ 0` the symmetric sum is monotone under majorization:

  `x^c y^d + x^d y^c ≤ x^a y^b + x^b y^a`.

Proof: with `b` the common minimum, write `c = b + α`, `d = b + β`,
`a = b + α + β` and apply `muirhead_swap`. -/
theorem muirhead_two_var (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    {a b c d : ℕ} (h : Majorizes2 a b c d) :
    x ^ c * y ^ d + x ^ d * y ^ c ≤ x ^ a * y ^ b + x ^ b * y ^ a := by
  obtain ⟨hba, hdc, hsum, hca⟩ := h
  -- `b` is the minimum of all four exponents
  have hbd : b ≤ d := by omega
  have hbc : b ≤ c := by omega
  obtain ⟨α, hα⟩ := Nat.exists_eq_add_of_le hbc   -- c = b + α
  obtain ⟨β, hβ⟩ := Nat.exists_eq_add_of_le hbd   -- d = b + β
  subst hα hβ
  have ha : a = b + α + β := by omega
  subst ha
  exact muirhead_swap x y hx hy b α β

/-!
## Part IV: Sample corollaries

Concrete instances that fall straight out of the two-variable theorem,
demonstrating that the majorization ordering has real content.
-/

/-- AM–GM for two variables as the majorization `(2, 0) ⪰ (1, 1)`:
`2xy ≤ x² + y²`. -/
theorem amgm_two_var (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  have h := muirhead_two_var x y hx hy
    (a := 2) (b := 0) (c := 1) (d := 1)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  simp only [pow_one, pow_zero, mul_one, one_mul] at h
  linarith [h]

/-- A genuine (non-degenerate) transfer, `(3, 1) ⪰ (2, 2)`:
`2 x² y² ≤ x³ y + x y³`.  Here both pairs have positive minimum, so it is not
reducible to a bare AM–GM. -/
theorem muirhead_3_1_vs_2_2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 * y ^ 2) ≤ x ^ 3 * y + x * y ^ 3 := by
  have h := muirhead_two_var x y hx hy
    (a := 3) (b := 1) (c := 2) (d := 2)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  simp only [pow_one] at h
  linarith [h]

end MuirheadBunching
