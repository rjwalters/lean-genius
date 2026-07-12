import Proofs.ElementaryQuadraticReciprocityOQ03OQ02
import Mathlib.Tactic

/-
# The Kronecker Symbol as a Periodic Character (completion of ...OQ03OQ02)

*Open question* (`elementary-quadratic-reciprocity-oq-03-oq-02-wip-01`): the parent
file `ElementaryQuadraticReciprocityOQ03OQ02` builds the Kronecker symbol `(a/n)`,
proves it is completely multiplicative in both arguments, and (Section 5) motivates
it as *"the associated primitive Dirichlet character"* of a fundamental discriminant.
The defining property of a Dirichlet character mod `n` — periodicity of the symbol
in its numerator, `(a/n)` depending only on `a mod n` — is asserted in the prose but
never formalized.  Likewise, for the `(·/2)` character `kronecker2` the parent proves
only *single-step* periodicity `kronecker2_periodic` (`(a+8/2) = (a/2)`), leaving the
full period statement `(a+8k/2) = (a/2)` and the residue-only dependence implicit.

This file closes those gaps, all derived from the parent's public API with no new
axioms (`propext`, `Classical.choice`, `Quot.sound` only):

## Numerator side — the Dirichlet-character property of `(·/n)`

* `kronecker_congr_left`      — for odd positive `n`, `a ≡ b (mod n) ⟹ (a/n) = (b/n)`.
                                The symbol is a function of the residue class `a mod n`.
* `kronecker_add_mul_left`    — `(a + n·k / n) = (a/n)` for every `k`: full periodicity
                                of the numerator with period `n`.
* `kronecker_periodic_left`   — the `k = 1` shift `(a + n / n) = (a/n)`, the textbook
                                statement that `(·/n)` is a character modulo `n`.

## `(·/2)` side — full periodicity of `kronecker2`

* `kronecker2_congr`          — `a ≡ b (mod 8) ⟹ kronecker2 a = kronecker2 b`.
* `kronecker2_add_mul_eight`  — `kronecker2 (a + 8·k) = kronecker2 a` (full period 8,
                                generalizing the parent's single-step `kronecker2_periodic`).

Together with the parent's `kronecker2_mul` / `kronecker2_neg` these complete the
identification of `(·/2)` and `(·/n)` (odd `n`) as genuine periodic characters — the
structural input the Gauss-sum route to generalized quadratic reciprocity rests on.

All results are fully machine-checked (0 axioms, 0 sorries).

Reference: Kronecker (1885); Hardy–Wright ch. 6; parent `ElementaryQuadraticReciprocityOQ03OQ02`.
-/

namespace KroneckerSymbol

open Int

-- ============================================================
-- Section A: The Dirichlet-character property of `(·/n)` (numerator side)
-- ============================================================

/-- **The Kronecker symbol depends only on the residue class of its numerator.**
    For odd positive `n`, if `a ≡ b (mod n)` then `(a/n) = (b/n)`.  On odd positive
    moduli the parent's `kronecker_eq_jacobi` identifies `(·/n)` with the Jacobi
    symbol, and `jacobiSym.mod_left'` supplies exactly this residue-invariance.  This
    is the defining periodicity of the Dirichlet character `(·/n)` promised (but not
    proved) in the parent's Section 5. -/
theorem kronecker_congr_left {a b : ℤ} {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : a % (n : ℤ) = b % (n : ℤ)) :
    kronecker a n = kronecker b n := by
  rw [kronecker_eq_jacobi a n hn hodd, kronecker_eq_jacobi b n hn hodd]
  exact jacobiSym.mod_left' h

/-- **Full numerator periodicity with period `n`.**  For odd positive `n` and every
    integer shift `k`, `(a + n·k / n) = (a/n)`: adding any multiple of the modulus to
    the numerator leaves the symbol unchanged.  Immediate from `kronecker_congr_left`
    since `(a + n·k) % n = a % n`. -/
theorem kronecker_add_mul_left (a k : ℤ) {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    kronecker (a + n * k) n = kronecker a n :=
  kronecker_congr_left hn hodd (by rw [Int.add_mul_emod_self_left])

/-- **`(·/n)` is a character modulo `n`: the unit shift.**  The `k = 1` case of
    `kronecker_add_mul_left`, `(a + n / n) = (a/n)` — the textbook statement that the
    Kronecker symbol at a fixed odd positive modulus `n` is periodic with period `n`. -/
theorem kronecker_periodic_left (a : ℤ) {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    kronecker (a + n) n = kronecker a n := by
  simpa using kronecker_add_mul_left a 1 hn hodd

-- ============================================================
-- Section B: Full periodicity of the `(·/2)` character `kronecker2`
-- ============================================================

/-- `kronecker2 x` depends only on `x % 8` (re-derived locally as a helper). -/
private theorem kronecker2_mod_eight (x : ℤ) : kronecker2 x = kronecker2 (x % 8) := by
  unfold kronecker2
  rw [Int.emod_emod_of_dvd x (by norm_num : (2 : ℤ) ∣ 8),
    Int.emod_emod_of_dvd x (by norm_num : (8 : ℤ) ∣ 8)]

/-- **`kronecker2` depends only on the residue mod `8`.**  If `a ≡ b (mod 8)` then
    `kronecker2 a = kronecker2 b`: the `(·/2)` symbol is a function of the residue
    class mod `8`.  This is the congruence-invariance underlying the parent's
    single-step `kronecker2_periodic`. -/
theorem kronecker2_congr {a b : ℤ} (h : a % 8 = b % 8) :
    kronecker2 a = kronecker2 b := by
  rw [kronecker2_mod_eight a, kronecker2_mod_eight b, h]

/-- **Full period `8` for `kronecker2`.**  `kronecker2 (a + 8·k) = kronecker2 a` for
    every integer `k`, generalizing the parent's single-step `kronecker2_periodic`
    (`k = 1`).  Since `kronecker2` depends only on `a % 8` (`kronecker2_congr`) and
    `(a + 8·k) % 8 = a % 8`, adding any multiple of `8` fixes the value — the exact
    period-8 statement identifying `(·/2)` as a Dirichlet character mod `8`. -/
theorem kronecker2_add_mul_eight (a k : ℤ) :
    kronecker2 (a + 8 * k) = kronecker2 a :=
  kronecker2_congr (by rw [Int.add_mul_emod_self_left])

end KroneckerSymbol
