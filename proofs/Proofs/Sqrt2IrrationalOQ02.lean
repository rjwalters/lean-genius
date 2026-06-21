/-
Beyond irrationality: transcendental numbers exist (OQ-02)

Parent entry `sqrt2-irrational` proves `√n` irrational for non-square `n` — every such
number is irrational but *algebraic* (a root of `x² − n`).  Its second open question asks:

  *Are there irrational numbers that aren't roots of any polynomial?  Yes — transcendental
  numbers.*

This file answers it concretely and axiom-free, using Mathlib's Liouville theory.
Liouville's constant `∑_k m^{-k!}` (for `m = 2`) is **transcendental**: it is not a root
of any nonzero polynomial with integer coefficients, and in particular it is irrational —
an irrational number lying strictly beyond the algebraic numbers `√n` of the parent.

Main results:
* `liouvilleConst_liouville`        — Liouville's constant is a Liouville number.
* `liouvilleConst_irrational`       — it is irrational.
* `liouvilleConst_transcendental`   — it is transcendental over `ℤ` (no integer polynomial
  has it as a root).
* `exists_irrational_transcendental`— there exists an irrational, transcendental real.
* `not_forall_irrational_isAlgebraic` — not every irrational real is algebraic (so the
  parent's `√n` family does not exhaust the irrationals).
-/

import Mathlib

open LiouvilleNumber

namespace Sqrt2IrrationalOQ02

/-- **Liouville's constant** `L = ∑_{k} 2^{-k!}`, the canonical concrete transcendental. -/
noncomputable def liouvilleConst : ℝ := liouvilleNumber (2 : ℕ)

/-- Liouville's constant is a Liouville number. -/
theorem liouvilleConst_liouville : Liouville liouvilleConst :=
  liouville_liouvilleNumber (by norm_num)

/-- Liouville's constant is irrational. -/
theorem liouvilleConst_irrational : Irrational liouvilleConst :=
  liouvilleConst_liouville.irrational

/-- **Liouville's constant is transcendental** over `ℤ`: it is not a root of any nonzero
polynomial with integer coefficients. -/
theorem liouvilleConst_transcendental : Transcendental ℤ liouvilleConst :=
  transcendental_liouvilleNumber (by norm_num)

/-- **Answer to OQ-02.** There is an irrational real number that is not a root of any
nonzero integer polynomial — a transcendental number, lying beyond the algebraic
irrationals `√n` of the parent entry. -/
theorem exists_irrational_transcendental :
    ∃ x : ℝ, Irrational x ∧ Transcendental ℤ x :=
  ⟨liouvilleConst, liouvilleConst_irrational, liouvilleConst_transcendental⟩

/-- Transcendence is genuinely stronger than irrationality: there is an irrational real
that is **not algebraic** over `ℤ`.  Hence the algebraic irrationals (such as the parent's
`√n`) do not exhaust the irrational numbers. -/
theorem not_forall_irrational_isAlgebraic :
    ∃ x : ℝ, Irrational x ∧ ¬ IsAlgebraic ℤ x :=
  ⟨liouvilleConst, liouvilleConst_irrational, liouvilleConst_transcendental⟩

end Sqrt2IrrationalOQ02
