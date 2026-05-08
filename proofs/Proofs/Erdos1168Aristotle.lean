/-
  Aristotle targets for Erdős Problem #1168
  Routine supporting lemmas for automated proof search.
  See Erdos1168Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

open Cardinal Ordinal

namespace Erdos1168Aristotle

/-- ℵ_ω is an infinite cardinal. -/
theorem aleph_omega_infinite : ℵ₀ ≤ Cardinal.aleph omega0 :=
  Cardinal.aleph0_le_aleph omega0

/-- ℵ_{ω+1} is uncountable. -/
theorem aleph_omega_succ_uncountable : ℵ₀ < Cardinal.aleph (omega0 + 1) := by
  have h0 : (0 : Ordinal) < omega0 + 1 := Ordinal.succ_pos omega0
  calc (ℵ₀ : Cardinal) = Cardinal.aleph 0 := Cardinal.aleph_zero.symm
    _ < Cardinal.aleph (omega0 + 1) := Cardinal.aleph_lt_aleph.mpr h0

/-- ω + 1 is a successor ordinal. -/
theorem omega_plus_one_is_succ : omega0 + 1 = Order.succ omega0 :=
  (Order.succ_eq_add_one omega0).symm

/-- aleph is strictly monotone: α < β → ℵ_α < ℵ_β. -/
theorem aleph_strict_mono (α β : Ordinal.{0}) (h : α < β) :
    Cardinal.aleph α < Cardinal.aleph β :=
  Cardinal.aleph_lt_aleph.mpr h

/-- aleph is monotone: α ≤ β → ℵ_α ≤ ℵ_β. -/
theorem aleph_mono (α β : Ordinal.{0}) (h : α ≤ β) :
    Cardinal.aleph α ≤ Cardinal.aleph β :=
  Cardinal.aleph_le_aleph.mpr h

/-- Every aleph is infinite: ℵ₀ ≤ ℵ_α for all α. -/
theorem aleph0_le_aleph (α : Ordinal.{0}) : ℵ₀ ≤ Cardinal.aleph α :=
  Cardinal.aleph0_le_aleph α

/-- n < ω for all natural numbers n. -/
theorem nat_lt_omega (n : ℕ) : (n : Ordinal) < omega0 :=
  Ordinal.nat_lt_omega0 n

/-- 3 ≤ ℵ₀: a finite number is at most aleph-zero. -/
theorem three_le_aleph0 : (3 : Cardinal) ≤ ℵ₀ :=
  (Cardinal.nat_lt_aleph0 3).le

/-- ℵ₀ ≤ ℵ_{n+1} for all n : ℕ. -/
theorem aleph0_le_aleph_nat_succ (n : ℕ) : ℵ₀ ≤ Cardinal.aleph (n + 1) :=
  Cardinal.aleph0_le_aleph (n + 1)

/-- The cofinality of a successor aleph equals that aleph:
    cf(ℵ_{α+1}) = ℵ_{α+1} (successor alephs are regular). -/
theorem cof_aleph_succ (α : Ordinal.{0}) :
    ((Cardinal.aleph (Order.succ α)).ord.cof : Cardinal) = Cardinal.aleph (Order.succ α) :=
  (Cardinal.isRegular_aleph_succ α).cof_eq

end Erdos1168Aristotle
