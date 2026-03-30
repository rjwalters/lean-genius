/-
  Multiplicative Property of Prime Factorization
  Open Question: fundamental-arithmetic-oq-01

  For coprime m, n: factorization(m·n) = factorization(m) + factorization(n).

  This means: for each prime p, v_p(m·n) = v_p(m) + v_p(n), where v_p is
  the p-adic valuation. For coprime m, n, at most one of v_p(m), v_p(n) is
  nonzero for each prime p, so the factorizations have disjoint support.

  The result is immediate from Mathlib: Nat.factorization_mul for general m, n,
  and Finsupp.disjoint_iff for the coprime support disjointness.

  References:
  - Mathlib: Nat.factorization_mul, Nat.coprime_iff_disjoint
  - FundamentalArithmetic.lean (parent proof)
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace FundamentalArithmeticOQ01

-- ============================================================
-- Part I: Multiplicativity of Factorization (General Case)
-- ============================================================

/-- For any m, n with m ≠ 0 and n ≠ 0, the factorization of the product
    equals the sum of individual factorizations:
      factorization(m · n) = factorization(m) + factorization(n)

    This is the p-adic valuation additivity: v_p(mn) = v_p(m) + v_p(n). -/
theorem factorization_mul_eq (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).factorization = m.factorization + n.factorization :=
  Nat.factorization_mul hm hn

/-- Pointwise form: for any prime p, v_p(mn) = v_p(m) + v_p(n). -/
theorem factorization_mul_apply (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [factorization_mul_eq m n hm hn]; rfl

-- ============================================================
-- Part II: Coprime Case — Disjoint Factorization Supports
-- ============================================================

/-- For coprime m, n: their factorizations have disjoint support.
    That is, no prime divides both m and n.

    This is the content of Nat.coprime: gcd(m,n) = 1 iff no prime
    divides both, iff the factorizations have disjoint support. -/
theorem factorization_disjoint_of_coprime (m n : ℕ) (hcop : Nat.Coprime m n) :
    Disjoint m.factorization.support n.factorization.support :=
  Nat.coprime_iff_disjoint.mp hcop

/-- For coprime m, n: for each prime p, at most one of v_p(m) and v_p(n)
    is nonzero. This is the pointwise consequence of disjoint support. -/
theorem coprime_valuation_exclusive (m n : ℕ) (hcop : Nat.Coprime m n) (p : ℕ) :
    m.factorization p = 0 ∨ n.factorization p = 0 := by
  by_contra h
  push_neg at h
  have hm : p ∈ m.factorization.support := Finsupp.mem_support_iff.mpr (Nat.pos_of_ne_zero h.1).ne'
  have hn : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr (Nat.pos_of_ne_zero h.2).ne'
  exact (factorization_disjoint_of_coprime m n hcop).ne_of_mem hm hn rfl

-- ============================================================
-- Part III: Concrete Examples
-- ============================================================

/-- Example: factorization(12) = {2 ↦ 2, 3 ↦ 1}. -/
theorem factorization_12 :
    (12 : ℕ).factorization 2 = 2 ∧ (12 : ℕ).factorization 3 = 1 := by
  constructor <;> native_decide

/-- Example: factorization(35) = {5 ↦ 1, 7 ↦ 1}. -/
theorem factorization_35 :
    (35 : ℕ).factorization 5 = 1 ∧ (35 : ℕ).factorization 7 = 1 := by
  constructor <;> native_decide

/-- Example: 12 and 35 are coprime, so factorization(420) = factorization(12) + factorization(35).
    420 = 12 · 35 = 2² · 3 · 5 · 7. -/
theorem factorization_420_from_coprime :
    (420 : ℕ).factorization 2 = 2 ∧
    (420 : ℕ).factorization 3 = 1 ∧
    (420 : ℕ).factorization 5 = 1 ∧
    (420 : ℕ).factorization 7 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The coprime decomposition 420 = 12 · 35 gives disjoint factorizations. -/
theorem coprime_12_35 : Nat.Coprime 12 35 := by native_decide

theorem factorization_420_split :
    (420 : ℕ).factorization = (12 : ℕ).factorization + (35 : ℕ).factorization :=
  factorization_mul_eq 12 35 (by norm_num) (by norm_num)

-- ============================================================
-- Part IV: Iterated Factorization (Finitely Many Coprime Factors)
-- ============================================================

/-- The factorization of a product of a list of nonzero naturals equals
    the sum of their individual factorizations.
    Proof: induction using Nat.factorization_mul at each step. -/
theorem factorization_prod_eq (l : List ℕ) (hpos : ∀ x ∈ l, x ≠ 0) :
    l.prod.factorization = l.map Nat.factorization |>.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [Nat.factorization_mul (hpos a (List.mem_cons_self a l))
      (List.prod_ne_zero (fun x hx => hpos x (List.mem_cons_of_mem a hx)))]
    rw [ih (fun x hx => hpos x (List.mem_cons_of_mem a hx))]

end FundamentalArithmeticOQ01
