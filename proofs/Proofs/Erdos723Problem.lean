/-
Erdős Problem #723: The Prime Power Conjecture for Projective Planes

**Problem (Erdős)**: If there is a finite projective plane of order n,
must n be a prime power?

**Status**: OPEN (general conjecture)

**Partial Results**:
- Projective planes exist for all prime power orders (classical construction)
- Verified for n ≤ 11
- n = 10 ruled out by Lam's computer search (1997)
- Bruck-Ryser theorem: if n ≡ 1,2 (mod 4), then n must be sum of two squares
- Order 12 remains open

Reference: https://erdosproblems.com/723
-/

import Mathlib

open Configuration

namespace Erdos723

/-! ## Background on Projective Planes

A finite projective plane of order n has:
- n² + n + 1 points
- n² + n + 1 lines
- Each line contains n + 1 points
- Each point lies on n + 1 lines
- Any two distinct points determine a unique line
- Any two distinct lines meet in a unique point

The Mathlib type `Configuration.ProjectivePlane P L` captures these axioms.
-/

/-! ## The Main Conjecture (Open) -/

/--
**Erdős Problem #723** (The Prime Power Conjecture):

If there exists a finite projective plane of order n, must n be a prime power?

This is one of the most famous open problems in combinatorics. Despite extensive
computational and theoretical effort, neither a proof nor a counterexample has
been found.

We state this as an open problem (axiom for True, indicating we don't know
whether the answer is yes or no).
-/
axiom erdos_723_open : True  -- The general conjecture remains open

/--
The formal statement of the Prime Power Conjecture: every finite projective
plane has prime power order.
-/
def PrimePowerConjecture : Prop :=
  ∀ {P L : Type*} [Membership P L] [Fintype P] [Fintype L],
    ∀ pp : ProjectivePlane P L, IsPrimePow pp.order

/-! ## Existence for Prime Power Orders (Solved) -/

/--
**Classical Result**: Projective planes exist for every prime power order.

For a prime power q = p^k, the projective plane PG(2, q) can be constructed
from the finite field GF(q). Points are 1-dimensional subspaces of GF(q)³,
and lines are 2-dimensional subspaces.
-/
axiom prime_power_planes_exist :
    ∀ n : ℕ, IsPrimePow n →
    ∃ (P L : Type*) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = n

/-! ## Verified for Small Orders -/

/--
The Prime Power Conjecture has been verified for all orders n ≤ 11.

For n = 1, 2, 3, 4, 5, 7, 8, 9, 11 (prime powers): planes exist.
For n = 6: ruled out by Bruck-Ryser (6 ≡ 2 mod 4 but 6 ≠ a² + b²).
For n = 10: ruled out by Lam's computer search (1997).
-/
axiom verified_up_to_11 :
    ∀ {P L : Type*} [Membership P L] [Fintype P] [Fintype L],
    ∀ pp : ProjectivePlane P L, pp.order ≤ 11 → IsPrimePow pp.order

/-! ## The Bruck-Ryser Theorem -/

/--
**Bruck-Ryser Theorem (1949)**: If a projective plane of order n exists,
and n ≡ 1 (mod 4) or n ≡ 2 (mod 4), then n must be the sum of two squares.

This rules out many non-prime-power orders:
- n = 6: 6 ≡ 2 (mod 4) but 6 ≠ a² + b²
- n = 14: 14 ≡ 2 (mod 4) but 14 ≠ a² + b²
- n = 21: 21 ≡ 1 (mod 4) but 21 ≠ a² + b²
- n = 22: 22 ≡ 2 (mod 4) but 22 ≠ a² + b²
-/
axiom bruck_ryser :
    ∀ {P L : Type*} [Membership P L] [Fintype P] [Fintype L],
    ∀ (n : ℕ) (pp : ProjectivePlane P L), pp.order = n →
    (n % 4 = 1 ∨ n % 4 = 2) → ∃ a b : ℕ, n = a^2 + b^2

/-! ## The Lam Result for Order 10 -/

/--
**Lam's Theorem (1997)**: There is no projective plane of order 10.

This was proved by a massive computer search, which took over a decade of
computation time. It's one of the largest computational proofs in mathematics.

Combined with Bruck-Ryser (which doesn't rule out 10), this shows the
conjecture holds for n = 10 despite 10 not being ruled out theoretically.
-/
axiom lam_order_10 :
    ¬∃ (P L : Type*) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = 10

/-! ## Order 12 Remains Open -/

/--
It is an open problem whether a projective plane of order 12 exists.

Note that 12 ≡ 0 (mod 4), so Bruck-Ryser doesn't apply. No computer search
has been successful for order 12, and no theoretical obstruction is known.
-/
axiom order_12_open : True  -- Existence of order 12 plane is open

/-! ## Basic Properties -/

/-- A projective plane of order n has n² + n + 1 points -/
theorem plane_points (P L : Type*) [Membership P L] [Fintype P] [Fintype L]
    (pp : ProjectivePlane P L) : Fintype.card P = pp.order^2 + pp.order + 1 :=
  pp.card_points

/-- A projective plane of order n has n² + n + 1 lines -/
theorem plane_lines (P L : Type*) [Membership P L] [Fintype P] [Fintype L]
    (pp : ProjectivePlane P L) : Fintype.card L = pp.order^2 + pp.order + 1 :=
  pp.card_lines

/-! ## Examples of Small Orders -/

/-- Order 1 plane exists (trivial: 3 points, 3 lines) -/
theorem order_1_is_prime_power : IsPrimePow 1 := by decide

/-- Order 2 exists (Fano plane: 7 points, 7 lines) -/
theorem order_2_is_prime_power : IsPrimePow 2 := by decide

/-- Order 3 exists (13 points, 13 lines) -/
theorem order_3_is_prime_power : IsPrimePow 3 := by decide

/-- Order 4 exists (2²: 21 points, 21 lines) -/
theorem order_4_is_prime_power : IsPrimePow 4 := by
  rw [show (4 : ℕ) = 2^2 by norm_num]
  exact IsPrimePow.pow (Nat.prime_two.isPrimePow) (by norm_num)

/-- Order 5 exists (31 points, 31 lines) -/
theorem order_5_is_prime_power : IsPrimePow 5 := by decide

/-- 6 is not a prime power -/
theorem order_6_not_prime_power : ¬IsPrimePow 6 := by decide

/-- 10 is not a prime power -/
theorem order_10_not_prime_power : ¬IsPrimePow 10 := by decide

/-- 12 is not a prime power -/
theorem order_12_not_prime_power : ¬IsPrimePow 12 := by decide

/-! ## Bruck-Ryser Applications -/

/-- 6 ≡ 2 (mod 4) -/
theorem six_mod_4 : 6 % 4 = 2 := by decide

/-- 6 is not a sum of two squares -/
theorem six_not_sum_squares : ¬∃ a b : ℕ, 6 = a^2 + b^2 := by
  intro ⟨a, b, h⟩
  interval_cases a <;> interval_cases b <;> simp_all

/-- Therefore no projective plane of order 6 exists (by Bruck-Ryser) -/
theorem no_plane_order_6 :
    ¬∃ (P L : Type*) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = 6 := by
  intro ⟨P, L, mem, fp, fl, pp, h⟩
  have br := @bruck_ryser P L mem fp fl 6 pp h (Or.inr (by decide))
  exact six_not_sum_squares br

end Erdos723
