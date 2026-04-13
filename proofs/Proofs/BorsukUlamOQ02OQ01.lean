/-
Equivariant Borsuk-Ulam for Non-Prime Groups (OQ-02-OQ-01)

Open Question: For finite cyclic groups Z/n with non-prime n, what is
the optimal equivariant Borsuk-Ulam dimension?

Background:
- For G = Z/p (prime), the Yang-Borsuk theorem gives the BU dimension
- For G = Z/n (composite), the answer depends on the representation
  and involves the prime factorization of n
- The key structural result is monotonicity: if p | n, then the
  Z/n-equivariant BU dimension is at least the Z/p one

This file formalizes the abstract dimension theory for cyclic groups,
avoiding topological infrastructure by axiomatizing the BU dimension
as a function of (group order, representation dimension).

References:
- Dold, "Simple proofs of some Borsuk-Ulam results" (1983)
- Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
- Matousek, "Using the Borsuk-Ulam Theorem" (2003)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace BorsukUlamOQ02OQ01

-- ============================================================
-- PART I: Abstract Equivariant Borsuk-Ulam Dimension
-- ============================================================

/-
We model the equivariant Borsuk-Ulam dimension as a function

  buDim : ℕ → ℕ → ℕ

where buDim(n, d) is the minimum sphere dimension such that any
Z/n-equivariant continuous map from S^{buDim(n,d)} to a d-dimensional
representation space must have a zero.

Axiomatized properties:
1. buDim(2, n+1) = n (classical Borsuk-Ulam: odd maps S^n → R^n vanish)
2. buDim(p, 2n) = 2n-1 for prime p (Yang-Borsuk)
3. Monotonicity: p | n → buDim(p, d) ≤ buDim(n, d)
4. Trivial group: buDim(1, d) = 0
-/

/-- The equivariant Borsuk-Ulam dimension for the cyclic group Z/n
    acting on a d-dimensional representation space.
    buDim(n, d) = minimum sphere dimension where equivariant maps vanish. -/
axiom buDim (n d : ℕ) : ℕ

-- ============================================================
-- PART II: Axiomatized Known Results
-- ============================================================

/-- Classical Borsuk-Ulam: Z/2-equivariant (odd) maps S^n → R^{n+1} vanish.
    Equivalently: buDim(2, n+1) = n.
    Trivial group Z/1: any map is Z/1-equivariant, so no dimension constraint. -/
axiom buDim_two (n : ℕ) : buDim 2 (n + 1) = n

/-- Yang-Borsuk theorem: for prime p, Z/p-equivariant maps on the
    standard complex representation have BU dimension 2n-1.
    The Z/p action is rotation by 2π/p on each complex coordinate. -/
axiom buDim_prime (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n) :
    buDim p (2 * n) = 2 * n - 1

/-- Monotonicity: if p divides n, then the Z/n BU dimension is at least
    the Z/p BU dimension (restriction of equivariance). -/
axiom buDim_mono (p n d : ℕ) (hdvd : p ∣ n) : buDim p d ≤ buDim n d

-- ============================================================
-- PART III: Consequences for Non-Prime Groups
-- ============================================================

/-- Every composite number has a prime divisor, giving a lower bound
    on the BU dimension via monotonicity. -/
theorem buDim_composite_has_prime_bound (n d : ℕ) (hn : 2 ≤ n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ buDim p d ≤ buDim n d := by
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  exact ⟨p, hp, hdvd, buDim_mono p n d hdvd⟩

/-- Z/4 lower bound: buDim(4, n+1) ≥ buDim(2, n+1) = n. -/
theorem z4_lower_bound (n : ℕ) : n ≤ buDim 4 (n + 1) := by
  have h := buDim_mono 2 4 (n + 1) ⟨2, by ring⟩
  rw [buDim_two] at h
  exact h

/-- Z/6 lower bound from Z/2: buDim(6, n+1) ≥ n. -/
theorem z6_lower_bound_z2 (n : ℕ) : n ≤ buDim 6 (n + 1) := by
  have h := buDim_mono 2 6 (n + 1) ⟨3, by ring⟩
  rw [buDim_two] at h
  exact h

/-- Z/6 lower bound from Z/3: buDim(6, 2n) ≥ 2n-1 for n ≥ 1. -/
theorem z6_lower_bound_z3 (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ buDim 6 (2 * n) := by
  have h := buDim_mono 3 6 (2 * n) ⟨2, by ring⟩
  rw [buDim_prime 3 n (by decide) hn] at h
  exact h

/-- Z/6 gets the best of both prime subgroup bounds.
    For even representation dimension 2n (n ≥ 1):
    buDim(6, 2n) ≥ 2n-1 (from both Z/2 and Z/3, since 2n-1 ≥ n). -/
theorem z6_combined_bound (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ buDim 6 (2 * n) :=
  z6_lower_bound_z3 n hn

/-- Z/p*q lower bound: for distinct primes p, q, both give bounds. -/
theorem zpq_lower_bound (p q n : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hn : 0 < n) :
    2 * n - 1 ≤ buDim (p * q) (2 * n) := by
  have h := buDim_mono p (p * q) (2 * n) (dvd_mul_right p q)
  rw [buDim_prime p n hp hn] at h
  exact h

-- ============================================================
-- PART IV: The Open Question
-- ============================================================

/-
## The Central Open Question

For composite n, is buDim(n, d) always equal to the maximum over
prime divisors p of n of buDim(p, d)?

If YES: the composite group structure adds no extra constraint.
If NO: there exist representations where the full group's symmetry
is harder to break than any prime subgroup's.

Evidence suggests YES for "standard" representations (those arising
from the regular representation). The answer for exotic representations
remains unclear.

## Specific Open Cases

1. buDim(4, 2n) = 2n-1? (Conjectured yes, same as Z/2)
2. buDim(6, 2n) = 2n-1? (Conjectured yes, maximum of Z/2 and Z/3 bounds)
3. buDim(p^2, 2n) = 2n-1 for prime p? (Z/p^2 case)
4. General: buDim(n, 2k) = max_{p|n, p prime} buDim(p, 2k)?
-/

end BorsukUlamOQ02OQ01
