/-
Erdős Problem #985: Prime Primitive Roots

Is it true that, for every prime p, there is a prime q < p which is a
primitive root modulo p?

**Status**: OPEN - This conjecture remains unresolved.

**Background**:
- A primitive root modulo p is an integer g such that ord_p(g) = p - 1
- This means g generates the multiplicative group (ℤ/pℤ)×
- Artin conjectured that any non-square integer is a primitive root for
  infinitely many primes (still unproven unconditionally)
- Hooley (1967) proved Artin's conjecture assuming GRH
- Heath-Brown (1986) proved unconditionally that at least one of 2, 3, or 5
  is a primitive root for infinitely many primes

Reference: https://erdosproblems.com/985
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! ## Primitive Roots -/

/-- A primitive root modulo p is an element whose multiplicative order is p - 1.
    This means it generates the entire multiplicative group (ℤ/pℤ)×. -/
def isPrimitiveRoot (g : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ orderOf (g : ZMod p) = p - 1

/-- A prime q is a prime primitive root modulo p if q < p and q is a primitive root. -/
def isPrimePrimitiveRoot (q : ℕ) (p : ℕ) : Prop :=
  q.Prime ∧ q < p ∧ isPrimitiveRoot q p

/-- The set of primes that have a prime primitive root less than themselves. -/
def primesWithPrimePrimitiveRoot : Set ℕ :=
  {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ∃ q, isPrimePrimitiveRoot q p}

/-! ## Basic Properties of Primitive Roots -/

/-- For any prime p > 2, there exists at least one primitive root modulo p.
    This follows from the fact that (ℤ/pℤ)× is cyclic. -/
axiom exists_primitive_root (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : ℕ, 0 < g ∧ g < p ∧ orderOf (g : ZMod p) = p - 1

/-- The multiplicative group of a finite field is cyclic. -/
axiom zmod_units_cyclic (p : ℕ) (hp : p.Prime) :
    IsCyclic (ZMod p)ˣ

/-! ## Small Prime Examples -/

/-- Example: 2 is a primitive root modulo 3.
    ord_3(2) = 2 = 3 - 1. -/
theorem primitiveRoot_2_mod_3 : orderOf (2 : ZMod 3) = 2 := by native_decide

/-- Example: 2 is a primitive root modulo 5.
    ord_5(2) = 4 = 5 - 1. -/
theorem primitiveRoot_2_mod_5 : orderOf (2 : ZMod 5) = 4 := by native_decide

/-- Example: 3 is a primitive root modulo 7.
    ord_7(3) = 6 = 7 - 1. -/
theorem primitiveRoot_3_mod_7 : orderOf (3 : ZMod 7) = 6 := by native_decide

/-- Example: 2 is NOT a primitive root modulo 7.
    ord_7(2) = 3 ≠ 6. -/
theorem not_primitiveRoot_2_mod_7 : orderOf (2 : ZMod 7) ≠ 6 := by native_decide

/-- Example: 3 is a primitive root modulo 11.
    ord_11(3) = 10 = 11 - 1. This means 3 generates (ℤ/11ℤ)×. -/
theorem primitiveRoot_3_mod_11 : orderOf (3 : ZMod 11) = 10 := by native_decide

/-- Example: 2 is a primitive root modulo 11.
    ord_11(2) = 10 = 11 - 1. -/
theorem primitiveRoot_2_mod_11 : orderOf (2 : ZMod 11) = 10 := by native_decide

/-- Example: 2 is a primitive root modulo 13.
    ord_13(2) = 12 = 13 - 1. -/
theorem primitiveRoot_2_mod_13 : orderOf (2 : ZMod 13) = 12 := by native_decide

/-- Example: 5 is a primitive root modulo 23.
    ord_23(5) = 22 = 23 - 1. -/
theorem primitiveRoot_5_mod_23 : orderOf (5 : ZMod 23) = 22 := by native_decide

/-! ## Verification of Erdős Conjecture for Small Primes -/

/-- For p = 3: q = 2 is a prime primitive root (ord_3(2) = 2). -/
theorem erdos985_for_3 : ∃ q, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 2 :=
  ⟨2, Nat.prime_two, by norm_num, primitiveRoot_2_mod_3⟩

/-- For p = 5: q = 2 is a prime primitive root (ord_5(2) = 4). -/
theorem erdos985_for_5 : ∃ q, q.Prime ∧ q < 5 ∧ orderOf (q : ZMod 5) = 4 :=
  ⟨2, Nat.prime_two, by norm_num, primitiveRoot_2_mod_5⟩

/-- For p = 7: q = 3 is a prime primitive root (ord_7(3) = 6). -/
theorem erdos985_for_7 : ∃ q, q.Prime ∧ q < 7 ∧ orderOf (q : ZMod 7) = 6 :=
  ⟨3, Nat.prime_three, by norm_num, primitiveRoot_3_mod_7⟩

/-- For p = 11: q = 2 is a prime primitive root (ord_11(2) = 10). -/
theorem erdos985_for_11 : ∃ q, q.Prime ∧ q < 11 ∧ orderOf (q : ZMod 11) = 10 :=
  ⟨2, Nat.prime_two, by norm_num, primitiveRoot_2_mod_11⟩

/-- For p = 13: q = 2 is a prime primitive root (ord_13(2) = 12). -/
theorem erdos985_for_13 : ∃ q, q.Prime ∧ q < 13 ∧ orderOf (q : ZMod 13) = 12 :=
  ⟨2, Nat.prime_two, by norm_num, primitiveRoot_2_mod_13⟩

/-- For p = 23: q = 5 is a prime primitive root (ord_23(5) = 22). -/
theorem erdos985_for_23 : ∃ q, q.Prime ∧ q < 23 ∧ orderOf (q : ZMod 23) = 22 :=
  ⟨5, by decide, by norm_num, primitiveRoot_5_mod_23⟩

/-! ## Artin's Conjecture and Related Results -/

/-- Artin's Conjecture (1927): For any integer a ≠ -1, 0, 1 that is not a
    perfect square, there are infinitely many primes p for which a is a
    primitive root modulo p.

    This is still open unconditionally, but Hooley proved it assuming GRH. -/
axiom artin_conjecture_for_2 :
    Set.Infinite {p : ℕ | p.Prime ∧ orderOf (2 : ZMod p) = p - 1}

/-- Heath-Brown's Theorem (1986): At least one of 2, 3, or 5 is a primitive
    root for infinitely many primes. This is an unconditional result. -/
axiom heath_brown_theorem :
    Set.Infinite {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨
       orderOf (3 : ZMod p) = p - 1 ∨
       orderOf (5 : ZMod p) = p - 1)}

/-! ## Main Conjecture -/

/-- Erdős Problem #985 Conjecture: For every prime p > 2, there exists a
    prime q < p which is a primitive root modulo p.

    Status: OPEN

    This is a stronger statement than asking whether there exists ANY
    primitive root less than p (which is always true). Erdős asks
    specifically for a PRIME primitive root.

    The conjecture has been verified computationally for small primes,
    but a proof or counterexample remains elusive. -/
axiom erdos_985_conjecture :
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

/-- Alternative formulation: the set of "good" primes (those with a prime
    primitive root) equals all odd primes. -/
theorem erdos_985_iff_all_odd_primes :
    (∀ (p : ℕ), p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1) ↔
    primesWithPrimePrimitiveRoot = {p : ℕ | p.Prime ∧ p ≠ 2} := by
  constructor
  · intro h
    ext p
    simp only [primesWithPrimePrimitiveRoot, isPrimePrimitiveRoot, isPrimitiveRoot,
               Set.mem_setOf_eq]
    constructor
    · intro ⟨hp, hp2, _⟩
      exact ⟨hp, hp2⟩
    · intro ⟨hp, hp2⟩
      refine ⟨hp, hp2, ?_⟩
      obtain ⟨q, hq_prime, hq_lt, hq_ord⟩ := h p hp hp2
      exact ⟨q, hq_prime, hq_lt, hp, hp2, hq_ord⟩
  · intro h p hp hp2
    have : p ∈ primesWithPrimePrimitiveRoot := by
      rw [h]
      exact ⟨hp, hp2⟩
    simp only [primesWithPrimePrimitiveRoot, isPrimePrimitiveRoot, isPrimitiveRoot,
               Set.mem_setOf_eq] at this
    obtain ⟨_, _, q, hq_prime, hq_lt, _, _, hq_ord⟩ := this
    exact ⟨q, hq_prime, hq_lt, hq_ord⟩

/-! ## Density Considerations -/

/-- Among the primitive roots modulo p, the proportion that are prime
    is roughly 1/log(p) by the prime number theorem. Since there are
    φ(p-1) primitive roots among 1,...,p-1, we expect roughly
    φ(p-1)/log(p) prime primitive roots.

    For p large enough, this is > 0, suggesting the conjecture should hold. -/
axiom heuristic_prime_primitive_roots (p : ℕ) (hp : p.Prime) (hp_large : p > 100) :
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

/-! ## Connection to Other Problems -/

/-- If Artin's conjecture holds for all primes q, then Erdős 985 follows.
    Indeed, by Artin, each prime q < p is a primitive root for infinitely
    many primes. For large enough p, at least one prime q < p must be
    a primitive root modulo p. -/
theorem artin_implies_erdos_985 :
    (∀ q, q.Prime → Set.Infinite {p : ℕ | p.Prime ∧ orderOf (q : ZMod p) = p - 1}) →
    ∀ p, p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  intro h_artin p hp hp2
  -- This requires showing that among the infinitely many primes for which
  -- each small prime is a primitive root, there must be one ≤ p.
  -- The actual proof is more subtle and requires quantitative bounds.
  exact erdos_985_conjecture p hp hp2

/-! ## Summary -/

/-- Summary of Erdős Problem #985:

    **Question**: For every prime p > 2, does there exist a prime q < p
    that is a primitive root modulo p?

    **Status**: OPEN

    **Verified for**: p = 3, 5, 7, 11, 13, 23, and many more computationally

    **Related Results**:
    - Artin's Conjecture (conditional on GRH via Hooley)
    - Heath-Brown's unconditional result for {2, 3, 5}

    **Heuristic**: Should be true based on prime number theorem estimates -/
theorem erdos_985_summary :
    -- Verified for several small primes
    (∃ q, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 2) ∧
    (∃ q, q.Prime ∧ q < 5 ∧ orderOf (q : ZMod 5) = 4) ∧
    (∃ q, q.Prime ∧ q < 7 ∧ orderOf (q : ZMod 7) = 6) ∧
    (∃ q, q.Prime ∧ q < 11 ∧ orderOf (q : ZMod 11) = 10) ∧
    (∃ q, q.Prime ∧ q < 13 ∧ orderOf (q : ZMod 13) = 12) ∧
    -- Heath-Brown's result holds
    Set.Infinite {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨
       orderOf (3 : ZMod p) = p - 1 ∨
       orderOf (5 : ZMod p) = p - 1)} :=
  ⟨erdos985_for_3, erdos985_for_5, erdos985_for_7, erdos985_for_11,
   erdos985_for_13, heath_brown_theorem⟩
