/-
  Symmetric Group Borsuk-Ulam: Largest-Prime-Subgroup Conjecture
  (OQ-02-OQ-01-OQ-03-OQ-02)

  Open Question (sub-question of `BorsukUlamOQ02OQ01OQ03`):

      For S_n, is symBUDim n d = buDim_{p*} d = 2⌊d/2⌋ − 1,
      where p* is the largest prime ≤ n?

  Background. The parent file `BorsukUlamOQ02OQ01OQ03.lean` axiomatizes
  the equivariant Borsuk-Ulam dimension `symBUDim n d` for the symmetric
  group S_n acting on a d-dimensional real representation, and proves the
  prime-subgroup lower bound: for every prime p ≤ n,

      buDim p d ≤ symBUDim n d                              (sym_has_cyclic_prime)

  Combined with the cyclic-prime axiom buDim p (2k) = 2k − 1
  (`buDim_prime`, axiomatized in `BorsukUlamOQ02OQ01.lean`), this gives
  the unconditional lower bound symBUDim n (2k) ≥ 2k − 1 for n ≥ 2.

  The OPEN question is the matching upper bound — i.e. whether
  symBUDim n d equals the cyclic bound buDim_{p*} d for the LARGEST
  prime p* ≤ n. We axiomatize this conjectured equality and derive the
  explicit floor formula as a consequence.

  Bertrand's postulate (Mathlib `Nat.exists_prime_lt_and_le_two_mul`)
  guarantees that for n ≥ 2 the largest prime p* ≤ n satisfies p* > n/2,
  so the conjecture differs from the trivial 2 ≤ p* ≤ n statement only
  by a factor of at most 2.

  References:
  - Borsuk 1933 (original BU theorem)
  - Fadell-Husseini 1988 (S_n equivariant index)
  - Matoušek 2003, "Using the Borsuk-Ulam Theorem", Ch. 6
  - tom Dieck 1987, "Transformation Groups"
  - Lovász 1978 (BU/chromatic number connection — Kneser graphs)
  - Bertrand 1845 / Erdős 1932 (postulate p ∈ (n, 2n])
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic
import Proofs.BorsukUlamOQ02OQ01OQ03

namespace BorsukUlamOQ02OQ01OQ03OQ02

open BorsukUlamNonCyclic BorsukUlamOQ02OQ01 Nat

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: LARGEST PRIME ≤ n
-- ═══════════════════════════════════════════════════════════════════════

/-- The largest prime p ≤ n. For n ≤ 1 this falls back to 0; for n ≥ 2
    it is a genuine prime, witnessed by `largestPrimeBelow_prime`. -/
noncomputable def largestPrimeBelow (n : ℕ) : ℕ :=
  Nat.findGreatest Nat.Prime n

/-- `largestPrimeBelow n ≤ n` always. -/
theorem largestPrimeBelow_le (n : ℕ) : largestPrimeBelow n ≤ n :=
  Nat.findGreatest_le n

/-- For n ≥ 2, `largestPrimeBelow n` is a prime. The witness is p = 2,
    which is prime and ≤ n. -/
theorem largestPrimeBelow_prime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime (largestPrimeBelow n) :=
  Nat.findGreatest_spec hn Nat.prime_two

/-- For n = 2, the largest prime ≤ n is exactly 2. -/
theorem largestPrimeBelow_two : largestPrimeBelow 2 = 2 := by
  unfold largestPrimeBelow
  -- 2 is prime and 2 ≤ 2, so findGreatest returns ≥ 2; and findGreatest ≤ 2.
  have h1 : 2 ≤ Nat.findGreatest Nat.Prime 2 :=
    Nat.le_findGreatest (le_refl 2) Nat.prime_two
  have h2 : Nat.findGreatest Nat.Prime 2 ≤ 2 := Nat.findGreatest_le 2
  omega

/-- **Bertrand bound for largestPrimeBelow.**
    For n ≥ 2, the largest prime ≤ n is strictly greater than n / 2.

    Proof: Bertrand's postulate applied to m = n / 2 (which is ≥ 1 for
    n ≥ 2) gives a prime p with n/2 < p ≤ 2·(n/2) ≤ n. Since p is prime
    and p ≤ n, we have p ≤ largestPrimeBelow n. Combined with n/2 < p
    this gives the bound. -/
theorem largestPrimeBelow_gt_half (n : ℕ) (hn : 2 ≤ n) :
    n / 2 < largestPrimeBelow n := by
  have hhalf_ne : (n / 2) ≠ 0 := by
    have : 1 ≤ n / 2 := by omega
    omega
  obtain ⟨p, hpp, hp1, hp2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n / 2) hhalf_ne
  -- p prime, n/2 < p, p ≤ 2 * (n/2)
  have h2half : 2 * (n / 2) ≤ n := by
    have := Nat.div_add_mod n 2
    omega
  have hpn : p ≤ n := hp2.trans h2half
  have hple : p ≤ largestPrimeBelow n := Nat.le_findGreatest hpn hpp
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: UNCONDITIONAL LOWER BOUND (axiom-free up to existing axioms)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Lower bound for S_n via the largest prime subgroup.**

    For n ≥ 2, S_n contains Z/p* (where p* is the largest prime ≤ n)
    as a cyclic subgroup, so by subgroup monotonicity (axiomatized as
    `sym_has_cyclic_prime` in the parent file):

        buDim p* d ≤ symBUDim n d.

    This is the strongest *known* unconditional lower bound from
    cyclic-subgroup structure alone. -/
theorem symBUDim_ge_largest_prime (n d : ℕ) (hn : 2 ≤ n) :
    buDim (largestPrimeBelow n) d ≤ symBUDim n d :=
  sym_has_cyclic_prime n d (largestPrimeBelow n)
    (largestPrimeBelow_prime n hn) (largestPrimeBelow_le n)

/-- **Explicit lower-bound floor formula.**

    For n ≥ 2 and k ≥ 1, the symmetric-group BU dimension on a 2k-dim
    representation satisfies symBUDim n (2k) ≥ 2k − 1, since
    symBUDim n (2k) ≥ buDim p* (2k) = 2k − 1 by the Yang-Borsuk
    cyclic-prime axiom `buDim_prime`. -/
theorem symBUDim_lower_bound (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim n (2 * k) := by
  have hp : Nat.Prime (largestPrimeBelow n) := largestPrimeBelow_prime n hn
  have h := symBUDim_ge_largest_prime n (2 * k) hn
  rwa [buDim_prime (largestPrimeBelow n) k hp hk] at h

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: THE CONJECTURED EQUALITY (axiomatized — main open question)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Conjectural equality — the open question.**

    The S_n-equivariant Borsuk-Ulam dimension equals the cyclic Borsuk-
    Ulam dimension of its largest prime-order cyclic subgroup. Equivalently:
    the symmetric-group structure of S_n adds NOTHING beyond the largest
    cyclic subgroup of prime order — the "extra" non-cyclic structure
    (representation-theoretic obstructions, Klein-4 subgroups in S_4 etc.)
    contributes no additional lower bound.

    Status: OPEN. A proof would require either
      (a) a Fadell-Husseini-style equivariant cohomology computation
          showing the upper bound symBUDim n d ≤ buDim p* d, or
      (b) an explicit equivariant map S^{buDim p* d} → V achieving the
          dimension on representations V of S_n.
    Neither is in Mathlib at present.

    This axiom encodes the conjecture as a working assumption. The
    lower-bound direction is `symBUDim_ge_largest_prime` (theorem). -/
axiom symBUDim_eq_largest_prime (n d : ℕ) (hn : 2 ≤ n) :
    symBUDim n d = buDim (largestPrimeBelow n) d

/-- **Tight floor formula (assuming the conjecture).**

    Combining the conjectured equality with the cyclic-prime axiom
    `buDim_prime` gives the closed form

        symBUDim n (2k) = 2k − 1   for n ≥ 2, k ≥ 1.

    This shows that, conditional on the equality conjecture, the
    symmetric-group BU dimension matches the classical Yang-Borsuk
    dimension. -/
theorem symBUDim_eq_floor_formula (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    symBUDim n (2 * k) = 2 * k - 1 := by
  rw [symBUDim_eq_largest_prime n (2 * k) hn]
  exact buDim_prime (largestPrimeBelow n) k (largestPrimeBelow_prime n hn) hk

/-- **Consistency with `symBUDim_two`.**

    For n = 2, p* = 2 and the new conjectural axiom collapses to
    `symBUDim 2 d = buDim 2 d`, which is exactly the standalone
    axiom `symBUDim_two` from the parent file. -/
theorem symBUDim_eq_largest_prime_two (d : ℕ) :
    symBUDim 2 d = buDim 2 d := by
  rw [symBUDim_eq_largest_prime 2 d (le_refl 2), largestPrimeBelow_two]

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: CONCRETE CASES
-- ═══════════════════════════════════════════════════════════════════════

/-- **n = 3: largest prime ≤ 3 is 3.** -/
example : largestPrimeBelow 3 = 3 := by
  unfold largestPrimeBelow
  have h1 : 3 ≤ Nat.findGreatest Nat.Prime 3 :=
    Nat.le_findGreatest (le_refl 3) Nat.prime_three
  have h2 : Nat.findGreatest Nat.Prime 3 ≤ 3 := Nat.findGreatest_le 3
  omega

/-- **n = 4: largest prime ≤ 4 is 3** (4 is not prime). -/
example : largestPrimeBelow 4 = 3 := by
  unfold largestPrimeBelow
  have h1 : 3 ≤ Nat.findGreatest Nat.Prime 4 :=
    Nat.le_findGreatest (by norm_num) Nat.prime_three
  have h2 : Nat.findGreatest Nat.Prime 4 ≤ 4 := Nat.findGreatest_le 4
  -- Need to rule out findGreatest = 4. 4 is not prime.
  have hP : Nat.Prime (Nat.findGreatest Nat.Prime 4) :=
    Nat.findGreatest_spec (by norm_num : 2 ≤ 4) Nat.prime_two
  -- If findGreatest = 4, then 4 would be prime. It isn't.
  by_contra hne
  interval_cases (Nat.findGreatest Nat.Prime 4)
  · exact hne rfl
  · norm_num at hP

/-- **n = 4 lower bound.** symBUDim 4 (2k) ≥ 2k − 1 (from Z/3 subgroup). -/
example (k : ℕ) (hk : 0 < k) : 2 * k - 1 ≤ symBUDim 4 (2 * k) :=
  symBUDim_lower_bound 4 k (by norm_num) hk

/-- **n = 5 lower bound.** symBUDim 5 (2k) ≥ 2k − 1 (from Z/5 subgroup). -/
example (k : ℕ) (hk : 0 < k) : 2 * k - 1 ≤ symBUDim 5 (2 * k) :=
  symBUDim_lower_bound 5 k (by norm_num) hk

/-- **Tight formula at n = 5, k = 3** (assuming conjecture). -/
example : symBUDim 5 6 = 5 := by
  have h := symBUDim_eq_floor_formula 5 3 (by norm_num) (by norm_num)
  norm_num at h
  exact h

end BorsukUlamOQ02OQ01OQ03OQ02
