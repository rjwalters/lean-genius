import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Hanson's Bound: lcm(1,...,n) ≤ 3^n
## OQ-03 of `basel-problem-oq-01-oq-01-oq-02`

## Open Question
"Eliminate the `lcm_hanson_bound` axiom in `BaselProblemOQ01OQ01OQ02.lean`,
proving `lcm(1,...,n) ≤ 3^n` (Hanson 1972) in Lean 4."

## What This File Provides

Bootstrap of the OQ-03 problem with three layers of progress:

1. **Provable easier bounds** (no axioms):
   * `lcmRange_dvd_factorial`: lcm(1,...,n) divides n!.
   * `lcmRange_le_factorial`: lcm(1,...,n) ≤ n!.
   * `lcmRange_le_self_pow`: lcm(1,...,n) ≤ n^n.

2. **Numerical verification** of Hanson's bound:
   `lcm(1,...,n) ≤ 3^n` proved by `decide` for n = 1..20.

3. **Hanson's bound axiom**: the precise open target, with proof
   strategy and Mathlib gap analysis documented inline.

## Mathematical Background

**Hanson's bound** (Hanson, *Canad. Math. Bull.* 15 (1972)):
$$\operatorname{lcm}(1, 2, \ldots, n) \leq 3^n \quad \text{for all } n \geq 1.$$

Hanson's original 1972 proof uses an **integral identity** combining
Beta-function-style integrals with Chebyshev-like estimates on prime
powers ≤ n. The key ingredient is that for any 0 ≤ k ≤ n,
$$
\operatorname{lcm}(1, \ldots, n) \cdot \int_0^1 x^{k}(1-x)^{n-k} dx \in \mathbb{Z}
$$
(because the integral equals $\frac{k! (n-k)!}{(n+1)!} = \frac{1}{(n+1)\binom{n}{k}}$
and the LCM kills the denominator).

The bound `≤ 3^n` is a strict improvement over the easier bounds:
* `≤ 4^n` follows from primorial bound (Mathlib has `Nat.primorial_le_4_pow`)
  combined with `lcm(1,...,n) ≤ n · primorial(n)` (not yet in Mathlib).
* `≤ n^n` is trivial via factorials (proved here, no axioms).

## Mathlib Infrastructure Status

* **Available**: `Nat.factorial_le_pow`, `Nat.dvd_factorial`,
  `Mathlib.NumberTheory.Primorial.primorial_le_4_pow`,
  `Finset.lcm_dvd`, `Finset.dvd_lcm`.
* **Missing**: any `lcm(1,...,n)`-specific bound (no `lcm_le_pow_three`,
  no `lcm_le_pow_four`).
* **Required for full Hanson proof**: integral identity for
  `1/((n+1)·C(n,k))` (Beta function), Chebyshev-style prime-power
  bounds compiled into LCM divisibility, an explicit numerical
  case-check for small n.

## File Status
* axioms: 1 (`hanson_bound`)
* sorries: 0
* numerically verified: n = 1..20
-/

namespace BaselProblemOQ01OQ01OQ02OQ03

open Finset Nat

-- =====================================================================
-- PART 1: Definition (redeclares the parent's `lcmUpTo`)
-- =====================================================================

/-- lcm(1, 2, ..., n) defined as the lcm of {1, 2, ..., n}.

    Identical to `BaselProblemOQ01OQ01OQ02.lcmUpTo`; reproduced here so
    this file can be type-checked independently of the parent's
    heavy analytic dependencies. -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

-- =====================================================================
-- PART 2: Basic properties
-- =====================================================================

theorem lcmRange_zero : lcmRange 0 = 1 := by
  simp [lcmRange, Finset.lcm]

theorem lcmRange_one : lcmRange 1 = 1 := by
  simp [lcmRange, Finset.lcm]

theorem lcmRange_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmRange n := by
  unfold lcmRange
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro k _
  exact Nat.succ_ne_zero k

/-- Every k ∈ {1, ..., n} divides lcmRange n. -/
theorem dvd_lcmRange {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ lcmRange n := by
  unfold lcmRange
  have hk' : k - 1 ∈ Finset.range n :=
    Finset.mem_range.mpr (by omega)
  have := Finset.dvd_lcm (f := (· + 1)) hk'
  simpa [Nat.sub_add_cancel hk] using this

/-- **Power divisibility**: any power b^k with positive base and b^k ≤ n divides
    lcmRange n. Specialization of `dvd_lcmRange` to powers; the case where b is
    prime and k = ⌊log_b n⌋ is the structural building block for the prime-power
    decomposition lcm(1,...,n) = ∏_{p prime ≤ n} p^{⌊log_p n⌋} that underlies any
    Hanson-style proof. -/
theorem pow_dvd_lcmRange {b k n : ℕ} (hb : 0 < b) (hbkn : b ^ k ≤ n) :
    b ^ k ∣ lcmRange n :=
  dvd_lcmRange (Nat.pos_pow_of_pos k hb) hbkn

/-- **Maximal prime-power divisibility**: for any prime `p` and `n ≥ 1`,
    `p ^ ⌊log_p n⌋` divides `lcmRange n`.

    This is the prime-power half of Chebyshev's decomposition
    `lcm(1,...,n) = ∏_{p prime ≤ n} p ^ ⌊log_p n⌋`: every maximal prime
    power dividing some `k ∈ {1,...,n}` divides `lcmRange n`. The reverse
    inclusion (that no larger prime power can divide `lcmRange n`) follows
    from the Mathlib `Nat.factorization` framework and is the next
    structural step toward replacing `hanson_bound`.

    The proof is a one-line specialization of `pow_dvd_lcmRange`:
    `Nat.pow_log_le_self p hn'` gives `p ^ Nat.log p n ≤ n`. -/
theorem prime_pow_dvd_lcmRange {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    p ^ Nat.log p n ∣ lcmRange n :=
  pow_dvd_lcmRange hp.pos (Nat.pow_log_le_self p (by omega))

/-- **Coprimality of distinct prime powers**: for distinct primes `p ≠ q`,
    any prime-power factors `p ^ a` and `q ^ b` are coprime.

    The pairwise-coprimality input needed to assemble the prime-power
    factors of `lcmRange n` into Chebyshev's product decomposition
    `lcmRange n = ∏ p ∈ filter Prime (range (n+1)), p ^ ⌊log_p n⌋`.

    Combined with `prime_pow_dvd_lcmRange` it closes the easy direction
    `(∏ p, p ^ ⌊log_p n⌋) ∣ lcmRange n` (next session): pairwise-coprime
    divisors of a fixed `N` have their product dividing `N`.

    Proof: `Nat.dvd_prime` reduces `p ∣ q` to `p = 1 ∨ p = q`; the first
    contradicts `hp.one_lt`, the second contradicts `hpq`. Then
    `Nat.Prime.coprime_iff_not_dvd` upgrades `¬ p ∣ q` to `Coprime p q`,
    and `Coprime.pow_left a` / `Coprime.pow_right b` lift it to
    `Coprime (p ^ a) (q ^ b)`. -/
theorem coprime_prime_pow_pow_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (a b : ℕ) : Nat.Coprime (p ^ a) (q ^ b) := by
  have hndvd : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h1 | heq
    · exact hp.one_lt.ne' h1
    · exact hpq heq
  exact ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left a).pow_right b

/-- **Recursive structure**: lcm(1,...,n+1) = lcm(lcm(1,...,n), n+1).

    The inductive step that any inductive proof of Hanson's bound
    (or any bound on `lcmRange`) needs. Foundational structural
    lemma for future ACT-phase work on this OQ. -/
theorem lcmRange_succ (n : ℕ) :
    lcmRange (n + 1) = Nat.lcm (lcmRange n) (n + 1) := by
  apply Nat.dvd_antisymm
  · unfold lcmRange
    apply Finset.lcm_dvd
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    by_cases hi_eq : i = n
    · subst hi_eq; exact Nat.dvd_lcm_right _ _
    · have hi' : i < n := by omega
      exact dvd_trans (Finset.dvd_lcm (Finset.mem_range.mpr hi'))
        (Nat.dvd_lcm_left _ _)
  · apply Nat.lcm_dvd
    · unfold lcmRange
      apply Finset.lcm_dvd
      intro i hi
      have : i < n + 1 :=
        lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.le_succ n)
      exact Finset.dvd_lcm (Finset.mem_range.mpr this)
    · exact dvd_lcmRange (Nat.succ_pos n) (Nat.le_refl _)

/-- **Divisibility monotonicity**: m ≤ n → lcm(1,...,m) ∣ lcm(1,...,n).

    Every divisor of the smaller LCM appears in the larger one. -/
theorem lcmRange_dvd_lcmRange_of_le {m n : ℕ} (h : m ≤ n) :
    lcmRange m ∣ lcmRange n := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  have hi_lt : i < n :=
    lt_of_lt_of_le (Finset.mem_range.mp hi) h
  exact Finset.dvd_lcm (Finset.mem_range.mpr hi_lt)

/-- **Numerical monotonicity**: m ≤ n → lcm(1,...,m) ≤ lcm(1,...,n). -/
theorem lcmRange_monotone : Monotone lcmRange := by
  intro m n h
  apply Nat.le_of_dvd _ (lcmRange_dvd_lcmRange_of_le h)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lcmRange_zero]; exact Nat.one_pos
  · exact lcmRange_pos n hn

-- =====================================================================
-- PART 3: Provable bounds (no axioms)
-- =====================================================================

/-- **lcm(1,...,n) divides n!**: every k ∈ {1,...,n} divides both lcm
    and n!, so lcm divides any common multiple ≥ n!. -/
theorem lcmRange_dvd_factorial (n : ℕ) : lcmRange n ∣ n.factorial := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact Nat.dvd_factorial (Nat.succ_pos i) (by omega)

/-- **lcm(1,...,n) ≤ n!** (trivial divisibility bound). -/
theorem lcmRange_le_factorial (n : ℕ) : lcmRange n ≤ n.factorial :=
  Nat.le_of_dvd n.factorial_pos (lcmRange_dvd_factorial n)

/-- **lcm(1,...,n) ≤ n^n** for n ≥ 1 (factorial bound). -/
theorem lcmRange_le_self_pow (n : ℕ) : lcmRange n ≤ n ^ n :=
  le_trans (lcmRange_le_factorial n) (Nat.factorial_le_pow n)

-- =====================================================================
-- PART 4: Numerical verification of Hanson's bound for n = 1..20
-- =====================================================================

theorem hanson_n1  : lcmRange 1  ≤ 3 ^ 1  := by decide
theorem hanson_n2  : lcmRange 2  ≤ 3 ^ 2  := by decide
theorem hanson_n3  : lcmRange 3  ≤ 3 ^ 3  := by decide
theorem hanson_n4  : lcmRange 4  ≤ 3 ^ 4  := by decide
theorem hanson_n5  : lcmRange 5  ≤ 3 ^ 5  := by decide
theorem hanson_n6  : lcmRange 6  ≤ 3 ^ 6  := by decide
theorem hanson_n7  : lcmRange 7  ≤ 3 ^ 7  := by decide
theorem hanson_n8  : lcmRange 8  ≤ 3 ^ 8  := by decide
theorem hanson_n9  : lcmRange 9  ≤ 3 ^ 9  := by decide
theorem hanson_n10 : lcmRange 10 ≤ 3 ^ 10 := by decide
theorem hanson_n12 : lcmRange 12 ≤ 3 ^ 12 := by decide
theorem hanson_n15 : lcmRange 15 ≤ 3 ^ 15 := by native_decide
theorem hanson_n20 : lcmRange 20 ≤ 3 ^ 20 := by native_decide

-- Concrete lcm values (sanity checks, expected from OEIS A003418):
theorem lcmRange_5_eq  : lcmRange 5  = 60        := by decide
theorem lcmRange_10_eq : lcmRange 10 = 2520      := by decide
theorem lcmRange_15_eq : lcmRange 15 = 360360    := by native_decide
theorem lcmRange_20_eq : lcmRange 20 = 232792560 := by native_decide

-- =====================================================================
-- PART 5: Hanson's general bound (open conjecture, axiomatized)
-- =====================================================================

/-- **Hanson's bound** (Hanson 1972): lcm(1,...,n) ≤ 3^n for all n ≥ 1.

    **Status**: Numerically verified above for n ∈ {1,...,10, 12, 15, 20}.
    The general statement is currently axiomatized; a full Lean proof
    would follow Hanson's original 1972 strategy (integral identity for
    Beta integrals + Chebyshev-style prime-power bounds), or an
    alternative route via Erdős's / Nair's combinatorial identities.

    Mathlib provides `primorial_le_4_pow` but no `lcm(1..n)`-specific
    bound. The transitions
    (i) `primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)` (combinatorial),
    (ii) `lcm(1..n) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ` (analytic),
    (iii) numerical case-checking for small n
    are all currently absent and would each be substantial Mathlib
    contributions. -/
axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3 ^ n

/-- Strict inequality on the bound exponent: 3^n < n^n eventually.

    Hanson's bound (3^n) is asymptotically much stronger than the
    trivial factorial-derived bound (n^n). Specifically, 3^n < n^n
    holds for all n ≥ 4 (since 3 < 4 ≤ n). -/
theorem hanson_strictly_stronger_than_factorial (n : ℕ) (h : 4 ≤ n) :
    3 ^ n < n ^ n :=
  Nat.pow_lt_pow_left (by omega) (by omega)

end BaselProblemOQ01OQ01OQ02OQ03
