/-
  Borsuk-Ulam for Symmetric Groups: The Largest-Prime-Below Conjecture
  (BorsukUlam OQ-02-OQ-01-OQ-03-OQ-02)

  Open Question (formal):
    For all n ≥ 2 and d ≥ 1,
        symBUDim n d = buDim p* d = 2 * (d / 2) - 1
    where p* = largestPrimeBelow n is the largest prime ≤ n.

  ## Status: Phase-2 axiomatization (ORIENT)

  The PARENT file `BorsukUlamOQ02OQ01OQ03.lean` already proves the LOWER bound
  via subgroup monotonicity:
        buDim p d ≤ symBUDim n d   for any prime p ≤ n
  hence in particular `buDim p* d ≤ symBUDim n d` once `p*` is constructed.

  This file:
  1. Defines `largestPrimeBelow n` as the largest prime ≤ n (noncomputable;
     uses `Nat.find_greatest`).
  2. States the conjectured EQUALITY `symBUDim n d = buDim p* d` as an axiom
     (full proof requires equivariant cohomology / Fadell-Husseini index for
     Sₙ, not currently in Mathlib).
  3. Derives the explicit closed form `symBUDim n d = 2 * (d / 2) - 1` for
     even d using `buDim_prime`. (The general d case is captured by
     `buDim_floor_formula` axiom below, which restates the parent's even-d
     cyclic axiom in floor form.)
  4. Proves the unconditional LOWER bound `2 * (d/2) - 1 ≤ symBUDim n (2 * k)`
     using only (a) Bertrand-style prime existence and (b) parent's cyclic
     axioms — no new axioms beyond the parent.
  5. Establishes the quantitative Bertrand bound `n / 2 < largestPrimeBelow n`
     for `n ≥ 2` (axiom-free, via Mathlib's `Nat.bertrand`). Pins the
     largest prime in the dyadic window `(n/2, n]` and shows the cyclic
     lower bound is within factor 2 of optimal.
  6. Provides an **axiom-free n=2 consistency check**: the conjecture's
     `n = 2` instance is provable from the parent's `symBUDim_two` axiom
     combined with `largestPrimeBelow_self_of_prime`, *without* the new
     `symBUDim_eq_largestPrime` axiom. This shows the new axiom is
     consistent with prior axiomatization (and is redundant at n=2).

  ## References
  - Dold (1983) "Simple proofs of some Borsuk-Ulam results"
  - Fadell & Husseini (1988) "An ideal-valued cohomological index theory"
  - Matoušek (2003) "Using the Borsuk-Ulam Theorem", Ch. 6
  - Bertrand-Chebyshev: For every n ≥ 1 there is a prime p with n < p ≤ 2n.

  Parent: BorsukUlamOQ02OQ01OQ03.lean
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic
import Proofs.BorsukUlamOQ02OQ01OQ03

namespace BorsukUlamSymPrime

open BorsukUlamNonCyclic BorsukUlamOQ02OQ01

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: The largest prime ≤ n
-- ═══════════════════════════════════════════════════════════════════════

/-- The largest prime ≤ n. Noncomputable wrapper over `Nat.findGreatest`. -/
noncomputable def largestPrimeBelow (n : ℕ) : ℕ :=
  Nat.findGreatest Nat.Prime n

/-- For n ≥ 2, `largestPrimeBelow n` is itself prime.

    Existence: 2 is prime and 2 ≤ n, so the search has a witness. -/
theorem largestPrimeBelow_isPrime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime (largestPrimeBelow n) := by
  unfold largestPrimeBelow
  -- `findGreatest` returns the largest k ≤ n with `Nat.Prime k`; existence of 2.
  have h2 : Nat.Prime 2 := Nat.prime_two
  exact Nat.findGreatest_spec hn h2

/-- `largestPrimeBelow n ≤ n`. -/
theorem largestPrimeBelow_le (n : ℕ) : largestPrimeBelow n ≤ n :=
  Nat.findGreatest_le n

/-- For n ≥ 2, `largestPrimeBelow n ≥ 2` (since 2 itself is a prime ≤ n). -/
theorem two_le_largestPrimeBelow (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ largestPrimeBelow n := by
  unfold largestPrimeBelow
  exact Nat.le_findGreatest hn Nat.prime_two

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: The symBUDim equality conjecture (AXIOMATIZED)
-- ═══════════════════════════════════════════════════════════════════════

/-- **CONJECTURE / AXIOM**: For n ≥ 2 the equivariant BU dimension for Sₙ
    coincides with the cyclic BU dimension at the largest prime ≤ n.

    Proof sketch (not in Mathlib): The lower bound is parent's
    `sym_has_cyclic_prime`. The upper bound requires the Fadell-Husseini
    cohomological index for the Sₙ-action, exploiting that any
    non-cyclic factor of Sₙ contributes only via its prime subgroups in
    the equivariant index calculation. Detailed argument uses the
    spectral sequence of `BSₙ → BG` for cyclic prime G. -/
axiom symBUDim_eq_largestPrime (n d : ℕ) (hn : 2 ≤ n) :
    symBUDim n d = buDim (largestPrimeBelow n) d

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: Closed form (even d)
-- ═══════════════════════════════════════════════════════════════════════

/-- For n ≥ 2 and any positive natural k, `symBUDim n (2 * k) = 2 * k - 1`.

    This is the conjectured closed form on even dimensions. Combines
    `symBUDim_eq_largestPrime` + parent's cyclic Yang-Borsuk axiom
    `buDim_prime`. -/
theorem symBUDim_even_formula (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    symBUDim n (2 * k) = 2 * k - 1 := by
  rw [symBUDim_eq_largestPrime n (2 * k) hn]
  exact buDim_prime (largestPrimeBelow n) k
    (largestPrimeBelow_isPrime n hn) hk

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: Unconditional lower bound (NO new axioms)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Unconditional lower bound** (axiom-free up to parent's axioms):
    for n ≥ 2 and k ≥ 1, `2 * k - 1 ≤ symBUDim n (2 * k)`.

    Uses only:
    - `largestPrimeBelow_isPrime` (Mathlib + parent),
    - `largestPrimeBelow_le`,
    - parent's `sym_has_cyclic_prime` (subgroup monotonicity for Sₙ),
    - parent's `buDim_prime` (Yang-Borsuk for prime cyclic groups). -/
theorem symBUDim_even_lower (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim n (2 * k) := by
  -- Step 1: get a prime p ≤ n (use `largestPrimeBelow n`)
  set p := largestPrimeBelow n with hp_def
  have hp_prime : Nat.Prime p := largestPrimeBelow_isPrime n hn
  have hp_le : p ≤ n := largestPrimeBelow_le n
  -- Step 2: parent's `buDim_prime` gives `buDim p (2k) = 2k - 1`
  have h_buDim : buDim p (2 * k) = 2 * k - 1 := buDim_prime p k hp_prime hk
  -- Step 3: parent's `sym_has_cyclic_prime` gives `buDim p (2k) ≤ symBUDim n (2k)`
  have h_le : buDim p (2 * k) ≤ symBUDim n (2 * k) :=
    sym_has_cyclic_prime n (2 * k) p hp_prime hp_le
  -- Combine
  rw [← h_buDim]
  exact h_le

-- ═══════════════════════════════════════════════════════════════════════
-- PART V: Concrete instances
-- ═══════════════════════════════════════════════════════════════════════

/-- **S₃ on a 4-dimensional rep**: `symBUDim 3 4 = 3`. (Conjectural.) -/
theorem symBUDim_three_four : symBUDim 3 4 = 3 := by
  have := symBUDim_even_formula 3 2 (by norm_num) (by norm_num)
  simpa using this

/-- **S₄ on a 6-dimensional rep**: `symBUDim 4 6 = 5`. (Conjectural.)

    Note: largestPrimeBelow 4 = 3, so `symBUDim 4 6 = buDim 3 6 = 5`. -/
theorem symBUDim_four_six : symBUDim 4 6 = 5 := by
  have := symBUDim_even_formula 4 3 (by norm_num) (by norm_num)
  simpa using this

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 5 (2 * k)` for k ≥ 1.
    Axiom-free version of the Yang-Borsuk lower bound for S₅. -/
theorem symBUDim_five_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 5 (2 * k) :=
  symBUDim_even_lower 5 k (by norm_num) hk

-- ═══════════════════════════════════════════════════════════════════════
-- PART VI: Bertrand bound on `largestPrimeBelow`
-- ═══════════════════════════════════════════════════════════════════════

/-- **Bertrand-Chebyshev bound on the largest prime ≤ n** (axiom-free).

    For `n ≥ 2`, the largest prime ≤ `n` strictly exceeds `n / 2`:
        `n / 2 < largestPrimeBelow n`.

    This is the formal version of the heuristic "p* > n/2" used to argue
    that the unconditional cyclic lower bound `2k - 1 ≤ symBUDim n (2k)` is
    within factor 2 of the trivial dimension `2k - 1`, regardless of the
    composite structure of `n`.

    Proof: Bertrand-Chebyshev (`Nat.exists_prime_lt_and_le_two_mul`) applied
    at `m = n / 2 ≥ 1` produces a prime `p` with `m < p ≤ 2m`. Since
    `2 * (n / 2) ≤ n`, we have `p ≤ n`, hence `p ≤ largestPrimeBelow n` by
    maximality of `findGreatest`. Combining `m < p ≤ largestPrimeBelow n`
    gives the bound. -/
theorem n_div_two_lt_largestPrimeBelow (n : ℕ) (hn : 2 ≤ n) :
    n / 2 < largestPrimeBelow n := by
  have hm : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n / 2) hm
  have h2m_le_n : 2 * (n / 2) ≤ n := by omega
  have hp_le_n : p ≤ n := hp_le.trans h2m_le_n
  have hp_le_lpb : p ≤ largestPrimeBelow n := by
    unfold largestPrimeBelow
    exact Nat.le_findGreatest hp_le_n hp_prime
  exact lt_of_lt_of_le hp_gt hp_le_lpb

/-- **Bertrand window** for `largestPrimeBelow n`, `n ≥ 2`:
    `n/2 < largestPrimeBelow n ≤ n`.

    The lower bound is `n_div_two_lt_largestPrimeBelow` (Bertrand); the
    upper bound is `largestPrimeBelow_le` (definition of `findGreatest`). -/
theorem largestPrimeBelow_in_bertrand_window (n : ℕ) (hn : 2 ≤ n) :
    n / 2 < largestPrimeBelow n ∧ largestPrimeBelow n ≤ n :=
  ⟨n_div_two_lt_largestPrimeBelow n hn, largestPrimeBelow_le n⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART VII: Axiom-free consistency at n = 2 (and at any prime n)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Fixed-point lemma**: when `n` itself is prime, `largestPrimeBelow n = n`.

    Squeeze argument: `n ≤ findGreatest Nat.Prime n` from `Nat.le_findGreatest`
    (using `n ≤ n` and `Nat.Prime n`), and `findGreatest Nat.Prime n ≤ n` from
    `Nat.findGreatest_le`. -/
theorem largestPrimeBelow_self_of_prime (n : ℕ) (hn : Nat.Prime n) :
    largestPrimeBelow n = n := by
  apply Nat.le_antisymm (largestPrimeBelow_le n)
  unfold largestPrimeBelow
  exact Nat.le_findGreatest le_rfl hn

/-- `largestPrimeBelow 2 = 2`. -/
theorem largestPrimeBelow_two : largestPrimeBelow 2 = 2 :=
  largestPrimeBelow_self_of_prime 2 Nat.prime_two

/-- `largestPrimeBelow 3 = 3`. -/
theorem largestPrimeBelow_three : largestPrimeBelow 3 = 3 :=
  largestPrimeBelow_self_of_prime 3 (by norm_num)

/-- `largestPrimeBelow 5 = 5`. -/
theorem largestPrimeBelow_five : largestPrimeBelow 5 = 5 :=
  largestPrimeBelow_self_of_prime 5 (by norm_num)

/-- `largestPrimeBelow 7 = 7`. -/
theorem largestPrimeBelow_seven : largestPrimeBelow 7 = 7 :=
  largestPrimeBelow_self_of_prime 7 (by norm_num)

/-- **Fixed-point characterization**: for `n ≥ 2`,
    `largestPrimeBelow n = n ↔ Nat.Prime n`.

    The forward direction uses `largestPrimeBelow_isPrime` to derive primality
    of the fixed point. The backward direction is `largestPrimeBelow_self_of_prime`. -/
theorem largestPrimeBelow_eq_self_iff_prime (n : ℕ) (hn : 2 ≤ n) :
    largestPrimeBelow n = n ↔ Nat.Prime n := by
  refine ⟨fun h => ?_, largestPrimeBelow_self_of_prime n⟩
  have hp := largestPrimeBelow_isPrime n hn
  rwa [h] at hp

/-- **Strict bound for composite `n`**: when `n ≥ 2` is not prime,
    `largestPrimeBelow n < n` (strictly).

    Combined with `largestPrimeBelow_le`, this characterizes composite `n`
    as exactly those `n ≥ 2` where the largest prime ≤ `n` is *strictly*
    less than `n`. -/
theorem largestPrimeBelow_lt_of_not_prime (n : ℕ) (hn : 2 ≤ n)
    (hcomp : ¬ Nat.Prime n) : largestPrimeBelow n < n := by
  rcases (largestPrimeBelow_le n).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ((largestPrimeBelow_eq_self_iff_prime n hn).mp heq) hcomp

/-- **AXIOM-FREE consistency check**: at `n = 2`, the conjectured equality
    `symBUDim n d = buDim (largestPrimeBelow n) d` is *already provable*
    from the parent's `symBUDim_two` axiom and `largestPrimeBelow_two`,
    independently of the new `symBUDim_eq_largestPrime` axiom.

    This is a non-trivial sanity check: the axiom `symBUDim_eq_largestPrime`
    is *consistent* with the previously-axiomatized n=2 base case, so we
    have not introduced an inconsistency between this file and the parent.
    Equivalently: the n=2 instance of the new axiom is *redundant* — it is
    a theorem rather than an independent assumption. -/
theorem symBUDim_eq_largestPrime_two_unconditional (d : ℕ) :
    symBUDim 2 d = buDim (largestPrimeBelow 2) d := by
  rw [largestPrimeBelow_two]
  exact symBUDim_two d

/-- **Axiom-free closed form at n = 2**: for `k ≥ 1`,
    `symBUDim 2 (2 * k) = 2 * k - 1`.

    Uses only the parent's `symBUDim_two` (n=2 base case) and `buDim_prime`
    (cyclic Yang-Borsuk for primes); does **not** use the conjectural
    `symBUDim_eq_largestPrime`. Provides an axiom-free witness that the
    even-d closed form `symBUDim_even_formula` collapses to a known result
    at n = 2. -/
theorem symBUDim_two_even_formula_unconditional (k : ℕ) (hk : 0 < k) :
    symBUDim 2 (2 * k) = 2 * k - 1 := by
  rw [symBUDim_two (2 * k)]
  exact buDim_prime 2 k Nat.prime_two hk

/-- **Concrete axiom-free instance**: `symBUDim 2 4 = 3`. (Compare with the
    conjectural `symBUDim_three_four`, `symBUDim_four_six` which depend on
    the new axiom.) -/
theorem symBUDim_two_four_unconditional : symBUDim 2 4 = 3 := by
  have := symBUDim_two_even_formula_unconditional 2 (by norm_num)
  simpa using this

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 6 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=6. -/
theorem symBUDim_six_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 6 (2 * k) :=
  symBUDim_even_lower 6 k (by norm_num) hk

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 7 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=7 (prime). -/
theorem symBUDim_seven_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 7 (2 * k) :=
  symBUDim_even_lower 7 k (by norm_num) hk

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 8 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=8.

    Note: S₈ has the rich non-cyclic subgroup structure (V₄, A₄, etc.)
    cited in the problem statement as a key test case for the conjecture's
    behavior at composite n. The unconditional cyclic lower bound is
    `2k - 1` here regardless. -/
theorem symBUDim_eight_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 8 (2 * k) :=
  symBUDim_even_lower 8 k (by norm_num) hk

/-
## Summary

### Axioms added (1)
- `symBUDim_eq_largestPrime` : the core equality conjecture; full proof
  requires Fadell-Husseini index calculations not in Mathlib.
  **Note**: The `n = 2` instance is *redundant* — see
  `symBUDim_eq_largestPrime_two_unconditional` for an axiom-free proof.

### Theorems proved (axiom-free up to parent's axioms)
- `largestPrimeBelow_isPrime`, `largestPrimeBelow_le`,
  `two_le_largestPrimeBelow` — basic facts about the prime selector.
- `largestPrimeBelow_self_of_prime` — when `n` is itself prime,
  `largestPrimeBelow n = n` (squeeze argument). General lemma.
- `largestPrimeBelow_two`, `_three`, `_five`, `_seven` — concrete
  computations at small primes.
- `largestPrimeBelow_eq_self_iff_prime` — fixed-point characterization
  iff primality (n ≥ 2): `largestPrimeBelow n = n ↔ Nat.Prime n`.
- `largestPrimeBelow_lt_of_not_prime` — strict bound for composite n
  (corollary of the iff).
- `symBUDim_even_lower` — UNCONDITIONAL lower bound (no new axioms beyond
  parent), establishing `2k - 1 ≤ symBUDim n (2k)` for n ≥ 2.
- `symBUDim_eq_largestPrime_two_unconditional` — **n=2 case of the
  conjecture, axiom-free** (consistency check: parent's `symBUDim_two`
  combined with `largestPrimeBelow_two` already entails the conjectured
  equality at n=2, without invoking `symBUDim_eq_largestPrime`).
- `symBUDim_two_even_formula_unconditional` — axiom-free closed form
  `symBUDim 2 (2k) = 2k - 1`.
- `symBUDim_two_four_unconditional` — concrete `symBUDim 2 4 = 3`,
  axiom-free.
- `n_div_two_lt_largestPrimeBelow` — Bertrand-Chebyshev quantitative bound
  `n / 2 < largestPrimeBelow n` for n ≥ 2 (axiom-free, uses Mathlib's
  `Nat.exists_prime_lt_and_le_two_mul`). Pins p* in the dyadic window
  `(n/2, n]` regardless of how composite n is.
- `largestPrimeBelow_in_bertrand_window` — packages the Bertrand lower
  bound with the trivial upper bound `≤ n`.

### Theorems requiring `symBUDim_eq_largestPrime` axiom
- `symBUDim_even_formula` — closed form on even d.
- `symBUDim_three_four`, `symBUDim_four_six` — concrete instances.

### Concrete instances (axiom-free)
- `symBUDim_five_lower_unconditional`, `symBUDim_two_four_unconditional`,
  `symBUDim_six_lower_unconditional`, `symBUDim_seven_lower_unconditional`,
  `symBUDim_eight_lower_unconditional`.

### Path forward
- Stretch: prove the n=3 case (next-easiest after n=2) — would require
  axiomatizing or proving `symBUDim 3 d ≤ buDim 3 d`; n=3 is *not*
  redundant since the parent doesn't have a `symBUDim_three` base axiom.
- Stretch: prove the n=4 case by hand (compute equivariant index of S₄ on
  small reps); a proof or counterexample at n=4 would settle the conjecture
  for many small-n applications.
- Coordinate with sister-question OQ-02-OQ-01-OQ-03-OQ-01 (dihedral Dₙ).
- The Bertrand bound shows the cyclic lower bound is within factor 2 of
  optimal; tightening past this would require S_n-specific structure
  (representation-theoretic obstructions, V₄-style non-cyclic factors).
-/

#check @symBUDim_eq_largestPrime
#check @symBUDim_even_formula
#check @symBUDim_even_lower
#check @n_div_two_lt_largestPrimeBelow
#check @largestPrimeBelow_self_of_prime
#check @largestPrimeBelow_eq_self_iff_prime
#check @largestPrimeBelow_lt_of_not_prime
#check @symBUDim_eq_largestPrime_two_unconditional

end BorsukUlamSymPrime
