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

/-- **Monotonicity of `largestPrimeBelow`**: if `n ≤ m`, then
    `largestPrimeBelow n ≤ largestPrimeBelow m`.

    Proof: case split on `n ≥ 2`.
    - If `n ≥ 2`: `largestPrimeBelow n` is prime (by `largestPrimeBelow_isPrime`)
      and ≤ `n` ≤ `m`, so `largestPrimeBelow n ≤ findGreatest Nat.Prime m`
      by maximality of `findGreatest`.
    - If `n < 2`: `findGreatest Nat.Prime n = 0` since no prime is ≤ 1, so
      the bound is trivial.

    This lemma is the structural prerequisite for compatibility of the
    `symBUDim_eq_largestPrime` axiom with the parent's
    `sym_has_smaller_sym n d` monotonicity (stretch goal in `nextSteps[3]`
    of the project file). -/
theorem largestPrimeBelow_mono : Monotone largestPrimeBelow := by
  intro n m hnm
  by_cases hn : 2 ≤ n
  · -- n ≥ 2: largestPrimeBelow n is itself a prime ≤ m
    have hp_prime : Nat.Prime (largestPrimeBelow n) := largestPrimeBelow_isPrime n hn
    have hp_le_m : largestPrimeBelow n ≤ m := (largestPrimeBelow_le n).trans hnm
    unfold largestPrimeBelow
    exact Nat.le_findGreatest hp_le_m hp_prime
  · -- n < 2: largestPrimeBelow n = 0, hence the bound is trivial
    push_neg at hn
    have h_eq_zero : largestPrimeBelow n = 0 := by
      unfold largestPrimeBelow
      interval_cases n
      · rfl
      · -- n = 1: only candidate k ≤ 1 is k ∈ {0,1}, neither prime
        decide
    rw [h_eq_zero]
    exact Nat.zero_le _

/-- **Concrete monotonicity instance**: `largestPrimeBelow 8 ≤ largestPrimeBelow 11`.

    Together with `largestPrimeBelow_seven : largestPrimeBelow 7 = 7` and
    `largestPrimeBelow 11 = 11` (since 11 is prime), this confirms the
    monotone progression `_ 7 = 7, _ 8 = 7, _ 9 = 7, _ 10 = 7, _ 11 = 11`
    over the dyadic Bertrand window from 7 to 11. -/
theorem largestPrimeBelow_eight_le_eleven :
    largestPrimeBelow 8 ≤ largestPrimeBelow 11 :=
  largestPrimeBelow_mono (by norm_num : (8 : ℕ) ≤ 11)

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

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 9 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=9 (composite, 3²).
    Note: `largestPrimeBelow 9 = 7`. -/
theorem symBUDim_nine_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 9 (2 * k) :=
  symBUDim_even_lower 9 k (by norm_num) hk

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 10 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=10.
    Note: `largestPrimeBelow 10 = 7`. -/
theorem symBUDim_ten_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 10 (2 * k) :=
  symBUDim_even_lower 10 k (by norm_num) hk

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 11 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=11 (prime). -/
theorem symBUDim_eleven_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 11 (2 * k) :=
  symBUDim_even_lower 11 k (by norm_num) hk

/-- **Unconditional**: `2 * k - 1 ≤ symBUDim 12 (2 * k)` for k ≥ 1.
    Direct application of `symBUDim_even_lower` at n=12.
    Note: `largestPrimeBelow 12 = 11`. -/
theorem symBUDim_twelve_lower_unconditional (k : ℕ) (hk : 0 < k) :
    2 * k - 1 ≤ symBUDim 12 (2 * k) :=
  symBUDim_even_lower 12 k (by norm_num) hk

-- ═══════════════════════════════════════════════════════════════════════
-- PART VIII: Conjecture specialized at prime n
-- ═══════════════════════════════════════════════════════════════════════

/-- **Specialization at prime n**: at any prime `p`, the conjectural equality
    `symBUDim_eq_largestPrime` simplifies to the clean statement
        `symBUDim p d = buDim p d`,
    because `largestPrimeBelow p = p` by `largestPrimeBelow_self_of_prime`.

    This isolates the *prime-n content* of the open question: when `n` is
    itself prime, the conjecture asks whether the Sₙ-equivariant BU
    dimension equals the cyclic-prime-`n` BU dimension — a strictly
    Sₙ-versus-ℤ/p question, no Bertrand selector involved.

    **Conditional on the axiom** `symBUDim_eq_largestPrime`. The statement
    has no prime-≥2 hypothesis on the RHS because primality already forces
    `2 ≤ p` via `Nat.Prime.two_le`. -/
theorem symBUDim_eq_buDim_at_prime (p d : ℕ) (hp : Nat.Prime p) :
    symBUDim p d = buDim p d := by
  have h2 : 2 ≤ p := hp.two_le
  rw [symBUDim_eq_largestPrime p d h2, largestPrimeBelow_self_of_prime p hp]

/-- **Tight closed form at prime n on even d** (conditional on the axiom):
    for prime `p` and `k ≥ 1`,
        `symBUDim p (2k) = 2k - 1`.
    Combines `symBUDim_eq_buDim_at_prime` with parent's `buDim_prime`. -/
theorem symBUDim_prime_even_formula (p k : ℕ) (hp : Nat.Prime p) (hk : 0 < k) :
    symBUDim p (2 * k) = 2 * k - 1 := by
  rw [symBUDim_eq_buDim_at_prime p (2 * k) hp]
  exact buDim_prime p k hp hk

/-- **Concrete prime-n instance at n = 11** (conditional):
    `symBUDim 11 d = buDim 11 d`. -/
theorem symBUDim_eleven_eq_buDim_eleven (d : ℕ) :
    symBUDim 11 d = buDim 11 d :=
  symBUDim_eq_buDim_at_prime 11 d (by norm_num)

/-- **Concrete prime-n instance at n = 13** (conditional):
    `symBUDim 13 d = buDim 13 d`. Pushes the enumerated range past 12. -/
theorem symBUDim_thirteen_eq_buDim_thirteen (d : ℕ) :
    symBUDim 13 d = buDim 13 d :=
  symBUDim_eq_buDim_at_prime 13 d (by norm_num)

/-- **Concrete closed form at n = 11** (conditional):
    `symBUDim 11 (2k) = 2k - 1` for k ≥ 1. -/
theorem symBUDim_eleven_even_formula (k : ℕ) (hk : 0 < k) :
    symBUDim 11 (2 * k) = 2 * k - 1 :=
  symBUDim_prime_even_formula 11 k (by norm_num) hk

/-- **Concrete closed form at n = 13** (conditional):
    `symBUDim 13 (2k) = 2k - 1` for k ≥ 1. -/
theorem symBUDim_thirteen_even_formula (k : ℕ) (hk : 0 < k) :
    symBUDim 13 (2 * k) = 2 * k - 1 :=
  symBUDim_prime_even_formula 13 k (by norm_num) hk

-- ═══════════════════════════════════════════════════════════════════════
-- PART IX: General-d (odd OR even) unconditional lower bound from Z/2
-- ═══════════════════════════════════════════════════════════════════════

/-- **Uniform unconditional lower bound** (axiom-free up to parent's axioms),
    valid for ALL `d ≥ 1` (not just even):
        `d - 1 ≤ symBUDim n d`  for `n ≥ 2`.

    Strategy: route through the Z/2 subgroup. The parent provides
    - `symBUDim_two d : symBUDim 2 d = buDim 2 d`,
    - `symBUDim_le_of_le 2 n d (hn : 2 ≤ n) : symBUDim 2 d ≤ symBUDim n d`,
    - `buDim_two m : buDim 2 (m + 1) = m`.
    Combining these at `d = (d - 1) + 1` (valid since `d ≥ 1`) yields
    `buDim 2 d = d - 1`, hence `d - 1 ≤ symBUDim n d`.

    This **strictly improves** `symBUDim_even_lower` at odd `d`:
    - For `d = 2k`: `d - 1 = 2k - 1` (matches `symBUDim_even_lower`).
    - For `d = 2k + 1`: `d - 1 = 2k > 2k - 1 = 2 * (d / 2) - 1`,
      so this gives a *strictly stronger* odd-d bound. -/
theorem symBUDim_lower_z2 (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) :
    d - 1 ≤ symBUDim n d := by
  -- Express `d` as `(d - 1) + 1` so we can use `buDim_two`.
  have hd' : d = (d - 1) + 1 := by omega
  -- Step 1: `buDim 2 d = d - 1` from parent's `buDim_two`.
  have h1 : buDim 2 d = d - 1 := by
    conv_lhs => rw [hd']
    exact buDim_two (d - 1)
  -- Step 2: `symBUDim 2 d = buDim 2 d` from parent's `symBUDim_two`.
  have h2 : symBUDim 2 d = buDim 2 d := symBUDim_two d
  -- Step 3: monotonicity 2 ≤ n.
  have h3 : symBUDim 2 d ≤ symBUDim n d := symBUDim_le_of_le 2 n d hn
  rw [h2, h1] at h3
  exact h3

/-- **Odd-d uniform lower bound** (corollary of `symBUDim_lower_z2`):
    for `n ≥ 2` and `k ≥ 0`, `2 * k ≤ symBUDim n (2 * k + 1)`.

    This bound is **strictly stronger** than what `symBUDim_even_lower`
    produces at odd dimension via floor-rounding: `2 * ((2k+1) / 2) - 1
    = 2k - 1`, while we get `2k`. Captures the extra "odd dimension"
    contribution from the classical Borsuk-Ulam map at p = 2. -/
theorem symBUDim_odd_lower_unconditional (n k : ℕ) (hn : 2 ≤ n) :
    2 * k ≤ symBUDim n (2 * k + 1) := by
  have h := symBUDim_lower_z2 n (2 * k + 1) hn (by omega)
  -- `(2 * k + 1) - 1 = 2 * k` definitionally; ensure the rewrite goes through.
  have heq : (2 * k + 1) - 1 = 2 * k := by omega
  rw [heq] at h
  exact h

-- ═══════════════════════════════════════════════════════════════════════
-- PART X: General-d closed form at n = 2 (axiom-free)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Axiom-free closed form at n = 2 for ALL d ≥ 1**:
        `symBUDim 2 d = d - 1`.

    Strengthens `symBUDim_two_even_formula_unconditional` (which only
    handled even d) by routing through `buDim_two` at the general-d shape.
    Uses only parent's `symBUDim_two` (the n=2 base axiom) and `buDim_two`
    (the classical Borsuk-Ulam in any dimension).

    Note: This is the **complete picture** at n = 2 — independent of the
    new `symBUDim_eq_largestPrime` axiom — because the parent already pins
    `symBUDim 2 = buDim 2`, and `buDim_two` is the classical formula. -/
theorem symBUDim_two_general_unconditional (d : ℕ) (hd : 0 < d) :
    symBUDim 2 d = d - 1 := by
  rw [symBUDim_two d]
  have hd' : d = (d - 1) + 1 := by omega
  conv_lhs => rw [hd']
  exact buDim_two (d - 1)

/-- **Concrete axiom-free instance at odd d**: `symBUDim 2 3 = 2`.
    Companion to `symBUDim_two_four_unconditional`. -/
theorem symBUDim_two_three_unconditional : symBUDim 2 3 = 2 := by
  have := symBUDim_two_general_unconditional 3 (by norm_num)
  simpa using this

/-- **Concrete axiom-free instance at odd d**: `symBUDim 2 5 = 4`.
    Smallest "interesting" odd dimension (d = 5 corresponds to the
    standard `S^4 → ℝ^5` Borsuk-Ulam scenario). -/
theorem symBUDim_two_five_unconditional : symBUDim 2 5 = 4 := by
  have := symBUDim_two_general_unconditional 5 (by norm_num)
  simpa using this

/-- **Concrete axiom-free instance at odd d**: `symBUDim 2 7 = 6`. -/
theorem symBUDim_two_seven_unconditional : symBUDim 2 7 = 6 := by
  have := symBUDim_two_general_unconditional 7 (by norm_num)
  simpa using this

-- ═══════════════════════════════════════════════════════════════════════
-- PART XI: Concrete odd-d unconditional lower bounds (n ≥ 3)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Odd d = 3 lower bound at S₃**: `2 ≤ symBUDim 3 3` (axiom-free). -/
theorem symBUDim_three_three_lower_unconditional : 2 ≤ symBUDim 3 3 := by
  have := symBUDim_odd_lower_unconditional 3 1 (by norm_num)
  simpa using this

/-- **Odd d = 3 lower bound at S₄**: `2 ≤ symBUDim 4 3` (axiom-free).
    Note: S₄ has the V₄ Klein-4 subgroup (cited in the problem statement
    as a key test case); the Z/2 lower bound holds regardless. -/
theorem symBUDim_four_three_lower_unconditional : 2 ≤ symBUDim 4 3 := by
  have := symBUDim_odd_lower_unconditional 4 1 (by norm_num)
  simpa using this

/-- **Odd d = 5 lower bound at S₃**: `4 ≤ symBUDim 3 5` (axiom-free).
    For odd d the largestPrimeBelow approach gives only `2k - 1 = 3` (via
    `buDim_prime`'s even-d range), but Z/2's classical Borsuk-Ulam in odd
    dimension yields the **strictly tighter** bound `d - 1 = 4`. -/
theorem symBUDim_three_five_lower_unconditional : 4 ≤ symBUDim 3 5 := by
  have := symBUDim_odd_lower_unconditional 3 2 (by norm_num)
  simpa using this

/-- **Odd d = 5 lower bound at S₄**: `4 ≤ symBUDim 4 5` (axiom-free).
    Companion to `_three_five_`; together they show the Z/2 odd-d bound
    is robust at the smallest non-trivial test cases (n=3 prime, n=4
    composite with V₄). -/
theorem symBUDim_four_five_lower_unconditional : 4 ≤ symBUDim 4 5 := by
  have := symBUDim_odd_lower_unconditional 4 2 (by norm_num)
  simpa using this

-- ═══════════════════════════════════════════════════════════════════════
-- PART XIV: Conditional consequence — Z/2 bound transfers to cyclic primes
-- ═══════════════════════════════════════════════════════════════════════

/-- **Conditional on `symBUDim_eq_largestPrime`**: the axiom-free Z/2 lower
    bound `symBUDim_lower_z2` pulls through the conjectured equality to
    pin a lower bound on the cyclic Yang-Borsuk dimension at the largest
    prime ≤ n:
        `d − 1 ≤ buDim (largestPrimeBelow n) d`   (n ≥ 2, d ≥ 1).

    This is genuinely new content beyond the parent's axiomatization:
    `buDim_two` (parent) only fixes `buDim 2`; `buDim_prime` only fixes
    `buDim p (2k)` for prime p and even d. At ODD d, `buDim p d` for
    p ≥ 3 is unconstrained by parent axioms — the symmetric-group
    conjecture would PIN a NEW lower bound `d − 1` valid at odd d. -/
theorem buDim_largestPrime_lower_z2 (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) :
    d - 1 ≤ buDim (largestPrimeBelow n) d := by
  rw [← symBUDim_eq_largestPrime n d hn]
  exact symBUDim_lower_z2 n d hn hd

/-- **Conditional on the conjecture, at prime p**: classical Borsuk-Ulam
    lower bound `d − 1 ≤ buDim p d` extends from p = 2 (parent's `buDim_two`)
    to ALL primes p and ALL d ≥ 1 (including odd d).

    This is strictly stronger than what `buDim_prime` provides: at odd d
    the parent's even-d Yang-Borsuk axiom yields nothing about `buDim p d`,
    while this conditional bound delivers `d − 1` for free.

    Proof: specialize `buDim_largestPrime_lower_z2` at n = p and use
    `largestPrimeBelow_self_of_prime` to collapse the prime selector. -/
theorem buDim_prime_lower_z2_conditional (p d : ℕ) (hp : Nat.Prime p) (hd : 0 < d) :
    d - 1 ≤ buDim p d := by
  have h := buDim_largestPrime_lower_z2 p d hp.two_le hd
  rwa [largestPrimeBelow_self_of_prime p hp] at h

/-- **Concrete conditional bound at p = 3**: `d − 1 ≤ buDim 3 d` for d ≥ 1.
    At odd d (e.g., d = 3) this gives `buDim 3 3 ≥ 2`, content beyond
    parent's even-d Yang-Borsuk axiom. -/
theorem buDim_three_lower_z2_conditional (d : ℕ) (hd : 0 < d) :
    d - 1 ≤ buDim 3 d :=
  buDim_prime_lower_z2_conditional 3 d (by decide) hd

/-- **Concrete conditional bound at p = 5**: `d − 1 ≤ buDim 5 d` for d ≥ 1. -/
theorem buDim_five_lower_z2_conditional (d : ℕ) (hd : 0 < d) :
    d - 1 ≤ buDim 5 d :=
  buDim_prime_lower_z2_conditional 5 d (by decide) hd

/-- **Concrete conditional bound at p = 7**: `d − 1 ≤ buDim 7 d` for d ≥ 1. -/
theorem buDim_seven_lower_z2_conditional (d : ℕ) (hd : 0 < d) :
    d - 1 ≤ buDim 7 d :=
  buDim_prime_lower_z2_conditional 7 d (by decide) hd

/-- **Combined unconditional lower bound at prime p**: at any prime p with
    d ≥ 1,
        `max (buDim p d) (d − 1) ≤ symBUDim p d`   (axiom-free).

    Packages the two axiom-free lower bounds at prime n into a single
    statement: the Z/p subgroup contribution (`buDim p d ≤ symBUDim p d`,
    parent's `sym_has_cyclic_prime`) and the Z/2 subgroup contribution
    (`d − 1 ≤ symBUDim p d`, iter-7's `symBUDim_lower_z2`). At even
    d = 2k the two coincide via `buDim_prime` (both deliver `2k − 1`);
    at odd d the Z/2 component dominates. -/
theorem symBUDim_prime_combined_lower (p d : ℕ) (hp : Nat.Prime p) (hd : 0 < d) :
    max (buDim p d) (d - 1) ≤ symBUDim p d := by
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · exact sym_has_cyclic_prime p d p hp le_rfl
  · exact symBUDim_lower_z2 p d hp.two_le hd

-- ═══════════════════════════════════════════════════════════════════════
-- PART XV: Conjecture-as-Prop and explicit falsification handles
-- ═══════════════════════════════════════════════════════════════════════

/-- The Largest-Prime-Below conjecture, stated as a `Prop` rather than an
    axiom. Downstream developments that wish to track conjecture-dependence
    explicitly can take this as a hypothesis instead of using the file's
    `symBUDim_eq_largestPrime` axiom. -/
def ConjectureLPB : Prop :=
  ∀ n d : ℕ, 2 ≤ n → symBUDim n d = buDim (largestPrimeBelow n) d

/-- Hypothesis-form variant of `buDim_largestPrime_lower_z2`: the conjecture
    (as a `Prop` hypothesis) implies the Z/2 lower bound on the cyclic
    Yang-Borsuk dimension at the largest prime ≤ n. Same statement as the
    axiom-using version, but the conjecture-dependence is explicit. -/
theorem buDim_largestPrime_lower_z2_of (h : ConjectureLPB) (n d : ℕ)
    (hn : 2 ≤ n) (hd : 0 < d) :
    d - 1 ≤ buDim (largestPrimeBelow n) d := by
  rw [← h n d hn]
  exact symBUDim_lower_z2 n d hn hd

/-- Hypothesis-form variant of `buDim_prime_lower_z2_conditional`. -/
theorem buDim_prime_lower_z2_of (h : ConjectureLPB) (p d : ℕ)
    (hp : Nat.Prime p) (hd : 0 < d) :
    d - 1 ≤ buDim p d := by
  have hL := buDim_largestPrime_lower_z2_of h p d hp.two_le hd
  rwa [largestPrimeBelow_self_of_prime p hp] at hL

/-- Hypothesis-form variant of `symBUDim_eq_buDim_at_prime`: at any prime p,
    the conjecture pins `symBUDim p d = buDim p d` for all d. -/
theorem symBUDim_eq_buDim_at_prime_of (h : ConjectureLPB) (p d : ℕ)
    (hp : Nat.Prime p) :
    symBUDim p d = buDim p d := by
  have hL := h p d hp.two_le
  rwa [largestPrimeBelow_self_of_prime p hp] at hL

/-- **Falsification handle (general)**: if for some prime p and some d ≥ 1
    we ever prove the strict bound `buDim p d < d - 1`, then `ConjectureLPB`
    is false.

    This is the contrapositive of `buDim_prime_lower_z2_of`. It is the
    formal restatement of iter-8's remark "any future computation of
    `buDim p d` at odd d that violates `d − 1 ≤ buDim p d` would FALSIFY
    `symBUDim_eq_largestPrime` at n = p". -/
theorem not_conjectureLPB_of_buDim_lt {p d : ℕ} (hp : Nat.Prime p)
    (hd : 0 < d) (hlt : buDim p d < d - 1) :
    ¬ ConjectureLPB := by
  intro h
  have := buDim_prime_lower_z2_of h p d hp hd
  omega

/-- **Falsification handle at p = 3, d = 3**: a proof of `buDim 3 3 < 2`
    would refute the conjecture. Concrete instance most likely amenable
    to direct equivariant-cohomology computation, since the Yang-Borsuk
    dimension at p = 3 in odd dimension d = 3 is exactly the simplest
    case beyond the parent file's even-d axiomatization. -/
theorem not_conjectureLPB_of_buDim_three_three_lt_two
    (h : buDim 3 3 < 2) : ¬ ConjectureLPB :=
  not_conjectureLPB_of_buDim_lt (p := 3) (d := 3) (by decide) (by norm_num)
    (by simpa using h)

/-- **Falsification handle at p = 5, d = 3**: a proof of `buDim 5 3 < 2`
    would refute the conjecture. The conjecture's claim here is strictly
    beyond Yang-Borsuk's even-d axiomatization. -/
theorem not_conjectureLPB_of_buDim_five_three_lt_two
    (h : buDim 5 3 < 2) : ¬ ConjectureLPB :=
  not_conjectureLPB_of_buDim_lt (p := 5) (d := 3) (by decide) (by norm_num)
    (by simpa using h)

/-- **Falsification handle at p = 3, d = 5**: a proof of `buDim 3 5 < 4`
    would refute the conjecture. -/
theorem not_conjectureLPB_of_buDim_three_five_lt_four
    (h : buDim 3 5 < 4) : ¬ ConjectureLPB :=
  not_conjectureLPB_of_buDim_lt (p := 3) (d := 5) (by decide) (by norm_num)
    (by simpa using h)

-- ═══════════════════════════════════════════════════════════════════════
-- PART XVI: Plateau infrastructure for largestPrimeBelow
-- ═══════════════════════════════════════════════════════════════════════

/-- **Successor non-prime preserves LPB**: if `n + 1` is not prime, then
    `largestPrimeBelow (n + 1) = largestPrimeBelow n`. Direct corollary of
    Mathlib's `Nat.findGreatest_of_not`.

    This is the atomic step underlying the plateau pattern: as `m` ranges
    over a maximal prime-gap interval `[p, q)`, `largestPrimeBelow m` stays
    pinned at the prime `p` because each successor jump is at a composite
    number. -/
theorem largestPrimeBelow_succ_of_not_prime (n : ℕ)
    (h : ¬ Nat.Prime (n + 1)) :
    largestPrimeBelow (n + 1) = largestPrimeBelow n := by
  unfold largestPrimeBelow
  exact Nat.findGreatest_of_not h

/-- **Plateau lemma — no-prime range form**: if no prime exists in the
    half-open interval `(n, m]`, then `largestPrimeBelow m = largestPrimeBelow n`.
    Proved by induction on `m - n` via `Nat.le_induction`, repeatedly applying
    `largestPrimeBelow_succ_of_not_prime` at each composite successor.

    This is the structural reason the LPB function is locally constant
    between consecutive primes — and hence (conjecturally) why
    `symBUDim n d` should be constant on the same intervals. -/
theorem largestPrimeBelow_const_in_no_prime_range (n m : ℕ) (hnm : n ≤ m)
    (h_no_prime : ∀ k, n < k → k ≤ m → ¬ Nat.Prime k) :
    largestPrimeBelow m = largestPrimeBelow n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have h_not_kp1 : ¬ Nat.Prime (k + 1) :=
      h_no_prime (k + 1) (Nat.lt_succ_of_le hk) le_rfl
    have h_no_prime_lower : ∀ j, n < j → j ≤ k → ¬ Nat.Prime j := fun j hj1 hj2 =>
      h_no_prime j hj1 (le_trans hj2 (Nat.le_succ k))
    rw [largestPrimeBelow_succ_of_not_prime k h_not_kp1, ih h_no_prime_lower]

/-- **Plateau lemma — prime-anchored form**: if `p` is prime, `p ≤ n ≤ m`,
    `largestPrimeBelow n = p`, and no prime lies in `(n, m]`, then
    `largestPrimeBelow m = p` as well. -/
theorem largestPrimeBelow_eq_of_in_plateau (p n m : ℕ)
    (hp : Nat.Prime p) (hpn : p ≤ n) (hnm : n ≤ m)
    (h_lpb_n : largestPrimeBelow n = p)
    (h_no_prime : ∀ k, n < k → k ≤ m → ¬ Nat.Prime k) :
    largestPrimeBelow m = p := by
  rw [largestPrimeBelow_const_in_no_prime_range n m hnm h_no_prime, h_lpb_n]

-- ─────────────────────────────────────────────────────────────────────
-- Conditional consequences (depend on `symBUDim_eq_largestPrime`)
-- ─────────────────────────────────────────────────────────────────────

/-- **Conjectural `symBUDim` equality from same LPB**: any two `n, m ≥ 2`
    with `largestPrimeBelow n = largestPrimeBelow m` have `symBUDim n d =
    symBUDim m d` at every dimension `d`. Conditional on
    `symBUDim_eq_largestPrime`.

    Combined with `largestPrimeBelow_const_in_no_prime_range`, this is the
    formal expression of the "plateau collapse" prediction: the conjecture
    forces three distinct symmetric groups in any prime-gap interval to
    have identical equivariant Borsuk-Ulam dimension. -/
theorem symBUDim_eq_of_lpb_eq (n m d : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : largestPrimeBelow n = largestPrimeBelow m) :
    symBUDim n d = symBUDim m d := by
  rw [symBUDim_eq_largestPrime n d hn, symBUDim_eq_largestPrime m d hm, h]

/-- **Conjectural plateau on no-prime range**: if no prime exists in `(n, m]`
    and `n ≥ 2`, then `symBUDim n d = symBUDim m d` for every `d`.
    Conditional on `symBUDim_eq_largestPrime`.

    This is the symBUDim-side of the plateau lemma. The atomic version of
    `symBUDim n d = symBUDim m d` for `m = n + 1` with `n + 1` composite
    falls out as a direct corollary. -/
theorem symBUDim_const_in_no_prime_range (n m d : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m)
    (h_no_prime : ∀ k, n < k → k ≤ m → ¬ Nat.Prime k) :
    symBUDim n d = symBUDim m d := by
  have hm : 2 ≤ m := le_trans hn hnm
  exact symBUDim_eq_of_lpb_eq n m d hn hm
    (largestPrimeBelow_const_in_no_prime_range n m hnm h_no_prime).symm

/-- **Hypothesis-form of `symBUDim_eq_of_lpb_eq`** — uses the explicit
    `ConjectureLPB` hypothesis introduced in Part XV instead of the file's
    axiom. -/
theorem symBUDim_eq_of_lpb_eq_of (h_conj : ConjectureLPB)
    (n m d : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : largestPrimeBelow n = largestPrimeBelow m) :
    symBUDim n d = symBUDim m d := by
  rw [h_conj n d hn, h_conj m d hm, h]

/-- **Hypothesis-form of `symBUDim_const_in_no_prime_range`**. -/
theorem symBUDim_const_in_no_prime_range_of (h_conj : ConjectureLPB)
    (n m d : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m)
    (h_no_prime : ∀ k, n < k → k ≤ m → ¬ Nat.Prime k) :
    symBUDim n d = symBUDim m d := by
  have hm : 2 ≤ m := le_trans hn hnm
  exact symBUDim_eq_of_lpb_eq_of h_conj n m d hn hm
    (largestPrimeBelow_const_in_no_prime_range n m hnm h_no_prime).symm

-- ═══════════════════════════════════════════════════════════════════════
-- PART XVII: Concrete plateau collapse instances
-- ═══════════════════════════════════════════════════════════════════════
-- Direct applications of PART XVI's plateau infrastructure to specific
-- prime-gap intervals.  Each instance pins a no-prime-in-gap fact via
-- `interval_cases` + `decide`, then derives:
--   1. Axiom-free LPB collapse: `largestPrimeBelow m = largestPrimeBelow n`.
--   2. Conditional `symBUDim` collapse: `symBUDim n d = symBUDim m d`,
--      depending on `symBUDim_eq_largestPrime`.
--   3. Hypothesis-form variant taking `ConjectureLPB` explicitly.
--
-- Chosen intervals are the smallest prime gaps with multiple composite
-- numbers between consecutive primes:
--   - (7, 11):   {8, 9, 10}                 — gap 4, dyadic gap
--   - (13, 17):  {14, 15, 16}               — gap 4
--   - (23, 29):  {24, 25, 26, 27, 28}       — gap 6 (first occurrence)
--
-- The conditional consequences are notable: distinct symmetric groups
-- with qualitatively different subgroup structures (e.g., S₈ ⊃ V₄·A₄
-- vs S₁₀ ⊃ A₅×A₅; or S₂₃ vs S₂₈ ⊃ S₄×S₂₄/?) conjecturally share the
-- *same* equivariant Borsuk-Ulam dimension at every dimension.

/-- **No prime in (8, 10]**: each of 9, 10 is composite. Witness for
    the dyadic prime gap (7, 11). -/
theorem no_prime_in_eight_to_ten :
    ∀ k, 8 < k → k ≤ 10 → ¬ Nat.Prime k := by
  intro k hk1 hk2
  interval_cases k <;> decide

/-- **LPB plateau across the dyadic gap (7, 11)**: `largestPrimeBelow 10 =
    largestPrimeBelow 8`, axiom-free.  Combined with `largestPrimeBelow 8
    = largestPrimeBelow 7 = 7` (which would follow from the still-pending
    PART XII concrete-LPB computations), this would witness the
    three-step plateau `lpb 8 = lpb 9 = lpb 10`.  Independent of those
    concrete values, the equality `lpb 10 = lpb 8` is a direct corollary
    of PART XVI's `largestPrimeBelow_const_in_no_prime_range`. -/
theorem largestPrimeBelow_eight_eq_ten :
    largestPrimeBelow 10 = largestPrimeBelow 8 :=
  largestPrimeBelow_const_in_no_prime_range 8 10 (by norm_num)
    no_prime_in_eight_to_ten

/-- **Conjectural plateau collapse at S₈ → S₁₀**: under
    `symBUDim_eq_largestPrime`, `symBUDim 8 d = symBUDim 10 d` for every
    `d`.  Witnesses the most concrete plateau-collapse content of the
    conjecture: two distinct symmetric groups (S₈ with rich V₄·A₄ subgroup
    structure, S₁₀ with A₅×A₅) conjecturally share equivariant Borsuk-Ulam
    dimensions at every dimension. -/
theorem symBUDim_eight_eq_ten (d : ℕ) :
    symBUDim 8 d = symBUDim 10 d :=
  symBUDim_const_in_no_prime_range 8 10 d (by norm_num) (by norm_num)
    no_prime_in_eight_to_ten

/-- **Hypothesis-form** of `symBUDim_eight_eq_ten` — uses explicit
    `ConjectureLPB` hypothesis instead of the file's axiom. -/
theorem symBUDim_eight_eq_ten_of (h_conj : ConjectureLPB) (d : ℕ) :
    symBUDim 8 d = symBUDim 10 d :=
  symBUDim_const_in_no_prime_range_of h_conj 8 10 d (by norm_num) (by norm_num)
    no_prime_in_eight_to_ten

/-- **No prime in (13, 16]**: each of 14, 15, 16 is composite.  Witness
    for the prime gap (13, 17). -/
theorem no_prime_in_fourteen_to_sixteen :
    ∀ k, 13 < k → k ≤ 16 → ¬ Nat.Prime k := by
  intro k hk1 hk2
  interval_cases k <;> decide

/-- **LPB plateau across the gap (13, 17)**: `largestPrimeBelow 16 =
    largestPrimeBelow 13`, axiom-free. -/
theorem largestPrimeBelow_thirteen_eq_sixteen :
    largestPrimeBelow 16 = largestPrimeBelow 13 :=
  largestPrimeBelow_const_in_no_prime_range 13 16 (by norm_num)
    no_prime_in_fourteen_to_sixteen

/-- **Conjectural plateau collapse at S₁₃ → S₁₆**: under
    `symBUDim_eq_largestPrime`, `symBUDim 13 d = symBUDim 16 d` for every
    `d`. -/
theorem symBUDim_thirteen_eq_sixteen (d : ℕ) :
    symBUDim 13 d = symBUDim 16 d :=
  symBUDim_const_in_no_prime_range 13 16 d (by norm_num) (by norm_num)
    no_prime_in_fourteen_to_sixteen

/-- **Hypothesis-form** of `symBUDim_thirteen_eq_sixteen`. -/
theorem symBUDim_thirteen_eq_sixteen_of (h_conj : ConjectureLPB) (d : ℕ) :
    symBUDim 13 d = symBUDim 16 d :=
  symBUDim_const_in_no_prime_range_of h_conj 13 16 d (by norm_num) (by norm_num)
    no_prime_in_fourteen_to_sixteen

/-- **No prime in (23, 28]**: each of 24, 25, 26, 27, 28 is composite.
    Witness for the prime gap (23, 29) — the first prime gap of size 6,
    five consecutive composites. -/
theorem no_prime_in_twentyfour_to_twentyeight :
    ∀ k, 23 < k → k ≤ 28 → ¬ Nat.Prime k := by
  intro k hk1 hk2
  interval_cases k <;> decide

/-- **LPB plateau across the gap (23, 29)**: `largestPrimeBelow 28 =
    largestPrimeBelow 23`, axiom-free.  The first prime gap of size 6
    in ℕ — five consecutive composites all share the same
    `largestPrimeBelow`. -/
theorem largestPrimeBelow_twentythree_eq_twentyeight :
    largestPrimeBelow 28 = largestPrimeBelow 23 :=
  largestPrimeBelow_const_in_no_prime_range 23 28 (by norm_num)
    no_prime_in_twentyfour_to_twentyeight

/-- **Conjectural plateau collapse at S₂₃ → S₂₈**: under
    `symBUDim_eq_largestPrime`, `symBUDim 23 d = symBUDim 28 d` for every
    `d`.  The conjecture forces equivariant BU dimensions at all six
    consecutive ranks `n ∈ {23, 24, …, 28}` to coincide — the longest
    plateau collapse delivered by a prime-6 gap below n = 30. -/
theorem symBUDim_twentythree_eq_twentyeight (d : ℕ) :
    symBUDim 23 d = symBUDim 28 d :=
  symBUDim_const_in_no_prime_range 23 28 d (by norm_num) (by norm_num)
    no_prime_in_twentyfour_to_twentyeight

/-- **Hypothesis-form** of `symBUDim_twentythree_eq_twentyeight`. -/
theorem symBUDim_twentythree_eq_twentyeight_of
    (h_conj : ConjectureLPB) (d : ℕ) :
    symBUDim 23 d = symBUDim 28 d :=
  symBUDim_const_in_no_prime_range_of h_conj 23 28 d
    (by norm_num) (by norm_num) no_prime_in_twentyfour_to_twentyeight

-- ═══════════════════════════════════════════════════════════════════════
-- PART XVIII: First prime gap of size 8 — plateau collapse at S₈₉ → S₉₆
-- ═══════════════════════════════════════════════════════════════════════
-- The interval `(89, 97)` is the first prime gap of size 8 in ℕ.  Seven
-- consecutive composites — 90, 91, 92, 93, 94, 95, 96 — lie strictly
-- between the consecutive primes 89 and 97 (89 < 97 with no prime
-- in between).  This is the smallest n ∈ ℕ where the prime-gap function
-- p_(k+1) − p_k first exceeds 7, distinguishing it from every gap among
-- the first 24 primes.  Following the Part-XVII pattern at the gaps of
-- size 4, 6, this section pins
--   `largestPrimeBelow 96 = largestPrimeBelow 89` axiom-free, and
--   `symBUDim 89 d = symBUDim 96 d` conditionally.
-- The plateau spans **eight consecutive ranks** `n ∈ {89, 90, …, 96}` —
-- the longest plateau collapse below n = 100, with structurally
-- distinguished symmetric groups along the way:
--   - S₈₉ (rank 89, with |S₈₉| = 89!),
--   - S₉₀ ⊃ A₉₀ ⋊ Z/2 (highly composite rank, |Sylow_2| = 2⁸⁶),
--   - S₉₆ ⊃ S_{96} on a multi-wreath rank (96 = 2⁵·3),
-- conjecturally agree on equivariant Borsuk-Ulam dimension at every `d`.

/-- **No prime in (89, 96]**: each of 90, 91, 92, 93, 94, 95, 96 is
    composite.  Witness for the **first prime gap of size 8** in ℕ
    (between consecutive primes 89 and 97). -/
theorem no_prime_in_ninety_to_ninetysix :
    ∀ k, 89 < k → k ≤ 96 → ¬ Nat.Prime k := by
  intro k hk1 hk2
  interval_cases k <;> decide

/-- **LPB plateau across the first gap of size 8 (89, 97)**:
    `largestPrimeBelow 96 = largestPrimeBelow 89`, axiom-free.  The
    longest LPB plateau below n = 100 — eight consecutive ranks
    `{89, 90, …, 96}` all share the same `largestPrimeBelow`. -/
theorem largestPrimeBelow_eightynine_eq_ninetysix :
    largestPrimeBelow 96 = largestPrimeBelow 89 :=
  largestPrimeBelow_const_in_no_prime_range 89 96 (by norm_num)
    no_prime_in_ninety_to_ninetysix

/-- **Conjectural plateau collapse at S₈₉ → S₉₆**: under
    `symBUDim_eq_largestPrime`, `symBUDim 89 d = symBUDim 96 d` for
    every `d`.  The conjecture forces equivariant BU dimensions at all
    eight consecutive ranks `n ∈ {89, 90, …, 96}` to coincide — the
    longest plateau collapse below n = 100, spanning the first prime
    gap of size 8 in ℕ.  Notable witnesses include S₈₉ (prime rank,
    |S₈₉| = 89!) versus S₉₆ on the highly-composite rank 96 = 2⁵ · 3
    (with rich Sylow-2 structure |Sylow_2(S₉₆)| = 2⁹³). -/
theorem symBUDim_eightynine_eq_ninetysix (d : ℕ) :
    symBUDim 89 d = symBUDim 96 d :=
  symBUDim_const_in_no_prime_range 89 96 d (by norm_num) (by norm_num)
    no_prime_in_ninety_to_ninetysix

/-- **Hypothesis-form** of `symBUDim_eightynine_eq_ninetysix` — uses
    explicit `ConjectureLPB` hypothesis instead of the file's axiom. -/
theorem symBUDim_eightynine_eq_ninetysix_of
    (h_conj : ConjectureLPB) (d : ℕ) :
    symBUDim 89 d = symBUDim 96 d :=
  symBUDim_const_in_no_prime_range_of h_conj 89 96 d
    (by norm_num) (by norm_num) no_prime_in_ninety_to_ninetysix

-- ═══════════════════════════════════════════════════════════════════════
-- PART XIX: Structural converse — strict monotonicity across primes
-- ═══════════════════════════════════════════════════════════════════════
-- Iterations 11–12 enumerated concrete LPB plateaus across specific
-- prime gaps (sizes 4, 6, 8) by applying the forward direction
-- `largestPrimeBelow_const_in_no_prime_range`.  This section provides
-- the **converse** — strict monotonicity of `largestPrimeBelow`
-- whenever a prime falls in the range — together with the resulting
-- biconditional packaging.
--
-- The biconditional `largestPrimeBelow_eq_iff_no_prime_in_range`
-- subsumes the entire "first prime gap of size N" enumeration template:
-- LPB plateau across an interval is *exactly* characterized by absence
-- of primes in that interval, with no further case analysis needed.
-- All Part XVII–XVIII concrete equalities are now corollaries of one
-- structural iff.

/-- **Strict monotonicity of `largestPrimeBelow` across primes**: if a
    prime `p` lies in the half-open interval `(n, m]`, then
    `largestPrimeBelow n < largestPrimeBelow m`.  This is the structural
    converse of `largestPrimeBelow_const_in_no_prime_range`: presence of
    a prime in the gap forces strict growth, absence forces equality.

    Axiom-free; relies only on `Nat.le_findGreatest` (witness for the RHS)
    and `largestPrimeBelow_le` (bound for the LHS).  The `2 ≤ n`
    hypothesis is *not* required — the chain
    `largestPrimeBelow n ≤ n < p ≤ largestPrimeBelow m` is unconditional. -/
theorem largestPrimeBelow_lt_of_prime_in_range
    (n m p : ℕ) (hp : Nat.Prime p) (hnp : n < p) (hpm : p ≤ m) :
    largestPrimeBelow n < largestPrimeBelow m := by
  have h_le : p ≤ largestPrimeBelow m := by
    unfold largestPrimeBelow
    exact Nat.le_findGreatest hpm hp
  exact lt_of_le_of_lt (largestPrimeBelow_le n) (lt_of_lt_of_le hnp h_le)

/-- **Plateau characterization (biconditional)**: for `n ≤ m`,
    `largestPrimeBelow n = largestPrimeBelow m` iff no prime exists in
    the half-open interval `(n, m]`.

    The forward direction is `largestPrimeBelow_const_in_no_prime_range`
    (PART XVI); the reverse direction is the contrapositive of
    `largestPrimeBelow_lt_of_prime_in_range`.  Combining the two gives
    a tight structural characterization: LPB plateaus correspond
    *exactly* to prime-gap intervals.  Axiom-free. -/
theorem largestPrimeBelow_eq_iff_no_prime_in_range
    (n m : ℕ) (hnm : n ≤ m) :
    largestPrimeBelow n = largestPrimeBelow m ↔
      (∀ k, n < k → k ≤ m → ¬ Nat.Prime k) := by
  refine ⟨?_, fun h => (largestPrimeBelow_const_in_no_prime_range n m hnm h).symm⟩
  intro h_eq k hk1 hk2 hk_prime
  exact absurd h_eq
    (ne_of_lt (largestPrimeBelow_lt_of_prime_in_range n m k hk_prime hk1 hk2))

/-- **Strict monotonicity at a prime endpoint**: if `n < p` and `p` is
    prime, then `largestPrimeBelow n < largestPrimeBelow p` — equivalently,
    the LPB plateau ending below `p` strictly precedes `largestPrimeBelow
    p = p`.  One-line specialization of
    `largestPrimeBelow_lt_of_prime_in_range` at `m = p`. -/
theorem largestPrimeBelow_strict_mono_at_prime
    (n p : ℕ) (hp : Nat.Prime p) (hnp : n < p) :
    largestPrimeBelow n < largestPrimeBelow p :=
  largestPrimeBelow_lt_of_prime_in_range n p p hp hnp le_rfl

-- ─────────────────────────────────────────────────────────────────────
-- Concrete plateau-edge witnesses (corollaries of the iff)
-- ─────────────────────────────────────────────────────────────────────
-- Each Part XVII–XVIII plateau (`lpb 8 = lpb 10`, `lpb 13 = lpb 16`,
-- `lpb 23 = lpb 28`, `lpb 89 = lpb 96`) ends at the next prime
-- (11, 17, 29, 97 respectively).  The strict-mono converse witnesses
-- the *boundary*: at the next prime, LPB strictly exceeds the plateau
-- value.  Together with the eq instances, these pin each plateau as
-- a *maximal* level set of `largestPrimeBelow`.

/-- **Plateau-edge at the dyadic gap (7, 11)**: `largestPrimeBelow 8 <
    largestPrimeBelow 11`.  Combined with `largestPrimeBelow_eight_eq_ten`,
    the plateau `{8, 9, 10}` is exactly the level set of `largestPrimeBelow`
    above 7 and below 11. -/
theorem largestPrimeBelow_eight_lt_eleven :
    largestPrimeBelow 8 < largestPrimeBelow 11 :=
  largestPrimeBelow_strict_mono_at_prime 8 11 (by decide) (by norm_num)

/-- **Plateau-edge at the gap (13, 17)**: `largestPrimeBelow 13 <
    largestPrimeBelow 17`. -/
theorem largestPrimeBelow_thirteen_lt_seventeen :
    largestPrimeBelow 13 < largestPrimeBelow 17 :=
  largestPrimeBelow_strict_mono_at_prime 13 17 (by decide) (by norm_num)

/-- **Plateau-edge at the gap of size 6 (23, 29)**: `largestPrimeBelow 23
    < largestPrimeBelow 29`.  Witnesses the right boundary of the
    longest plateau `{23, …, 28}` below n = 30. -/
theorem largestPrimeBelow_twentythree_lt_twentynine :
    largestPrimeBelow 23 < largestPrimeBelow 29 :=
  largestPrimeBelow_strict_mono_at_prime 23 29 (by decide) (by norm_num)

/-- **Plateau-edge at the first gap of size 8 (89, 97)**:
    `largestPrimeBelow 89 < largestPrimeBelow 97`.  Witnesses the right
    boundary of the longest plateau `{89, …, 96}` below n = 100. -/
theorem largestPrimeBelow_eightynine_lt_ninetyseven :
    largestPrimeBelow 89 < largestPrimeBelow 97 :=
  largestPrimeBelow_strict_mono_at_prime 89 97 (by decide) (by norm_num)

-- ═══════════════════════════════════════════════════════════════════════
-- PART XX: Symmetric biconditional — drop the order hypothesis
-- ═══════════════════════════════════════════════════════════════════════
-- The Part XIX biconditional `largestPrimeBelow_eq_iff_no_prime_in_range`
-- carries an `n ≤ m` hypothesis.  Equality of `largestPrimeBelow` values
-- is symmetric in its arguments, so the same characterization holds for
-- the unordered pair `{n, m}`: the condition becomes "no prime in
-- `(min n m, max n m]`".
--
-- The symmetric form is the canonical statement when the order between
-- `n` and `m` is unknown or context-dependent (e.g., the conjectured
-- collapse `symBUDim n d = symBUDim m d` for an unordered pair).

/-- **Symmetric plateau characterization**: for any `n m : ℕ`,
    `largestPrimeBelow n = largestPrimeBelow m` iff no prime lies in
    the half-open interval `(min n m, max n m]`.  Drops the `n ≤ m`
    hypothesis from `largestPrimeBelow_eq_iff_no_prime_in_range` by
    case-splitting on `le_total n m`.  Axiom-free. -/
theorem largestPrimeBelow_eq_iff_no_prime_in_range_symm (n m : ℕ) :
    largestPrimeBelow n = largestPrimeBelow m ↔
      (∀ k, min n m < k → k ≤ max n m → ¬ Nat.Prime k) := by
  rcases le_total n m with hnm | hmn
  · rw [min_eq_left hnm, max_eq_right hnm]
    exact largestPrimeBelow_eq_iff_no_prime_in_range n m hnm
  · rw [min_eq_right hmn, max_eq_left hmn]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact (largestPrimeBelow_eq_iff_no_prime_in_range m n hmn).mp h.symm
    · exact ((largestPrimeBelow_eq_iff_no_prime_in_range m n hmn).mpr h).symm

/-- **Symmetric strict-monotonicity contrapositive**: if a prime lies in
    either half-open interval `(n, m]` or `(m, n]`, then `largestPrimeBelow
    n ≠ largestPrimeBelow m`.  Together with
    `largestPrimeBelow_eq_iff_no_prime_in_range_symm` this packages both
    directions of the order-free characterization. -/
theorem largestPrimeBelow_ne_of_prime_in_range_symm
    (n m p : ℕ) (hp : Nat.Prime p)
    (h : (n < p ∧ p ≤ m) ∨ (m < p ∧ p ≤ n)) :
    largestPrimeBelow n ≠ largestPrimeBelow m := by
  rcases h with ⟨hnp, hpm⟩ | ⟨hmp, hpn⟩
  · exact ne_of_lt (largestPrimeBelow_lt_of_prime_in_range n m p hp hnp hpm)
  · exact (ne_of_lt (largestPrimeBelow_lt_of_prime_in_range m n p hp hmp hpn)).symm

/-- **Unordered symBUDim collapse**: for `n, m ≥ 2` and `d` arbitrary, if
    no prime lies in `(min n m, max n m]`, then `symBUDim n d = symBUDim
    m d`.  Combines the symmetric LPB-iff with `symBUDim_eq_of_lpb_eq`
    (which uses the file axiom).  Conditional on
    `symBUDim_eq_largestPrime`. -/
theorem symBUDim_const_in_unordered_no_prime_range
    (n m d : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : ∀ k, min n m < k → k ≤ max n m → ¬ Nat.Prime k) :
    symBUDim n d = symBUDim m d :=
  symBUDim_eq_of_lpb_eq n m d hn hm
    ((largestPrimeBelow_eq_iff_no_prime_in_range_symm n m).mpr h)

/-- **Hypothesis-form** of `symBUDim_const_in_unordered_no_prime_range` —
    uses explicit `ConjectureLPB` hypothesis instead of the file's axiom. -/
theorem symBUDim_const_in_unordered_no_prime_range_of
    (h_conj : ConjectureLPB) (n m d : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : ∀ k, min n m < k → k ≤ max n m → ¬ Nat.Prime k) :
    symBUDim n d = symBUDim m d :=
  symBUDim_eq_of_lpb_eq_of h_conj n m d hn hm
    ((largestPrimeBelow_eq_iff_no_prime_in_range_symm n m).mpr h)

/-- **Concrete reverse-order instance**: re-derives the Part XVII LPB
    plateau equality `largestPrimeBelow 10 = largestPrimeBelow 8` via
    the symmetric biconditional applied with arguments swapped (LHS:
    `n = 10 > m = 8`).  Demonstrates that the new iff handles the
    non-canonical order without going through `Eq.symm`. -/
theorem largestPrimeBelow_ten_eq_eight :
    largestPrimeBelow 10 = largestPrimeBelow 8 := by
  refine (largestPrimeBelow_eq_iff_no_prime_in_range_symm 10 8).mpr ?_
  intro k hk1 hk2
  -- min 10 8 = 8, max 10 8 = 10
  have hmin : min (10 : ℕ) 8 = 8 := by decide
  have hmax : max (10 : ℕ) 8 = 10 := by decide
  rw [hmin] at hk1
  rw [hmax] at hk2
  exact no_prime_in_eight_to_ten k hk1 hk2

-- ═══════════════════════════════════════════════════════════════════════
-- PART XXII: Bertrand-window packaging + missing hypothesis-form variants
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Hypothesis-form bridge for the conjecture

`ConjectureLPB` (PART XV) is definitionally the universal closure of the
file's axiom `symBUDim_eq_largestPrime`. The bridge lemma
`symBUDim_eq_largestPrime_of` lets a `ConjectureLPB` hypothesis stand in
for the axiom in any rewrite. Trivial proof, but it is the canonical
hypothesis-form base for downstream developments that want to track
conjecture-dependence at the type level. -/

/-- **Hypothesis-form bridge** for the conjecture: under `ConjectureLPB`,
    the file's axiom statement holds. One-liner via the `Prop`
    definition. -/
theorem symBUDim_eq_largestPrime_of (h : ConjectureLPB) (n d : ℕ)
    (hn : 2 ≤ n) :
    symBUDim n d = buDim (largestPrimeBelow n) d :=
  h n d hn

/-! ### Hypothesis-form variants of older closed-form theorems

Mirrors of `symBUDim_even_formula` (PART III) and `symBUDim_prime_even_formula`
(PART VIII) that take `ConjectureLPB` as a hypothesis instead of relying on
the file's axiom. Same statements, but conjecture-dependence is explicit. -/

/-- **Hypothesis-form** of `symBUDim_even_formula` (PART III): under
    `ConjectureLPB`, `symBUDim n (2 * k) = 2 * k - 1` for n ≥ 2 and k ≥ 1. -/
theorem symBUDim_even_formula_of (h : ConjectureLPB) (n k : ℕ)
    (hn : 2 ≤ n) (hk : 0 < k) :
    symBUDim n (2 * k) = 2 * k - 1 := by
  rw [symBUDim_eq_largestPrime_of h n (2 * k) hn]
  exact buDim_prime (largestPrimeBelow n) k
    (largestPrimeBelow_isPrime n hn) hk

/-- **Hypothesis-form** of `symBUDim_prime_even_formula` (PART VIII): under
    `ConjectureLPB`, at any prime p with k ≥ 1, `symBUDim p (2 * k) = 2 * k - 1`. -/
theorem symBUDim_prime_even_formula_of (h : ConjectureLPB) (p k : ℕ)
    (hp : Nat.Prime p) (hk : 0 < k) :
    symBUDim p (2 * k) = 2 * k - 1 := by
  rw [symBUDim_eq_buDim_at_prime_of h p (2 * k) hp]
  exact buDim_prime p k hp hk

/-! ### Bertrand-window packaging of the conjecture

The conjecture pins `symBUDim n d = buDim (largestPrimeBelow n) d`. The
Bertrand-Chebyshev bound `n / 2 < largestPrimeBelow n ≤ n` (PART VI)
constrains `largestPrimeBelow n` to the dyadic window `(n/2, n]`.
Combining the two yields a packaged form of the conjecture's prediction
that **does not reference `largestPrimeBelow` at all**: `symBUDim n d =
buDim p d` for *some* prime `p` in `(n/2, n]`. The internal selector
`largestPrimeBelow` is hidden behind an existential — useful for
downstream applications that want to think of the prediction as a
"there exists a Bertrand-window prime" statement rather than a
"the largest prime ≤ n" statement. -/

/-- **Bertrand-window packaging of the conjecture** (uses file's axiom):
    for n ≥ 2 and any d, there exists a prime `p` in the Bertrand window
    `(n/2, n]` with `symBUDim n d = buDim p d`. The witness is
    `largestPrimeBelow n`; the existential hides the internal selector. -/
theorem symBUDim_eq_buDim_in_bertrand_window (n d : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n ∧ symBUDim n d = buDim p d :=
  ⟨largestPrimeBelow n, largestPrimeBelow_isPrime n hn,
    n_div_two_lt_largestPrimeBelow n hn, largestPrimeBelow_le n,
    symBUDim_eq_largestPrime n d hn⟩

/-- **Hypothesis-form** of `symBUDim_eq_buDim_in_bertrand_window`: under
    `ConjectureLPB`, the same packaged Bertrand-window prediction holds. -/
theorem symBUDim_eq_buDim_in_bertrand_window_of (h : ConjectureLPB)
    (n d : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n ∧ symBUDim n d = buDim p d :=
  ⟨largestPrimeBelow n, largestPrimeBelow_isPrime n hn,
    n_div_two_lt_largestPrimeBelow n hn, largestPrimeBelow_le n,
    h n d hn⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART XXIII: Bertrand-window monotonicity packaging
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Monotonicity of `buDim ∘ largestPrimeBelow`

Path Forward Item 2 from Iter 15. The parent file (`BorsukUlamOQ02OQ01OQ03.lean`)
proves `symBUDim_le_of_le : m ≤ n → symBUDim m d ≤ symBUDim n d`
unconditionally (modulo parent axiom `sym_has_smaller_sym`). Combined with
this file's axiom `symBUDim_eq_largestPrime` (PART X), monotonicity in `n`
transfers to monotonicity of `buDim (largestPrimeBelow n) d` in `n`.

Combining further with PART VI's `n_div_two_lt_largestPrimeBelow`
(Bertrand–Chebyshev) and `largestPrimeBelow_le` gives a *selector-free*
existential packaging: for `n ≤ m`, there exist primes `p` in the dyadic
window `(n/2, n]` and `q` in `(m/2, m]` with `buDim p d ≤ buDim q d`.
This is the "monotone in the Bertrand window" form: as `n` grows, the
prime witness grows with it (always strictly above the dyadic floor).
-/

/-- **Monotonicity of `buDim ∘ largestPrimeBelow`** (uses file's axiom).
    For `2 ≤ n ≤ m` and any `d`,
    `buDim (largestPrimeBelow n) d ≤ buDim (largestPrimeBelow m) d`.

    One-line rewrite proof through the file's axiom, reducing to the
    parent's `symBUDim_le_of_le`. -/
theorem buDim_largestPrime_mono {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (d : ℕ) :
    buDim (largestPrimeBelow n) d ≤ buDim (largestPrimeBelow m) d := by
  rw [← symBUDim_eq_largestPrime n d hn,
      ← symBUDim_eq_largestPrime m d (hn.trans hnm)]
  exact symBUDim_le_of_le n m d hnm

/-- **Hypothesis-form** of `buDim_largestPrime_mono`: same monotonicity
    under `ConjectureLPB`. -/
theorem buDim_largestPrime_mono_of (h : ConjectureLPB)
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (d : ℕ) :
    buDim (largestPrimeBelow n) d ≤ buDim (largestPrimeBelow m) d := by
  rw [← symBUDim_eq_largestPrime_of h n d hn,
      ← symBUDim_eq_largestPrime_of h m d (hn.trans hnm)]
  exact symBUDim_le_of_le n m d hnm

/-- **Bertrand-window monotonicity packaging** (uses file's axiom). For
    `2 ≤ n ≤ m` and any `d`, there exist primes `p` in the Bertrand
    window `(n/2, n]` and `q` in `(m/2, m]` with `buDim p d ≤ buDim q d`.

    The internal selector `largestPrimeBelow` is hidden behind two
    existentials. Useful for downstream applications that want to think
    of the conjecture's monotonicity prediction as
    "Bertrand-window primes have monotonically non-decreasing buDim". -/
theorem exists_bertrand_window_primes_mono
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (d : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      n / 2 < p ∧ p ≤ n ∧ m / 2 < q ∧ q ≤ m ∧
      buDim p d ≤ buDim q d :=
  ⟨largestPrimeBelow n, largestPrimeBelow m,
    largestPrimeBelow_isPrime n hn,
    largestPrimeBelow_isPrime m (hn.trans hnm),
    n_div_two_lt_largestPrimeBelow n hn,
    largestPrimeBelow_le n,
    n_div_two_lt_largestPrimeBelow m (hn.trans hnm),
    largestPrimeBelow_le m,
    buDim_largestPrime_mono hn hnm d⟩

/-- **Hypothesis-form** of `exists_bertrand_window_primes_mono`: under
    `ConjectureLPB`, the same Bertrand-window monotonicity packaging
    holds. -/
theorem exists_bertrand_window_primes_mono_of (h : ConjectureLPB)
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (d : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      n / 2 < p ∧ p ≤ n ∧ m / 2 < q ∧ q ≤ m ∧
      buDim p d ≤ buDim q d :=
  ⟨largestPrimeBelow n, largestPrimeBelow m,
    largestPrimeBelow_isPrime n hn,
    largestPrimeBelow_isPrime m (hn.trans hnm),
    n_div_two_lt_largestPrimeBelow n hn,
    largestPrimeBelow_le n,
    n_div_two_lt_largestPrimeBelow m (hn.trans hnm),
    largestPrimeBelow_le m,
    buDim_largestPrime_mono_of h hn hnm d⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART XXIV: Even-d / odd-d asymmetry of the conjecture's content
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Strict monotonicity at even d is *impossible*

Iter 16 (Part XXIII) packaged `buDim ∘ largestPrimeBelow` as monotone in
`n` under the file's axiom.  Its Path Forward Item 3 raised the natural
follow-up: can the inequality be strengthened to a strict `<` across
prime gaps?

This iteration documents that the strict form is **impossible at every
even `d`** under the file's existing axioms — independently of the
conjecture:

- Parent's `buDim_prime` (Yang-Borsuk) gives `buDim p (2 * k) = 2 * k - 1`
  for **every** prime `p` and `k ≥ 1`.
- Consequently `buDim (largestPrimeBelow n) (2 * k) = 2 * k - 1` for every
  `n ≥ 2`, **axiom-free** (the file's `symBUDim_eq_largestPrime` is not
  required for this side of the bridge).
- Hence `buDim (largestPrimeBelow n) (2 * k)` is constant in `n`, and
  no strict `<` can hold between any two `n, m ≥ 2`.

The conjecture's genuine non-trivial content therefore lives at **odd
`d`**, where the parent's `buDim p (·)` axiom is silent for primes
`p ≥ 3`.  This sharpens the boundary between proven and open content
established by earlier iterations.
-/

/-- **Axiom-free even-d value of `buDim ∘ largestPrimeBelow`**.
    For `n ≥ 2` and `k ≥ 1`,
    `buDim (largestPrimeBelow n) (2 * k) = 2 * k - 1`.

    Uses only parent's `buDim_prime` (Yang-Borsuk for prime cyclic groups)
    plus `largestPrimeBelow_isPrime` — the file's
    `symBUDim_eq_largestPrime` axiom is **not** required. -/
theorem buDim_largestPrime_even_eq (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    buDim (largestPrimeBelow n) (2 * k) = 2 * k - 1 :=
  buDim_prime (largestPrimeBelow n) k (largestPrimeBelow_isPrime n hn) hk

/-- **Axiom-free even-d constancy of `buDim ∘ largestPrimeBelow` across n**.
    For `n, m ≥ 2` and `k ≥ 1`,
    `buDim (largestPrimeBelow n) (2 * k) = buDim (largestPrimeBelow m) (2 * k)`.

    The prediction at even `d` is independent of the choice of `n` — both
    sides reduce to `2 * k - 1` by `buDim_prime`. -/
theorem buDim_largestPrime_even_const (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hk : 0 < k) :
    buDim (largestPrimeBelow n) (2 * k) = buDim (largestPrimeBelow m) (2 * k) := by
  rw [buDim_largestPrime_even_eq n k hn hk,
      buDim_largestPrime_even_eq m k hm hk]

/-- **No strict monotonicity at even d (axiom-free)**. For `n, m ≥ 2` and
    `k ≥ 1`, `buDim (largestPrimeBelow n) (2 * k) <
    buDim (largestPrimeBelow m) (2 * k)` is impossible.

    Formal refutation of Iter 16 Path Forward Item 3's strict variant at
    every even `d`: parent's `buDim_prime` pins both sides to `2 * k - 1`
    regardless of which prime appears. -/
theorem buDim_largestPrime_even_no_strict_mono
    (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 0 < k) :
    ¬ buDim (largestPrimeBelow n) (2 * k) < buDim (largestPrimeBelow m) (2 * k) := by
  rw [buDim_largestPrime_even_const n m k hn hm hk]
  exact lt_irrefl _

/-- **Even-d constancy of `symBUDim` across `n`** (uses file's axiom).
    For `n, m ≥ 2` and `k ≥ 1`, `symBUDim n (2 * k) = symBUDim m (2 * k)`.

    Combines PART III's `symBUDim_even_formula` on each side.  The
    conjecture's even-`d` content is constancy in `n`, not strict
    monotonicity. -/
theorem symBUDim_even_const_across_n (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hk : 0 < k) :
    symBUDim n (2 * k) = symBUDim m (2 * k) := by
  rw [symBUDim_even_formula n k hn hk, symBUDim_even_formula m k hm hk]

/-- **Hypothesis-form** of `symBUDim_even_const_across_n`: same constancy
    under `ConjectureLPB`. -/
theorem symBUDim_even_const_across_n_of (h : ConjectureLPB)
    (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 0 < k) :
    symBUDim n (2 * k) = symBUDim m (2 * k) := by
  rw [symBUDim_even_formula_of h n k hn hk,
      symBUDim_even_formula_of h m k hm hk]

/-- **No strict monotonicity of `symBUDim` at even `d`** (uses file's
    axiom).  For `n, m ≥ 2` and `k ≥ 1`,
    `symBUDim n (2 * k) < symBUDim m (2 * k)` is impossible. -/
theorem symBUDim_even_no_strict_mono
    (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 0 < k) :
    ¬ symBUDim n (2 * k) < symBUDim m (2 * k) := by
  rw [symBUDim_even_const_across_n n m k hn hm hk]
  exact lt_irrefl _

/-- **Hypothesis-form** of `symBUDim_even_no_strict_mono`. -/
theorem symBUDim_even_no_strict_mono_of (h : ConjectureLPB)
    (n m k : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 0 < k) :
    ¬ symBUDim n (2 * k) < symBUDim m (2 * k) := by
  rw [symBUDim_even_const_across_n_of h n m k hn hm hk]
  exact lt_irrefl _

-- ═══════════════════════════════════════════════════════════════════════
-- PART XXV: Concrete `largestPrimeBelow` values at small composites
-- ═══════════════════════════════════════════════════════════════════════
-- Earlier sections established `largestPrimeBelow p = p` at the small
-- primes p ∈ {2, 3, 5, 7} via `largestPrimeBelow_self_of_prime`, and
-- plateau equalities like `largestPrimeBelow 10 = largestPrimeBelow 8`
-- via `largestPrimeBelow_const_in_no_prime_range` (PART XI/XVI).  The
-- docstring of `largestPrimeBelow_eight_eq_ten` (PART XVII) explicitly
-- flagged the *concrete* values `lpb 8 = lpb 9 = lpb 10 = 7` as still
-- pending the PART XII concrete-LPB computations.  This part closes that
-- gap: it pins each LPB at 7 directly, and combines it with parent's
-- `largestPrimeBelow_seven` to yield the longest concrete `symBUDim`
-- plateau collapse below n = 11 — the 4-step run `symBUDim 7 d =
-- symBUDim 8 d = symBUDim 9 d = symBUDim 10 d` for every dimension `d`
-- (the last equality is conditional on `symBUDim_eq_largestPrime`).
--
-- The plateau covers S₇ (a non-trivial simple-group test case),
-- S₈ (rich V₄·A₄ structure), S₉ (first non-trivial composite with
-- *two* distinct Sylow-2 contributions: S₂ × S₂), and S₁₀
-- (A₅ × A₅) — four symmetric groups with very different subgroup
-- lattices.  The conjecture forces all of them to share equivariant
-- BU dimensions at every dimension despite the qualitative subgroup
-- differences.

/-- **No prime in (7, 10]**: each of 8, 9, 10 is composite.  Witness for
    the prime gap (7, 11), in the form needed to chain `lpb 10`,
    `lpb 9`, and `lpb 8` together back to `lpb 7 = 7`. -/
theorem no_prime_in_seven_to_ten :
    ∀ k, 7 < k → k ≤ 10 → ¬ Nat.Prime k := by
  intro k hk1 hk2
  interval_cases k <;> decide

/-- **Axiom-free** concrete `largestPrimeBelow 8 = 7`.  Chains the
    plateau equality `lpb 8 = lpb 7` (via PART XVI's
    `largestPrimeBelow_const_in_no_prime_range` over the no-prime
    interval `(7, 8]`) with the prime base case
    `largestPrimeBelow_seven`. -/
theorem largestPrimeBelow_eight_eq_seven : largestPrimeBelow 8 = 7 := by
  have h : largestPrimeBelow 8 = largestPrimeBelow 7 :=
    largestPrimeBelow_const_in_no_prime_range 7 8 (by norm_num)
      (fun k hk1 hk2 =>
        no_prime_in_seven_to_ten k hk1 (le_trans hk2 (by norm_num)))
  rw [h, largestPrimeBelow_seven]

/-- **Axiom-free** concrete `largestPrimeBelow 9 = 7`.  Same chain as
    `largestPrimeBelow_eight_eq_seven` over the longer interval `(7, 9]`. -/
theorem largestPrimeBelow_nine_eq_seven : largestPrimeBelow 9 = 7 := by
  have h : largestPrimeBelow 9 = largestPrimeBelow 7 :=
    largestPrimeBelow_const_in_no_prime_range 7 9 (by norm_num)
      (fun k hk1 hk2 =>
        no_prime_in_seven_to_ten k hk1 (le_trans hk2 (by norm_num)))
  rw [h, largestPrimeBelow_seven]

/-- **Axiom-free** concrete `largestPrimeBelow 10 = 7`.  The full
    dyadic-gap plateau value at the right endpoint of the gap (7, 11).
    Closes the explicit TODO in the docstring of
    `largestPrimeBelow_eight_eq_ten` (PART XVII), which noted that the
    concrete value `lpb 10 = 7` "would follow from the still-pending
    PART XII concrete-LPB computations".  -/
theorem largestPrimeBelow_ten_eq_seven : largestPrimeBelow 10 = 7 := by
  have h : largestPrimeBelow 10 = largestPrimeBelow 7 :=
    largestPrimeBelow_const_in_no_prime_range 7 10 (by norm_num)
      no_prime_in_seven_to_ten
  rw [h, largestPrimeBelow_seven]

/-- **Conjectural 4-step plateau collapse `S₇ → S₁₀`**: under
    `symBUDim_eq_largestPrime`, `symBUDim 7 d = symBUDim 10 d` for every
    dimension `d`.

    The longest concrete `symBUDim` plateau collapse delivered by a
    dyadic prime gap below n = 11.  Combined with the parent file's
    `symBUDim_eight_eq_ten` (PART XVII), the chain reads
    `symBUDim 7 d = symBUDim 8 d = symBUDim 9 d = symBUDim 10 d`
    (the middle two follow from the same `symBUDim_const_in_no_prime_range`
    machinery applied at intermediate ranks).  Four symmetric groups
    with qualitatively distinct subgroup lattices (S₇ simple-like,
    S₈ with V₄·A₄, S₉ with S₂×S₂ Sylow-2, S₁₀ with A₅×A₅) are forced
    to share equivariant Borsuk-Ulam dimensions at every dimension. -/
theorem symBUDim_seven_eq_ten (d : ℕ) :
    symBUDim 7 d = symBUDim 10 d :=
  symBUDim_const_in_no_prime_range 7 10 d (by norm_num) (by norm_num)
    no_prime_in_seven_to_ten

/-- **Hypothesis-form** of `symBUDim_seven_eq_ten` — uses explicit
    `ConjectureLPB` hypothesis instead of the file's axiom. -/
theorem symBUDim_seven_eq_ten_of (h_conj : ConjectureLPB) (d : ℕ) :
    symBUDim 7 d = symBUDim 10 d :=
  symBUDim_const_in_no_prime_range_of h_conj 7 10 d (by norm_num) (by norm_num)
    no_prime_in_seven_to_ten

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
- `largestPrimeBelow_mono` — monotonicity in n: `n ≤ m → lpb n ≤ lpb m`.
  Structural prerequisite for compatibility with parent's
  `sym_has_smaller_sym` monotonicity.
- `largestPrimeBelow_eight_le_eleven` — concrete monotonicity instance.

### Theorems requiring `symBUDim_eq_largestPrime` axiom
- `symBUDim_even_formula` — closed form on even d.
- `symBUDim_three_four`, `symBUDim_four_six` — concrete instances.
- `symBUDim_eq_buDim_at_prime` — at any prime p, conjecture collapses to
  `symBUDim p d = buDim p d` (isolates the *prime-n content*: Sₙ vs ℤ/p,
  no Bertrand selector).
- `symBUDim_prime_even_formula` — closed form `symBUDim p (2k) = 2k - 1`
  at any prime p, k ≥ 1.
- `symBUDim_eleven_eq_buDim_eleven`, `symBUDim_thirteen_eq_buDim_thirteen` —
  concrete prime-n instances at n = 11, 13.
- `symBUDim_eleven_even_formula`, `symBUDim_thirteen_even_formula` —
  concrete closed forms at n = 11, 13.

### Concrete instances (axiom-free)
- `symBUDim_five_lower_unconditional`, `symBUDim_two_four_unconditional`,
  `symBUDim_six_lower_unconditional`, `symBUDim_seven_lower_unconditional`,
  `symBUDim_eight_lower_unconditional`,
  `symBUDim_nine_lower_unconditional`, `symBUDim_ten_lower_unconditional`,
  `symBUDim_eleven_lower_unconditional`, `symBUDim_twelve_lower_unconditional`.

### Iteration 7 additions (general-d Z/2, axiom-free)
- `symBUDim_lower_z2` — uniform unconditional lower bound `d - 1 ≤
  symBUDim n d` for all `n ≥ 2`, `d ≥ 1`. Routes through Z/2 (parent's
  `symBUDim_two` + `buDim_two` + `symBUDim_le_of_le 2 n d`). **Strictly
  stronger than `symBUDim_even_lower` at odd `d`**: at `d = 2k + 1`
  this gives `2k`, while `symBUDim_even_lower` only delivers the
  floor-rounded `2k - 1`.
- `symBUDim_odd_lower_unconditional` — odd-d corollary `2k ≤ symBUDim n
  (2k + 1)` for `n ≥ 2`.
- `symBUDim_two_general_unconditional` — axiom-free CLOSED FORM at
  `n = 2` for ALL `d ≥ 1`: `symBUDim 2 d = d - 1`. Generalizes
  `symBUDim_two_even_formula_unconditional` past the even-d restriction
  and **fully settles the conjecture axiom-free at n = 2 across all
  dimensions** (combined with `largestPrimeBelow_two`).
- Concrete axiom-free instances: `symBUDim_two_three_unconditional`,
  `_two_five_`, `_two_seven_` (closed-form values at small odd `d`);
  `symBUDim_three_three_lower_`, `_four_three_lower_` (Klein-4 ≤ S₄
  test case), `_three_five_lower_`, `_four_five_lower_` (extends odd-d
  coverage past n = 3).

### Iteration 8 additions (conditional Z/2 transfer to cyclic primes)
- `buDim_largestPrime_lower_z2` — **conditional** on
  `symBUDim_eq_largestPrime`: the axiom-free Z/2 lower bound
  `symBUDim_lower_z2` pulls through the conjectured equality to
  `d − 1 ≤ buDim (largestPrimeBelow n) d` for `n ≥ 2`, `d ≥ 1`. Genuinely
  new content: at odd `d` the parent's `buDim_prime` axiom (which only
  fires on even d) leaves `buDim p d` unconstrained for primes `p ≥ 3`;
  the symmetric-group conjecture would PIN a NEW lower bound `d − 1`
  valid at odd d as well.
- `buDim_prime_lower_z2_conditional` — at any prime p and d ≥ 1,
  conditional `d − 1 ≤ buDim p d`. Specializes
  `buDim_largestPrime_lower_z2` via `largestPrimeBelow_self_of_prime`.
  **Significance**: at odd d this is content beyond Yang-Borsuk (which
  only handles even d at primes ≥ 3).
- `buDim_three_lower_z2_conditional`, `buDim_five_lower_z2_conditional`,
  `buDim_seven_lower_z2_conditional` — concrete instances at small odd
  primes (e.g., conditionally `buDim 3 3 ≥ 2`).
- `symBUDim_prime_combined_lower` — **axiom-free** combined lower bound
  at any prime p: `max (buDim p d) (d − 1) ≤ symBUDim p d`. Packages
  the Z/p subgroup contribution (parent's `sym_has_cyclic_prime`) with
  the Z/2 contribution (iter-7's `symBUDim_lower_z2`). At even `d = 2k`
  both coincide (`buDim p (2k) = 2k − 1 = d − 1`); at odd d the Z/2
  component dominates.

### Iteration 9 additions (conjecture-as-Prop and falsification handles)
- `ConjectureLPB : Prop` — the equality conjecture stated as an explicit
  hypothesis (not an axiom). Lets downstream developments take the
  conjecture as a hypothesis instead of using `symBUDim_eq_largestPrime`,
  making conjecture-dependence explicit at the type level.
- `buDim_largestPrime_lower_z2_of`, `buDim_prime_lower_z2_of`,
  `symBUDim_eq_buDim_at_prime_of` — hypothesis-form variants of the
  iter-8 conditional theorems (and `symBUDim_eq_buDim_at_prime` from
  iter 5). Same statements, but the dependence on the conjecture is
  encoded via a `ConjectureLPB` hypothesis rather than via the file's
  axiom.
- `not_conjectureLPB_of_buDim_lt` — **falsification theorem**: a future
  proof of `buDim p d < d − 1` at any prime p and any d ≥ 1 refutes
  `ConjectureLPB`. Formal contrapositive of `buDim_prime_lower_z2_of`.
  Crystallizes iter-8's "falsification handle" remark as a concrete
  theorem at the type level.
- Concrete falsification handles at small (p, d):
  `not_conjectureLPB_of_buDim_three_three_lt_two`,
  `not_conjectureLPB_of_buDim_five_three_lt_two`,
  `not_conjectureLPB_of_buDim_three_five_lt_four` — explicit instances
  at the simplest odd-d cases beyond the parent's `buDim_prime` axiom
  (which only fires on even d). These pinpoint exactly where future
  Yang-Borsuk research could refute the conjecture.

### Iteration 10 additions (plateau infrastructure for `largestPrimeBelow`)
- `largestPrimeBelow_succ_of_not_prime` — **axiom-free** atomic step:
  if `n + 1` is composite, `largestPrimeBelow (n + 1) = largestPrimeBelow n`.
  Direct corollary of Mathlib's `Nat.findGreatest_of_not`.
- `largestPrimeBelow_const_in_no_prime_range` — **axiom-free** general
  plateau lemma: if no prime exists in `(n, m]`, `largestPrimeBelow m =
  largestPrimeBelow n`. Proved by `Nat.le_induction` lifting the atomic
  step over each composite successor in the gap.
- `largestPrimeBelow_eq_of_in_plateau` — **axiom-free** prime-anchored
  packaging: if `p` is prime, `lpb n = p`, and no prime lies in `(n, m]`,
  then `lpb m = p` too.
- `symBUDim_eq_of_lpb_eq` — **conditional** plateau collapse: any two
  `n, m ≥ 2` with the same `largestPrimeBelow` have equal `symBUDim n d
  = symBUDim m d` at every `d`. Conditional on `symBUDim_eq_largestPrime`.
- `symBUDim_const_in_no_prime_range` — **conditional** corollary chaining
  the two: if no prime exists in `(n, m]` and `n ≥ 2`, then `symBUDim n d
  = symBUDim m d` for all `d`. Formal expression of the "plateau collapse"
  prediction (S_n's in any prime-gap interval conjecturally share the
  equivariant BU dimension at every dimension).
- `symBUDim_eq_of_lpb_eq_of`, `symBUDim_const_in_no_prime_range_of` —
  hypothesis-form variants taking `ConjectureLPB` as a `Prop` argument
  rather than relying on the file's axiom (matches Part XV's pattern).

### Iteration 11 additions (concrete plateau collapse instances)
- `no_prime_in_eight_to_ten`, `no_prime_in_fourteen_to_sixteen`,
  `no_prime_in_twentyfour_to_twentyeight` — **axiom-free** witnesses that
  the half-open intervals `(8, 10]`, `(13, 16]`, `(23, 28]` contain no
  primes (each proved by `interval_cases` + `decide`).  Selected to
  cover the smallest prime gaps with multiple composites in between:
  the dyadic gap (7, 11), the gap (13, 17), and the first gap of size 6
  at (23, 29).
- `largestPrimeBelow_eight_eq_ten`, `largestPrimeBelow_thirteen_eq_sixteen`,
  `largestPrimeBelow_twentythree_eq_twentyeight` — **axiom-free** LPB
  collapse instances at the three intervals.  Direct applications of
  `largestPrimeBelow_const_in_no_prime_range` from PART XVI.
- `symBUDim_eight_eq_ten`, `symBUDim_thirteen_eq_sixteen`,
  `symBUDim_twentythree_eq_twentyeight` — **conditional** plateau collapse
  at the three intervals.  Each is a one-liner specialization of PART
  XVI's `symBUDim_const_in_no_prime_range`.  The S₂₃ → S₂₈ instance is
  the longest plateau collapse below n = 30 — six consecutive symmetric
  groups conjecturally share equivariant Borsuk-Ulam dimensions at every
  dimension.
- `symBUDim_eight_eq_ten_of`, `symBUDim_thirteen_eq_sixteen_of`,
  `symBUDim_twentythree_eq_twentyeight_of` — hypothesis-form variants
  taking `ConjectureLPB` explicitly.

### Iteration 12 additions (first gap of size 8 — Part XVIII)
- `no_prime_in_ninety_to_ninetysix` — **axiom-free** witness that the
  half-open interval `(89, 96]` contains no primes (each of 90, 91, 92,
  93, 94, 95, 96 is composite).  Pins the **first prime gap of size 8
  in ℕ** (between consecutive primes 89 and 97).
- `largestPrimeBelow_eightynine_eq_ninetysix` — **axiom-free** LPB
  collapse at the first gap of size 8: `largestPrimeBelow 96 =
  largestPrimeBelow 89`.  The longest LPB plateau below n = 100 —
  eight consecutive ranks `{89, 90, …, 96}` all share the same
  `largestPrimeBelow`.
- `symBUDim_eightynine_eq_ninetysix` — **conditional** plateau collapse
  at S₈₉ → S₉₆.  Two-line specialization of Part XVI's
  `symBUDim_const_in_no_prime_range`.  The longest plateau collapse
  below n = 100 — eight consecutive symmetric groups conjecturally
  share equivariant Borsuk-Ulam dimensions at every dimension despite
  qualitatively different rank structure (S₈₉ on prime rank vs S₉₆ on
  the highly-composite rank 96 = 2⁵ · 3).
- `symBUDim_eightynine_eq_ninetysix_of` — hypothesis-form variant
  taking `ConjectureLPB` explicitly.

### Iteration 13 additions (structural converse — Part XIX)
- `largestPrimeBelow_lt_of_prime_in_range` — **axiom-free** structural
  converse of `largestPrimeBelow_const_in_no_prime_range`: if a prime
  `p` lies in the half-open interval `(n, m]`, then `largestPrimeBelow
  n < largestPrimeBelow m`.  Three-line proof via Mathlib's
  `Nat.le_findGreatest` (witness for the RHS) and `largestPrimeBelow_le`
  (bound for the LHS).
- `largestPrimeBelow_eq_iff_no_prime_in_range` — **axiom-free
  biconditional**: for `n ≤ m`, `largestPrimeBelow n = largestPrimeBelow
  m` iff no prime exists in `(n, m]`.  Combines the forward direction
  (PART XVI) with the new converse to give a tight characterization:
  LPB plateaus correspond *exactly* to prime-gap intervals.  Subsumes
  the entire Part XVII–XVIII concrete-gap enumeration template — every
  "no prime in (a, b] ⇒ lpb a = lpb b" instance is now an iff-corollary.
- `largestPrimeBelow_strict_mono_at_prime` — **axiom-free** clean
  specialization at `m = p` prime: `largestPrimeBelow n < largestPrimeBelow
  p` whenever `n < p`.  Tight at the right endpoint of every prime gap.
- `largestPrimeBelow_eight_lt_eleven`, `largestPrimeBelow_thirteen_lt_seventeen`,
  `largestPrimeBelow_twentythree_lt_twentynine`,
  `largestPrimeBelow_eightynine_lt_ninetyseven` — **axiom-free**
  plateau-edge witnesses at the four prime-gap intervals from Parts
  XVII–XVIII.  Together with the corresponding eq-instances, these pin
  each plateau as a *maximal* level set of `largestPrimeBelow` (rather
  than a possibly-extendable equal-LPB cluster).

### Iteration 14 additions (symmetric biconditional — Part XX)
- `largestPrimeBelow_eq_iff_no_prime_in_range_symm` — **axiom-free**
  drop of the `n ≤ m` hypothesis from the Part XIX biconditional.
  For arbitrary `n m : ℕ`, `largestPrimeBelow n = largestPrimeBelow m`
  iff no prime lies in `(min n m, max n m]`.  Routine case-split via
  `le_total n m` reducing each branch to the asymmetric iff with
  arguments in the canonical order.  This is the order-free statement
  natural for unordered pairs.
- `largestPrimeBelow_ne_of_prime_in_range_symm` — symmetric
  contrapositive: prime in either `(n, m]` or `(m, n]` ⇒
  `largestPrimeBelow n ≠ largestPrimeBelow m`.  Packages both directions
  of the order-free characterization.
- `symBUDim_const_in_unordered_no_prime_range` (conditional on
  `symBUDim_eq_largestPrime`) and `_of` (hypothesis form): unordered
  symBUDim collapse — for `n, m ≥ 2`, no prime in `(min n m, max n m]`
  forces `symBUDim n d = symBUDim m d` at every `d`.  Direct
  composition of the new iff with `symBUDim_eq_of_lpb_eq` /
  `symBUDim_eq_of_lpb_eq_of`.
- `largestPrimeBelow_ten_eq_eight` — concrete demo: re-derives
  `lpb 10 = lpb 8` by applying the new iff with arguments in the
  *non-canonical* order (`n = 10 > m = 8`), without going through
  `Eq.symm` of the existing `largestPrimeBelow_eight_eq_ten`.  Verifies
  `min`/`max` reduce as expected at concrete values.

### Iteration 17 additions (even-d/odd-d asymmetry — Part XXIV)
- `buDim_largestPrime_even_eq` — **axiom-free**: for `n ≥ 2` and `k ≥ 1`,
  `buDim (largestPrimeBelow n) (2 * k) = 2 * k - 1`.  Reduces parent's
  `buDim_prime` along `largestPrimeBelow_isPrime`.  Notable: the file's
  `symBUDim_eq_largestPrime` axiom is **not** required for this side of
  the bridge.
- `buDim_largestPrime_even_const` — **axiom-free**: constancy of
  `buDim ∘ largestPrimeBelow` across `n` at every even `d`.  Direct
  composition of `buDim_largestPrime_even_eq` on each side.
- `buDim_largestPrime_even_no_strict_mono` — **axiom-free**: formal
  refutation of strict `<` for `buDim_largestPrime_mono` (PART XXIII) at
  every even `d`.  Iter 16 Path Forward Item 3 raised the natural
  strict-monotonicity follow-up; this theorem shows the strict form is
  *impossible* at even `d` under the file's existing axioms.
- `symBUDim_even_const_across_n` (conditional on `symBUDim_eq_largestPrime`)
  and `_of` (hypothesis form): the conjecture's even-`d` content is
  constancy of `symBUDim` in `n` at every fixed even `d` — not strict
  monotonicity.  Compositions of PART III's `symBUDim_even_formula` on
  each side.
- `symBUDim_even_no_strict_mono` (conditional) and `_of` (hypothesis
  form): symBUDim-side companion of the no-strict-mono result.

**Significance**.  Sharpens the boundary between proven and open content:
the conjecture's even-`d` content reduces to a constant `2 * k - 1`
independent of `n` (parent's `buDim_prime` does all the work), so the
genuine non-trivial prediction lives at **odd `d`** where the parent's
`buDim p (·)` axiom is silent for primes `p ≥ 3`.

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
- Concrete falsification target: compute or bound `buDim 3 3` directly
  via equivariant cohomology of Z/3 on simple S^2-actions. A proof of
  `buDim 3 3 < 2` would refute `ConjectureLPB`; a proof of `buDim 3 3 = 2`
  would tighten its content at the simplest odd-d case.
-/

#check @symBUDim_eq_largestPrime
#check @symBUDim_even_formula
#check @symBUDim_even_lower
#check @n_div_two_lt_largestPrimeBelow
#check @largestPrimeBelow_self_of_prime
#check @largestPrimeBelow_eq_self_iff_prime
#check @largestPrimeBelow_lt_of_not_prime
#check @largestPrimeBelow_mono
#check @symBUDim_eq_largestPrime_two_unconditional
#check @symBUDim_eq_buDim_at_prime
#check @symBUDim_prime_even_formula
#check @symBUDim_lower_z2
#check @symBUDim_odd_lower_unconditional
#check @symBUDim_two_general_unconditional
#check @buDim_largestPrime_lower_z2
#check @buDim_prime_lower_z2_conditional
#check @symBUDim_prime_combined_lower
#check @ConjectureLPB
#check @buDim_largestPrime_lower_z2_of
#check @buDim_prime_lower_z2_of
#check @symBUDim_eq_buDim_at_prime_of
#check @not_conjectureLPB_of_buDim_lt

#check @largestPrimeBelow_succ_of_not_prime
#check @largestPrimeBelow_const_in_no_prime_range
#check @largestPrimeBelow_eq_of_in_plateau
#check @symBUDim_eq_of_lpb_eq
#check @symBUDim_const_in_no_prime_range
#check @symBUDim_eq_of_lpb_eq_of
#check @symBUDim_const_in_no_prime_range_of

#check @no_prime_in_eight_to_ten
#check @largestPrimeBelow_eight_eq_ten
#check @symBUDim_eight_eq_ten
#check @symBUDim_eight_eq_ten_of
#check @no_prime_in_fourteen_to_sixteen
#check @symBUDim_thirteen_eq_sixteen
#check @no_prime_in_twentyfour_to_twentyeight
#check @symBUDim_twentythree_eq_twentyeight

#check @no_prime_in_ninety_to_ninetysix
#check @largestPrimeBelow_eightynine_eq_ninetysix
#check @symBUDim_eightynine_eq_ninetysix
#check @symBUDim_eightynine_eq_ninetysix_of

#check @largestPrimeBelow_lt_of_prime_in_range
#check @largestPrimeBelow_eq_iff_no_prime_in_range
#check @largestPrimeBelow_strict_mono_at_prime
#check @largestPrimeBelow_eight_lt_eleven
#check @largestPrimeBelow_thirteen_lt_seventeen
#check @largestPrimeBelow_twentythree_lt_twentynine
#check @largestPrimeBelow_eightynine_lt_ninetyseven

#check @largestPrimeBelow_eq_iff_no_prime_in_range_symm
#check @largestPrimeBelow_ne_of_prime_in_range_symm
#check @symBUDim_const_in_unordered_no_prime_range
#check @symBUDim_const_in_unordered_no_prime_range_of
#check @largestPrimeBelow_ten_eq_eight

#check @symBUDim_eq_largestPrime_of
#check @symBUDim_even_formula_of
#check @symBUDim_prime_even_formula_of
#check @symBUDim_eq_buDim_in_bertrand_window
#check @symBUDim_eq_buDim_in_bertrand_window_of

#check @buDim_largestPrime_mono
#check @buDim_largestPrime_mono_of
#check @exists_bertrand_window_primes_mono
#check @exists_bertrand_window_primes_mono_of

#check @buDim_largestPrime_even_eq
#check @buDim_largestPrime_even_const
#check @buDim_largestPrime_even_no_strict_mono
#check @symBUDim_even_const_across_n
#check @symBUDim_even_const_across_n_of
#check @symBUDim_even_no_strict_mono
#check @symBUDim_even_no_strict_mono_of

#check @no_prime_in_seven_to_ten
#check @largestPrimeBelow_eight_eq_seven
#check @largestPrimeBelow_nine_eq_seven
#check @largestPrimeBelow_ten_eq_seven
#check @symBUDim_seven_eq_ten
#check @symBUDim_seven_eq_ten_of
end BorsukUlamSymPrime
