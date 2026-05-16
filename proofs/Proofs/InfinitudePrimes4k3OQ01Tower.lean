import Proofs.InfinitudePrimes4k3
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Factorial-Tower Bound for Primes ≡ 3 (mod 4)

S6 PREP Path C deliverable for `infinitude-primes-4k3-oq-01`, routed
into a regression-resilient sub-file per S8 PREP option (b).

S2 ACT(a) `InfinitudePrimes4k3OQ01.lean` provides the bridge between
the elementary `% 4 = 3` form and the Mathlib ZMod form via the
`DirichletsTheorem.dirichlet_zmod` corollary. That file transitively
imports `Proofs.DirichletsTheorem`, which currently bears 9 v4.26.0
regressions (see S3 ACT R1 cross-slug note + S7 STATE-SYNC §11).

This file (`InfinitudePrimes4k3OQ01Tower.lean`) provides the
**factorial-tower explicit bound** for primes ≡ 3 (mod 4) without
touching `DirichletsTheorem`, mirroring the regression-resilient
pattern of `InfinitudePrimes4k3OQ01Klein2.lean` (S3 ACT R1, #19088).

## What this file contributes

1. **`tower : ℕ → ℕ`** — factorial-iterated super-exponential
   sequence with `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`.
2. **`primeSeq_3_mod_4 : ℕ → ℕ`** — explicit increasing prime sequence
   ≡ 3 (mod 4), each term bounded by the next `tower` value.
3. **`primeSeq_3_mod_4_prime`**, **`_mod`**, **`primeSeq_strict_mono`**,
   **`primeSeq_le_tower`** — the four helper theorems composing the
   `Classical.choose`-spec quadruple.
4. **`primes_3_mod_4_explicit_tower_bound`** — the qualitative
   corollary that the slug's `state.md` calls out:
   `∀ k, ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ tower k`.

## Dependency surface

- `Proofs.InfinitudePrimes4k3` (parent file) provides
  `infinitely_many_primes_3_mod_4_bounded`, the strengthened
  bounded-witness variant added in S9 ACT R1's parent-file edit
  (S8 PREP §5).
- `Mathlib.Data.Nat.Factorial.Basic` provides `Nat.factorial_pos`,
  `Nat.factorial_le`.
- `Mathlib.Tactic` provides `omega`, `decide`, `simp`, and
  `strictMono_nat_of_lt_succ`.

**Imports NOT taken** (relative to `InfinitudePrimes4k3OQ01.lean`):

- `Proofs.DirichletsTheorem` — the regression-bearing file (9 v4.26.0
  errors at lines 124, 140, 148, 178, 186, 201, 215, 226, 238).
- `Mathlib.Data.ZMod.Basic` — not needed for the elementary
  factorial-tower bound.

This minimal import surface is the regression-resilient property
that motivates the sub-file split.
-/

namespace InfinitudePrimes4k3OQ01

/-- Factorial-based tower: `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`.
    The recursion is primitive-recursive super-exponential and matches
    the parent's factorial witness shape. -/
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 * (tower k + 1).factorial

/-- An explicit increasing sequence of primes ≡ 3 (mod 4) bounded by `tower`. -/
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Classical.choose
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))

theorem primeSeq_3_mod_4_prime : ∀ k, Nat.Prime (primeSeq_3_mod_4 k)
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).1

theorem primeSeq_3_mod_4_mod : ∀ k, primeSeq_3_mod_4 k % 4 = 3
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.2.2

theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  apply strictMono_nat_of_lt_succ
  intro k
  show primeSeq_3_mod_4 k <
    Classical.choose
      (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))
  exact (Classical.choose_spec
    (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.1

theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero =>
    show (3 : ℕ) ≤ 4
    decide
  | succ n ih =>
    show Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (tower n + 1).factorial
    have hub : Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 :=
      (Classical.choose_spec
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))).2.2.1
    have hfact_le : (primeSeq_3_mod_4 n + 1).factorial ≤ (tower n + 1).factorial :=
      Nat.factorial_le (Nat.succ_le_succ ih)
    have _hfact_pos : 1 ≤ (primeSeq_3_mod_4 n + 1).factorial := Nat.factorial_pos _
    calc Classical.choose
            (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 := hub
      _ ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial     := by omega
      _ ≤ 4 * (tower n + 1).factorial                := Nat.mul_le_mul_left 4 hfact_le

/-- Qualitative tower bound: for every `k`, there is a prime ≡ 3 (mod 4)
    bounded by `tower k`. The sequence `primeSeq_3_mod_4` witnesses this
    explicitly. -/
theorem primes_3_mod_4_explicit_tower_bound (k : ℕ) :
    ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ tower k := by
  refine ⟨primeSeq_3_mod_4 k, primeSeq_3_mod_4_prime k, primeSeq_3_mod_4_mod k, ?_⟩
  exact primeSeq_le_tower k

end InfinitudePrimes4k3OQ01

#check @InfinitudePrimes4k3OQ01.tower
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4_prime
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4_mod
#check @InfinitudePrimes4k3OQ01.primeSeq_strict_mono
#check @InfinitudePrimes4k3OQ01.primeSeq_le_tower
#check @InfinitudePrimes4k3OQ01.primes_3_mod_4_explicit_tower_bound
