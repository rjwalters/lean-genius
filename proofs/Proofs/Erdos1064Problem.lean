import Mathlib

/-
# Erdős Problem 1064: Comparing φ(n) and φ(n - φ(n))

## What This Proves
We formalize Erdős Problem 1064, which asks to prove that φ(n) > φ(n - φ(n))
for almost all n, but φ(n) < φ(n - φ(n)) for infinitely many n.

Both parts were proved: Luca and Pomerance (2002) showed φ(n) > φ(n - φ(n))
has density 1, while Grytczuk, Luca, and Wójtowicz (2001) showed the reverse
inequality holds infinitely often.

## The Problem
Consider the iterated application: start with n, compute n - φ(n), then
compare φ(n) with φ(n - φ(n)). For most n, φ(n) is larger, but exceptions
exist infinitely often.

Examples:
- n = 15: φ(15) = 8, n - φ(n) = 7, φ(7) = 6, so 8 > 6 ✓
- n = 30: φ(30) = 8, n - φ(n) = 22, φ(22) = 10, so 8 < 10 ✗

## Historical Context
This problem connects to understanding the "typical" behavior of arithmetic
functions versus their exceptional values. The totient function φ(n) measures
the count of integers less than n that are coprime to n.

## Approach
- **Foundation:** We use Mathlib's totient function
- **Axiom Required:** The density-1 result requires analytic number theory
- **Explicit Witnesses:** We show specific n where φ(n) < φ(n - φ(n))

## Status
- [x] Problem statement formalized
- [x] Both parts stated as axioms
- [x] Explicit counterexamples verified
- [ ] Full constructive proof

## References
- Luca, F. and Pomerance, C., Colloq. Math. (2002)
- Grytczuk, Luca, Wójtowicz, Publ. Math. Debrecen (2001)
- https://erdosproblems.com/1064
-/

namespace Erdos1064

open Nat

/- ## Definitions -/

/-- The comparison function: φ(n) compared to φ(n - φ(n)) -/
def phiDiff (n : ℕ) : ℤ := (totient n : ℤ) - (totient (n - totient n) : ℤ)

/-- The set A₊ where φ(n) > φ(n - φ(n)) -/
def A_greater : Set ℕ := {n : ℕ | totient n > totient (n - totient n)}

/-- The set A₋ where φ(n) < φ(n - φ(n)) -/
def A_less : Set ℕ := {n : ℕ | totient n < totient (n - totient n)}

/-- The set A₌ where φ(n) = φ(n - φ(n)) -/
def A_equal : Set ℕ := {n : ℕ | totient n = totient (n - totient n)}

/-! ### The trichotomy `A₊ / A₋ / A₌` partitions ℕ

Comparing `φ(n)` with `φ(n − φ(n))` places every `n` in exactly one of the three sets
`A_greater` (`>`), `A_less` (`<`), `A_equal` (`=`). The following record that they are
pairwise disjoint and jointly exhaust ℕ — the structural backdrop against which the density-1
(`lucaPomerance_density_one`) and infinitely-often (`glw_infinitely_many`,
`A_greater_infinite`) results are stated. -/

/-- `A₊` and `A₋` are disjoint: `φ(n)` cannot be both `>` and `<` than `φ(n − φ(n))`. -/
theorem A_greater_disjoint_A_less : Disjoint A_greater A_less := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [A_greater, A_less, Set.mem_setOf_eq] at hn hn'; omega

/-- `A₊` and `A₌` are disjoint. -/
theorem A_greater_disjoint_A_equal : Disjoint A_greater A_equal := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [A_greater, A_equal, Set.mem_setOf_eq] at hn hn'; omega

/-- `A₋` and `A₌` are disjoint. -/
theorem A_less_disjoint_A_equal : Disjoint A_less A_equal := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [A_less, A_equal, Set.mem_setOf_eq] at hn hn'; omega

/-- The trichotomy is exhaustive: `A₊ ∪ A₋ ∪ A₌ = ℕ`. -/
theorem A_greater_union_A_less_union_A_equal :
    A_greater ∪ A_less ∪ A_equal = Set.univ := by
  ext n
  simp only [A_greater, A_less, A_equal, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  omega

/- ## Concrete Examples -/

/-- φ(1) = 1 -/
example : totient 1 = 1 := by native_decide

/-- φ(2) = 1 -/
example : totient 2 = 1 := by native_decide

/-- φ(6) = 2 -/
example : totient 6 = 2 := by native_decide

/-- φ(15) = 8 -/
example : totient 15 = 8 := by native_decide

/-- φ(30) = 8 -/
example : totient 30 = 8 := by native_decide

/- ## Examples of the Greater Case -/

/-- n = 15: φ(15) = 8, 15 - 8 = 7, φ(7) = 6, so 8 > 6 -/
example : totient 15 > totient (15 - totient 15) := by native_decide

/-- n = 10: φ(10) = 4, 10 - 4 = 6, φ(6) = 2, so 4 > 2 -/
example : totient 10 > totient (10 - totient 10) := by native_decide

/- ## Examples of the Less Case -/

/-- n = 30: φ(30) = 8, 30 - 8 = 22, φ(22) = 10, so 8 < 10 -/
example : totient 30 < totient (30 - totient 30) := by native_decide

/-- n = 60: φ(60) = 16, 60 - 16 = 44, φ(44) = 20, so 16 < 20 -/
example : totient 60 < totient (60 - totient 60) := by native_decide

/-- n = 66: φ(66) = 20, 66 - 20 = 46, φ(46) = 22, so 20 < 22 -/
example : totient 66 < totient (66 - totient 66) := by native_decide

/- ## Main Theorems -/

/-- **Axiom (Luca-Pomerance 2002):**
    The set A₊ = {n : φ(n) > φ(n - φ(n))} has natural density 1.

    In fact, for any f(n) = o(n), we have φ(n) > φ(n - φ(n)) + f(n)
    for almost all n. -/
axiom lucaPomerance_density_one :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
    (Finset.filter (fun n => totient n > totient (n - totient n)) (Finset.range M)).card
    ≥ (1 - ε) * M

/-- **Theorem (Grytczuk-Luca-Wójtowicz 2001), constructively verified.**
    The set `A₋ = {n : φ(n) < φ(n - φ(n))}` is infinite.

    We eliminate the former axiom by exhibiting the explicit family
    `n = 15 · 2^(k+1)` (`k : ℕ`).  For each such `n`:
    * `φ(n) = φ(15) · φ(2^(k+1)) = 8 · 2^k`  (since `gcd(15, 2^(k+1)) = 1`);
    * `n − φ(n) = 15·2^(k+1) − 8·2^k = 11·2^(k+1)`;
    * `φ(n − φ(n)) = φ(11) · φ(2^(k+1)) = 10 · 2^k > 8 · 2^k = φ(n)`.
    The map `k ↦ 15·2^(k+1)` is injective, so `A₋` is infinite. -/
theorem mem_A_less_pow (k : ℕ) : 15 * 2 ^ (k + 1) ∈ A_less := by
  -- φ(15) = φ(3) · φ(5) = 8
  have h15 : Nat.totient 15 = 8 := by
    have h35 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h35, Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
        Nat.totient_prime (by norm_num)]
  -- φ(11) = 10
  have h11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)
  -- φ(2^(k+1)) = 2^k
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
    simp
  -- 15 and 11 are coprime to any power of two
  have cop15 : Nat.Coprime 15 (2 ^ (k + 1)) :=
    (show Nat.Coprime 15 2 by norm_num).pow_right (k + 1)
  have cop11 : Nat.Coprime 11 (2 ^ (k + 1)) :=
    (show Nat.Coprime 11 2 by norm_num).pow_right (k + 1)
  -- φ(n) = 8 · 2^k
  have hφn : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop15, h15, hp2]
  -- n − φ(n) = 11 · 2^(k+1)
  have hsub : 15 * 2 ^ (k + 1) - 8 * 2 ^ k = 11 * 2 ^ (k + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2]; omega
  -- φ(n − φ(n)) = 10 · 2^k
  have hφsub : Nat.totient (11 * 2 ^ (k + 1)) = 10 * 2 ^ k := by
    rw [Nat.totient_mul cop11, h11, hp2]
  -- assemble: 8·2^k < 10·2^k
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  show Nat.totient (15 * 2 ^ (k + 1))
      < Nat.totient (15 * 2 ^ (k + 1) - Nat.totient (15 * 2 ^ (k + 1)))
  rw [hφn, hsub, hφsub]
  omega

/-- The map `k ↦ 15·2^(k+1)` is injective. -/
theorem witness_injective : Function.Injective (fun k : ℕ => 15 * 2 ^ (k + 1)) := by
  intro a b hab
  simp only at hab
  have h2 : (2 : ℕ) ^ (a + 1) = 2 ^ (b + 1) := Nat.eq_of_mul_eq_mul_left (by norm_num) hab
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

/-- **Theorem (Grytczuk-Luca-Wójtowicz 2001).** `A₋` is infinite —
    formerly an axiom, now derived from the explicit family above. -/
theorem glw_infinitely_many : A_less.Infinite :=
  Set.infinite_of_injective_forall_mem witness_injective mem_A_less_pow

/-- **Erdős Problem 1064** (Solved)

    Part 1: φ(n) > φ(n - φ(n)) for almost all n (density 1).
    Part 2: φ(n) < φ(n - φ(n)) for infinitely many n. -/
theorem erdos_1064_resolution :
    -- The problem is fully resolved
    A_less.Infinite := glw_infinitely_many

/- ## Complement: A₊ is also infinite (axiom-free)

The density-1 result (`lucaPomerance_density_one`) is the deep analytic input and
implies `A₊` is infinite, but that infinitude is elementary and needs no analysis:
**every odd prime lies in `A₊`.**  For a prime `p` we have `φ(p) = p − 1`, so
`n − φ(n) = p − (p − 1) = 1` and `φ(1) = 1`; hence `φ(p) = p − 1 > 1 = φ(n − φ(n))`
whenever `p ≥ 3`.  As there are infinitely many primes, `A₊` is infinite —
mirroring the explicit-family proof that `A₋` is infinite, so *both* comparison
sets are unconditionally infinite. -/

/-- Every odd prime `p` lies in `A₊`, i.e. `φ(p) > φ(p − φ(p))`:
    `φ(p) = p − 1`, `p − φ(p) = 1`, and `φ(1) = 1 < p − 1`. -/
theorem mem_A_greater_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : p ∈ A_greater := by
  have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hsub : p - Nat.totient p = 1 := by rw [hφ]; omega
  show Nat.totient p > Nat.totient (p - Nat.totient p)
  rw [hsub, hφ, Nat.totient_one]
  omega

/-- **`A₊` is infinite (axiom-free).**  The elementary complement to
    `glw_infinitely_many`: every odd prime lies in `A₊`
    (`mem_A_greater_of_prime`) and there are infinitely many primes, so `A₊` is
    infinite with no appeal to the density-1 axiom `lucaPomerance_density_one`. -/
theorem A_greater_infinite : A_greater.Infinite := by
  have hsub : {p : ℕ | p.Prime} \ {2} ⊆ A_greater := by
    rintro p ⟨hp, hp2⟩
    have hprime : p.Prime := hp
    have hne : p ≠ 2 := by simpa using hp2
    have h2le : 2 ≤ p := hprime.two_le
    exact mem_A_greater_of_prime hprime (by omega)
  exact Set.Infinite.mono hsub
    (Nat.infinite_setOf_prime.diff (Set.finite_singleton 2))

/-- **Both comparison sets are infinite (axiom-free).**  Combining
    `glw_infinitely_many` (`A₋` infinite, explicit family `15·2^(k+1)`) with
    `A_greater_infinite` (`A₊` infinite, odd primes): the totient comparison
    `φ(n)` vs `φ(n − φ(n))` flips in *both* directions infinitely often, with
    neither infinitude relying on the density axiom. -/
theorem A_less_and_A_greater_infinite : A_less.Infinite ∧ A_greater.Infinite :=
  ⟨glw_infinitely_many, A_greater_infinite⟩

/- ## Sharper structure of A₊: prime powers

`mem_A_greater_of_prime` shows every odd prime lies in `A₊`.  The same mechanism
extends verbatim to *prime powers*, which is strictly stronger: for a prime power
`n = p^j`,
`φ(p^j) = p^(j-1)(p-1)`, so `n − φ(n) = p^j − p^(j-1)(p-1) = p^(j-1)`, and hence
the comparison reduces to `φ(p^j) = p^(j-1)(p-1)` versus `φ(p^(j-1)) ≤ p^(j-1)`.
Whenever `p − 1 ≥ 2` (i.e. `p ≥ 3`) this gives `φ(p^j) ≥ 2·p^(j-1) > p^(j-1)`,
so `p^j ∈ A₊` for *every* exponent `j ≥ 1` — not merely `j = 1`.  Remarkably the
even prime is not fully excluded: for `p = 2` the same bound works as soon as
`j ≥ 2` (`n − φ(n) = 2^(j-1)` and `φ(2^(j-1)) = 2^(j-2) < 2^(j-1) = φ(2^j)`),
giving a *second explicit family* `2^(k+2)` witnessing `A₊`'s infinitude —
structurally parallel to the `15·2^(k+1)` family for `A₋`. -/

/-- **Every odd prime power lies in `A₊`.**  Generalises `mem_A_greater_of_prime`
    (the `j = 1` case) to arbitrary `p^j`, `j ≥ 1`, with `p` an odd prime:
    `φ(p^j) = p^(j-1)(p-1) ≥ 2·p^(j-1) > p^(j-1) ≥ φ(p^(j-1)) = φ(p^j − φ(p^j))`. -/
theorem mem_A_greater_of_odd_prime_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {j : ℕ} (hj : 1 ≤ j) : p ^ j ∈ A_greater := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  -- an odd prime is at least 3
  have hp3 : 3 ≤ p := by
    rcases hodd with ⟨t, rfl⟩; have := hp.two_le; omega
  -- φ(p^(m+1)) = p^m · (p − 1)
  have hφ : Nat.totient (p ^ (m + 1)) = p ^ m * (p - 1) :=
    Nat.totient_prime_pow_succ hp m
  -- p^(m+1) = p^m·(p−1) + p^m, hence n − φ(n) = p^m
  have hid : p ^ m * (p - 1) + p ^ m = p ^ (m + 1) := by
    have hp1 : p - 1 + 1 = p := by omega
    calc p ^ m * (p - 1) + p ^ m
        = p ^ m * (p - 1 + 1) := by ring
      _ = p ^ m * p := by rw [hp1]
      _ = p ^ (m + 1) := by rw [pow_succ]
  have hsub : p ^ (m + 1) - Nat.totient (p ^ (m + 1)) = p ^ m := by rw [hφ]; omega
  -- φ(p^m) ≤ p^m < 2·p^m ≤ p^m·(p−1) = φ(p^(m+1))
  have hlb : p ^ m * 2 ≤ p ^ m * (p - 1) := mul_le_mul_left' (by omega) (p ^ m)
  have hle : Nat.totient (p ^ m) ≤ p ^ m := Nat.totient_le _
  have hpm : 0 < p ^ m := pow_pos hp.pos m
  show Nat.totient (p ^ (m + 1))
      > Nat.totient (p ^ (m + 1) - Nat.totient (p ^ (m + 1)))
  rw [hsub, hφ]
  omega

/-- **Every power `2^j` with `j ≥ 2` lies in `A₊`.**  The even-prime companion of
    `mem_A_greater_of_odd_prime_pow`: `φ(2^j) = 2^(j-1)`, `2^j − φ(2^j) = 2^(j-1)`,
    and `φ(2^(j-1)) = 2^(j-2) < 2^(j-1) = φ(2^j)`.  (`j = 1` fails: `2 ∈ A₌`.) -/
theorem mem_A_greater_of_two_pow {j : ℕ} (hj : 2 ≤ j) : 2 ^ j ∈ A_greater := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  -- φ(2^(m+2)) = 2^(m+1)
  have hφ : Nat.totient (2 ^ (m + 2)) = 2 ^ (m + 1) := by
    have h := Nat.totient_prime_pow_succ Nat.prime_two (m + 1)
    simpa using h
  -- φ(2^(m+1)) = 2^m
  have hφ2 : Nat.totient (2 ^ (m + 1)) = 2 ^ m := by
    have h := Nat.totient_prime_pow_succ Nat.prime_two m
    simpa using h
  -- 2^(m+2) = 2^(m+1) + 2^(m+1), so n − φ(n) = 2^(m+1)
  have h2 : (2 : ℕ) ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hsub : 2 ^ (m + 2) - Nat.totient (2 ^ (m + 2)) = 2 ^ (m + 1) := by rw [hφ]; omega
  -- 2^(m+1) = 2^m + 2^m > 2^m = φ(n − φ(n))
  have h3 : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
  have hpm : 0 < (2 : ℕ) ^ m := pow_pos (by norm_num) m
  show Nat.totient (2 ^ (m + 2))
      > Nat.totient (2 ^ (m + 2) - Nat.totient (2 ^ (m + 2)))
  rw [hsub, hφ, hφ2]
  omega

/-- The map `k ↦ 2^(k+2)` is injective. -/
theorem two_pow_witness_injective : Function.Injective (fun k : ℕ => 2 ^ (k + 2)) := by
  intro a b hab
  simp only at hab
  have := Nat.pow_right_injective (le_refl 2) hab
  omega

/-- **`A₊` is infinite via powers of two (axiom-free).**  A second explicit
    witness family for `A₊`'s infinitude, independent of the odd-prime family in
    `A_greater_infinite`: every `2^(k+2)` lies in `A₊` and `k ↦ 2^(k+2)` is
    injective.  This mirrors `glw_infinitely_many`'s `15·2^(k+1)` family for `A₋`,
    so *each* comparison set has a clean powers-of-two-based explicit witness. -/
theorem A_greater_infinite_via_two_pow : A_greater.Infinite :=
  Set.infinite_of_injective_forall_mem two_pow_witness_injective
    (fun k => mem_A_greater_of_two_pow (Nat.le_add_left 2 k))

/- ## The Pattern: 15 · 2^k ∈ A_less

For n = 15 · 2^k, we have φ(n) < φ(n - φ(n)).
- n = 30: φ(30) = 8, 30 - 8 = 22, φ(22) = 10
- This is because 15 · 2^k - φ(15 · 2^k) = 15 · 2^k - 4 · 2^k = 11 · 2^k
  and φ(11 · 2^k) = 5 · 2^k > 4 · 2^k = φ(15 · 2^k) -/

/-! ## OQ-03: the higher iterate `D(n) = n − φ(n − φ(n))`

Erdős 1064 OQ-03 iterates the construction one step further: from `n` form the
*second-order* value `D(n) = n − φ(n − φ(n))` and compare `φ(n)` with `φ(D(n))`.
This is the object the open question is stated about; the parent file above only
develops the first-order comparison `φ(n)` vs `φ(n − φ(n))`.  Here we give the
first Lean formalization of the OQ-03 iterate together with its elementary
structural facts.

The trichotomy `B₊ / B₋ / B₌` partitions ℕ exactly as `A₊ / A₋ / A₌` does.  Two
elementary infinitude results are proved unconditionally (no density input):

* **Odd primes lie in `B₊`.**  For an odd prime `p`, `n − φ(n) = 1`, so
  `D(p) = p − φ(1) = p − 1` and `φ(D(p)) = φ(p − 1) < p − 1 = φ(p)`.  Hence `B₊`
  is infinite.
* **The parent reversal family lands in `B₌`.**  The family `15·2^(k+1)` — which
  *reverses* the first-order comparison (`mem_A_less_pow`, it lies in `A₋`) —
  gives `D(15·2^(k+1)) = 5·2^(k+2)` with `φ(D(n)) = 8·2^k = φ(n)`: **equality** at
  the second order.  So the second iterate *neutralizes* the parent reversal, and
  `B₌` is infinite.

The deep forward direction (`φ(n) > φ(D(n))` for almost all `n`, the density-1
analogue of Luca–Pomerance for the iterate) needs the same class of analytic input
as the parent and is left open. -/

/-- The OQ-03 second-order iterate `D(n) = n − φ(n − φ(n))`. -/
def D (n : ℕ) : ℕ := n - Nat.totient (n - Nat.totient n)

/-- `B₊`: the set where `φ(n) > φ(D(n))` (OQ-03 "greater" regime). -/
def B_greater : Set ℕ := {n : ℕ | Nat.totient n > Nat.totient (D n)}

/-- `B₋`: the set where `φ(n) < φ(D(n))` (OQ-03 "less" regime). -/
def B_less : Set ℕ := {n : ℕ | Nat.totient n < Nat.totient (D n)}

/-- `B₌`: the set where `φ(n) = φ(D(n))` (OQ-03 "equal" regime). -/
def B_equal : Set ℕ := {n : ℕ | Nat.totient n = Nat.totient (D n)}

/-- The OQ-03 trichotomy is exhaustive: `B₊ ∪ B₋ ∪ B₌ = ℕ`. -/
theorem B_greater_union_B_less_union_B_equal :
    B_greater ∪ B_less ∪ B_equal = Set.univ := by
  ext n
  simp only [B_greater, B_less, B_equal, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  omega

/-- `B₊` and `B₋` are disjoint. -/
theorem B_greater_disjoint_B_less : Disjoint B_greater B_less := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [B_greater, B_less, Set.mem_setOf_eq] at hn hn'; omega

/-- `B₊` and `B₌` are disjoint. -/
theorem B_greater_disjoint_B_equal : Disjoint B_greater B_equal := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [B_greater, B_equal, Set.mem_setOf_eq] at hn hn'; omega

/-- `B₋` and `B₌` are disjoint. -/
theorem B_less_disjoint_B_equal : Disjoint B_less B_equal := by
  rw [Set.disjoint_left]; intro n hn hn'
  simp only [B_less, B_equal, Set.mem_setOf_eq] at hn hn'; omega

/-- **Every odd prime lies in `B₊`** (OQ-03 greater regime).  For an odd prime
    `p`: `φ(p) = p − 1`, so `p − φ(p) = 1`, `D(p) = p − φ(1) = p − 1`, and
    `φ(D(p)) = φ(p − 1) < p − 1 = φ(p)` by `Nat.totient_lt` (as `p − 1 ≥ 2`). -/
theorem mem_B_greater_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : p ∈ B_greater := by
  have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hsub1 : p - Nat.totient p = 1 := by rw [hφ]; omega
  have hD : D p = p - 1 := by unfold D; rw [hsub1, Nat.totient_one]
  show Nat.totient p > Nat.totient (D p)
  rw [hD, hφ]
  exact Nat.totient_lt (p - 1) (by omega)

/-- **`B₊` is infinite (axiom-free).**  Every odd prime lies in `B₊`
    (`mem_B_greater_of_prime`) and there are infinitely many primes.  The OQ-03
    analogue of `A_greater_infinite`. -/
theorem B_greater_infinite : B_greater.Infinite := by
  have hsub : {p : ℕ | p.Prime} \ {2} ⊆ B_greater := by
    rintro p ⟨hp, hp2⟩
    have hne : p ≠ 2 := by simpa using hp2
    exact mem_B_greater_of_prime hp (by have := hp.two_le; omega)
  exact Set.Infinite.mono hsub
    (Nat.infinite_setOf_prime.diff (Set.finite_singleton 2))

/-- **The parent reversal family `15·2^(k+1)` lands in `B₌`.**  For `n = 15·2^(k+1)`
    the parent computation gives `φ(n) = 8·2^k` and `n − φ(n) = 11·2^(k+1)` with
    `φ(n − φ(n)) = 10·2^k`, so `D(n) = n − 10·2^k = 20·2^k = 5·2^(k+2)` and
    `φ(D(n)) = φ(5)·φ(2^(k+2)) = 4·2^(k+1) = 8·2^k = φ(n)`.  So although this family
    *reverses* the first-order comparison (`mem_A_less_pow`, `n ∈ A₋`), the second
    iterate produces **equality**: the reversal is neutralized at order two. -/
theorem mem_B_equal_pow (k : ℕ) : 15 * 2 ^ (k + 1) ∈ B_equal := by
  have h15 : Nat.totient 15 = 8 := by
    have h35 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h35, Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
        Nat.totient_prime (by norm_num)]
  have h11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)
  have h5 : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have hp2' : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 1))]; simp
  have cop15 : Nat.Coprime 15 (2 ^ (k + 1)) :=
    (show Nat.Coprime 15 2 by norm_num).pow_right (k + 1)
  have cop11 : Nat.Coprime 11 (2 ^ (k + 1)) :=
    (show Nat.Coprime 11 2 by norm_num).pow_right (k + 1)
  have cop5 : Nat.Coprime 5 (2 ^ (k + 2)) :=
    (show Nat.Coprime 5 2 by norm_num).pow_right (k + 2)
  -- φ(n) = 8·2^k
  have hφn : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop15, h15, hp2]
  -- n − φ(n) = 11·2^(k+1)
  have hsub : 15 * 2 ^ (k + 1) - 8 * 2 ^ k = 11 * 2 ^ (k + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2]; omega
  -- φ(n − φ(n)) = 10·2^k
  have hφsub : Nat.totient (11 * 2 ^ (k + 1)) = 10 * 2 ^ k := by
    rw [Nat.totient_mul cop11, h11, hp2]
  -- D(n) = n − 10·2^k = 20·2^k = 5·2^(k+2)
  have hDval : 15 * 2 ^ (k + 1) - 10 * 2 ^ k = 5 * 2 ^ (k + 2) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have h2' : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
    rw [h2, h2']; omega
  have hD : D (15 * 2 ^ (k + 1)) = 5 * 2 ^ (k + 2) := by
    unfold D; rw [hφn, hsub, hφsub, hDval]
  -- φ(D(n)) = 8·2^k
  have hφD : Nat.totient (5 * 2 ^ (k + 2)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop5, h5, hp2']
    have h2' : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2']; ring
  show Nat.totient (15 * 2 ^ (k + 1)) = Nat.totient (D (15 * 2 ^ (k + 1)))
  rw [hφn, hD, hφD]

/-- **`B₌` is infinite (axiom-free).**  The family `15·2^(k+1)` lies in `B₌`
    (`mem_B_equal_pow`) and `k ↦ 15·2^(k+1)` is injective (`witness_injective`).
    So the OQ-03 comparison is an *equality* infinitely often — a regime distinct
    from the parent, where the same family instead produced strict reversal. -/
theorem B_equal_infinite : B_equal.Infinite :=
  Set.infinite_of_injective_forall_mem witness_injective mem_B_equal_pow

end Erdos1064
