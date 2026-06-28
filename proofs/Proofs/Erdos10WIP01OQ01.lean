/-
# Erdős #10 — WIP·OQ01: certifying witnesses by a *finite offset* search (no `native_decide`)

**Parent.** `Erdos10WIP01` — the prime-plus-popcount characterization
`isPrimePlusKPowers_iff_popcount`:

> `IsPrimePlusKPowers k n ↔ ∃ p, p.Prime ∧ p ≤ n ∧ popcount (n − p) ≤ k`

**The gap this file closes.** The shipped decidability route
(`decidableIsPrimePlusKPowers`, via `isPrimePlusKPowers_iff_range`) searches over
*every prime candidate* `p ∈ range (n+1)` — `Θ(n)` primality tests. That is why the
concrete witnesses (`906`, Grechuk's `1117175146`) were discharged by `native_decide`:
the kernel cannot run `n+1` primality tests for `n ≈ 10⁹`, and even the compiler
(`native_decide`) cannot iterate a billion-element range. Worse, `native_decide`
trusts the compiler (`Lean.ofReduceBool`), so those facts are *not* axiom-free.

**The fix — search the offset, not the prime.** The *witness* of a representation is
the offset `m = n − p`, and the only offsets that can possibly work are the ones with
`popcount m ≤ k`. There are `Θ((log n)^k)` of those (e.g. ≈ 5000 for `k = 3`,
`n ≈ 10⁹`), not `Θ(n)`. Re-indexing the characterization by `m` gives

> `IsPrimePlusKPowers k n ↔ ∃ m, m ≤ n ∧ popcount m ≤ k ∧ (n − m).Prime`

and, contrapositively, the **refutation criterion**

> `¬ IsPrimePlusKPowers k n ↔ ∀ m ≤ n, popcount m ≤ k → ¬ (n − m).Prime`.

The right-hand side is a *bounded* `∀` over `m ≤ n` whose body is decidable, so it is
checkable by the kernel `decide` (no `native_decide`, hence axiom-free) whenever each
compositeness obligation `¬ (n − m).Prime` is cheap. For tiny witnesses `decide`
closes everything directly; for the genuine `~10⁹` witnesses each `¬ (n − m).Prime` is
discharged by exhibiting a *small proper divisor* (a covering-congruence certificate),
for which `not_prime_of_proper_divisor` below is the kernel-fast tool.

## What is proved here (0 sorries, 0 `axiom`, no `native_decide`)

* `isPrimePlusKPowers_iff_offset` — the offset reformulation.
* `not_isPrimePlusKPowers_iff` — the finite refutation criterion.
* `not_prime_of_proper_divisor` — compositeness from a single small factor.
* `not_isPrimePlusKPowers_one_sixteen` — the smallest concrete witness `16`
  (`16` is not a prime plus `≤ 1` power of two), certified by kernel `decide`
  through the offset criterion. This is the first *axiom-free* (no `native_decide`)
  member of the Erdős #10 witness family.
* `not_isPrimePlusKPowers_one_905` — the smallest *odd* witness `905 = 5·181`,
  also axiom-free. The de Polignac numbers below it are all prime (hence
  representable with zero powers), so `905` is the first odd integer genuinely
  neither prime nor prime-plus-a-power-of-two. Its `~900`-sized complements
  overflow the kernel's default primality `decide`, so compositeness is supplied
  by `norm_num`'s factor-exhibiting extension — a stepping stone between the tiny
  `decide`-closed `16` and the small-divisor certificate path the `~10⁹` witnesses
  need.

The full `1117175146` witness needs its covering-congruence factor table as input data
(≈ 5000 `(offset, small prime divisor)` pairs); assembling that table is left as data
entry — the *proof obligation* it discharges is exactly `not_isPrimePlusKPowers_iff`
fed to `not_prime_of_proper_divisor`, both supplied here.

Tags: number-theory, primes, powers-of-two, binary, popcount, decidability,
native-decide-free, additive-combinatorics, erdos-problem
-/

import Proofs.Erdos10WIP01

namespace Erdos10WIP01

open Erdos10OQ02

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE OFFSET REFORMULATION

`isPrimePlusKPowers_iff_popcount` is indexed by the prime `p`. Substituting the
offset `m = n − p` (a bijection on `{p ≤ n} ↔ {m ≤ n}` via `n − (n − x) = x`)
re-indexes the search by `m`, where the only viable candidates are the finitely
many `m ≤ n` with `popcount m ≤ k`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Offset reformulation.** `n` is a prime plus at most `k` powers of two iff some
offset `m ≤ n` of binary popcount `≤ k` has prime complement `n − m`. Equivalent to
`isPrimePlusKPowers_iff_popcount` under the involution `m = n − p`, but indexed by the
offset, whose viable values are the `Θ((log n)^k)` numbers with `popcount ≤ k` rather
than the `Θ(n)` primes below `n`. -/
theorem isPrimePlusKPowers_iff_offset (k n : ℕ) :
    IsPrimePlusKPowers k n ↔ ∃ m, m ≤ n ∧ popcount m ≤ k ∧ (n - m).Prime := by
  rw [isPrimePlusKPowers_iff_popcount]
  constructor
  · rintro ⟨p, hp, hpn, hpc⟩
    exact ⟨n - p, Nat.sub_le n p, hpc, by rwa [Nat.sub_sub_self hpn]⟩
  · rintro ⟨m, hmn, hmc, hprime⟩
    exact ⟨n - m, hprime, Nat.sub_le n m, by rwa [Nat.sub_sub_self hmn]⟩

/-- **Finite refutation criterion.** `n` is *not* a prime plus at most `k` powers of
two iff every offset `m ≤ n` of popcount `≤ k` has *composite* (non-prime) complement
`n − m`. The right-hand side is a bounded `∀ m ≤ n` with decidable body, so it is
checkable by kernel `decide` — no `native_decide`, hence no `Lean.ofReduceBool`. -/
theorem not_isPrimePlusKPowers_iff (k n : ℕ) :
    ¬ IsPrimePlusKPowers k n ↔ ∀ m, m ≤ n → popcount m ≤ k → ¬ (n - m).Prime := by
  rw [isPrimePlusKPowers_iff_offset]
  push_neg
  rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: COMPOSITENESS FROM A SINGLE SMALL FACTOR

For the genuine `~10⁹` witnesses, each obligation `¬ (n − m).Prime` is discharged
not by trial division (infeasible in the kernel) but by exhibiting one proper
divisor — the small prime from the covering congruence. This is the kernel-fast
certificate tool.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Compositeness certificate.** A number with a proper divisor `1 < d < q` is not
prime. Exhibiting such a `d` (e.g. the covering-congruence prime) certifies
`¬ q.Prime` in the kernel without any trial division. -/
theorem not_prime_of_proper_divisor {d q : ℕ} (hd1 : 1 < d) (hdq : d < q)
    (hdvd : d ∣ q) : ¬ q.Prime := by
  intro hq
  rcases (hq.eq_one_or_self_of_dvd d hdvd) with h | h <;> omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE `k = 1` OFFSET STRUCTURE (KERNEL-FRIENDLY)

The binary popcount `(Nat.bitIndices ·).length` does **not** reduce under kernel
`decide` (only the compiler — `native_decide` — evaluates it, which is precisely
what we are avoiding). So we replace popcount *computation* with the popcount
*structure theorem*: an offset has popcount `≤ 1` iff it is `0` or a single power
of two. This is the `k = 1` instance that the witness below consumes, and it is a
clean reusable fact in its own right.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Popcount `≤ 1` structure.** A number has binary popcount at most one iff it is
`0` (the empty sum) or a single power of two. The viable `k = 1` offsets are exactly
`{0} ∪ {2^a}`. Proved through the binary-expansion identity `twoPowSum_bitIndices`,
so it needs no `decide` on `bitIndices`. -/
theorem popcount_le_one_iff (m : ℕ) :
    popcount m ≤ 1 ↔ m = 0 ∨ ∃ a, m = 2 ^ a := by
  unfold popcount
  have hsum := Nat.twoPowSum_bitIndices m
  constructor
  · intro h
    rcases hl : Nat.bitIndices m with _ | ⟨a, t⟩
    · left
      rw [hl] at hsum
      simpa using hsum.symm
    · right
      rw [hl] at h hsum
      rw [List.length_cons] at h
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      subst ht
      exact ⟨a, by simpa using hsum.symm⟩
  · rintro (rfl | ⟨a, rfl⟩)
    · simp
    · rw [Nat.bitIndices_two_pow]; simp

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE SMALLEST CONCRETE WITNESS, AXIOM-FREE

`16` is the smallest integer that is not a prime plus `≤ 1` power of two. The
viable offsets `m ≤ 16` with `popcount m ≤ 1` are `0, 1, 2, 4, 8, 16`, with
complements `16, 15, 14, 12, 8, 0` — none prime. Feeding the refutation criterion
the popcount-`≤ 1` structure lemma reduces this to five `decide` compositeness
checks on numbers `< 16`, giving the first member of the Erdős #10 witness family
proved with **no `native_decide`** (so no `Lean.ofReduceBool`).
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Smallest witness, axiom-free.** `16` is not a prime plus at most one power of two.
Proved through the offset criterion (no `native_decide`): the popcount-`≤ 1` offsets
are `0` and the powers `2^a ≤ 16` (so `a ≤ 4`), and the complements
`16 − 2^a ∈ {15,14,12,8,0}` (and `16 − 0 = 16`) contain no prime. Contrast the shipped
`906`/`1117175146` facts, which use `native_decide` and so carry `Lean.ofReduceBool`. -/
theorem not_isPrimePlusKPowers_one_sixteen : ¬ IsPrimePlusKPowers 1 16 := by
  rw [not_isPrimePlusKPowers_iff]
  intro m hm hpc
  rw [popcount_le_one_iff] at hpc
  obtain rfl | ⟨a, rfl⟩ := hpc
  · decide                                  -- m = 0:  ¬ Prime 16
  · -- m = 2^a with 2^a ≤ 16, hence a ≤ 4
    have ha : a ≤ 4 := by
      by_contra h
      have h32 : (32 : ℕ) ≤ 2 ^ a := by
        calc (32 : ℕ) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases a <;> decide              -- 16 − 2^a ∈ {15,14,12,8,0}, none prime

/-- **Smallest *odd* witness, axiom-free.** `905 = 5·181` is not a prime plus at most one
power of two. Where `16` is the smallest witness overall (and even), `905` is the smallest
*odd* one: the de Polignac numbers below it — odd integers not of the form `prime + 2^a` —
namely `127, 149, 251, 331, 337, 373, 509, 599, 701, 757, 809, 877`, are *all themselves
prime*, hence representable here with zero powers (`m = 0`). `905 = 5·181` is the first that
is genuinely neither prime nor prime-plus-a-power-of-two, so it is the smallest odd member of
the Erdős #10 witness family. Proved through the same offset criterion with no `native_decide`
(so no `Lean.ofReduceBool`): the popcount-`≤ 1` offsets are `0` and the powers `2^a ≤ 905`
(so `a ≤ 9`), and each complement
`905 − m ∈ {905, 904, 903, 901, 897, 889, 873, 841, 777, 649, 393}` is composite — `norm_num`
exhibits a factor (`5, 2, 3, 17, 3, 7, 3, 29, 3, 11, 3` respectively). Unlike the tiny `16`
case (numbers `< 16`, closed by kernel `decide`), the `~900`-sized complements overflow the
kernel's default primality `decide`, so compositeness here is discharged by `norm_num`'s
factor-exhibiting primality extension — the lightweight analogue of the small-divisor
certificate `not_prime_of_proper_divisor` that the genuine `~10⁹` witnesses require. -/
theorem not_isPrimePlusKPowers_one_905 : ¬ IsPrimePlusKPowers 1 905 := by
  rw [not_isPrimePlusKPowers_iff]
  intro m hm hpc
  rw [popcount_le_one_iff] at hpc
  obtain rfl | ⟨a, rfl⟩ := hpc
  · norm_num                                  -- m = 0:  905 = 5·181, not prime
  · -- m = 2^a with 2^a ≤ 905, hence a ≤ 9
    have ha : a ≤ 9 := by
      by_contra h
      have h1024 : (1024 : ℕ) ≤ 2 ^ a := by
        calc (1024 : ℕ) = 2 ^ 10 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases a <;> norm_num             -- each 905 − 2^a is composite

/-- Sanity check that the offset criterion is the *right* equivalence: `15` *is* a prime
plus one power of two (`15 = 13 + 2`), witnessed by the offset `m = 2`. -/
theorem isPrimePlusKPowers_one_fifteen : IsPrimePlusKPowers 1 15 := by
  rw [isPrimePlusKPowers_iff_offset]
  exact ⟨2, by norm_num, (popcount_le_one_iff 2).mpr (Or.inr ⟨1, by norm_num⟩), by norm_num⟩

#check @isPrimePlusKPowers_iff_offset
#check @not_isPrimePlusKPowers_iff
#check @not_prime_of_proper_divisor
#check @popcount_le_one_iff
#check @not_isPrimePlusKPowers_one_sixteen
#check @not_isPrimePlusKPowers_one_905

end Erdos10WIP01
