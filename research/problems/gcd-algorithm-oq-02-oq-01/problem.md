# Problem: Step-Count Upper Bound for Binary GCD (Stein's Algorithm)

**Slug**: gcd-algorithm-oq-02-oq-01
**Created**: 2026-07-01T22:11:20-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let `steps(a, b)` denote the number of recursive calls made by the binary GCD
(Stein's) algorithm on inputs `a, b ∈ ℕ`. We seek a formal logarithmic upper
bound on this count. Concretely:

$$
\operatorname{steps}(a, b) \;\le\; 2\left\lfloor \log_2\big(\max(a, b)\big)\right\rfloor + c
$$

for a small explicit constant `c`. An equivalent, cleaner target uses the
combined bit-length as a potential function: writing
`bits(n) = Nat.size n` (the number of bits in the binary representation), each
iteration strictly decreases `bits(a) + bits(b)`, so

$$
\operatorname{steps}(a, b) \;\le\; \operatorname{bits}(a) + \operatorname{bits}(b) \;=\; \texttt{Nat.size}\,a + \texttt{Nat.size}\,b.
$$

Since `Nat.size n ≤ log₂ n + 1`, the bit-length bound implies the
`2·log₂(max(a,b))` bound up to an additive constant.

### Plain Language

Stein's algorithm computes `gcd(a, b)` on a binary computer using only three
cheap operations: (1) if both `a` and `b` are even, pull out a common factor of
2 and recurse; (2) if exactly one is even, divide that one by 2 (an odd number
shares no factor of 2 with the gcd); (3) if both are odd, subtract the smaller
from the larger — the result is even, so the next step halves it. We want to
prove, in Lean, that the algorithm always halts quickly: the number of steps
grows only logarithmically in the size of the inputs. Intuitively every step
either removes a bit (a halving) or sets up a halving (an odd–odd subtraction),
so the total binary size of the pair keeps shrinking.

### Why This Matters

The Euclidean algorithm needs a general division at each step, which is
expensive for large multi-precision integers. Stein's algorithm replaces
division by bit shifts (halving) and subtraction, both extremely cheap in
hardware — this is why bignum libraries such as GMP use binary-GCD variants.
The correctness of the algorithm is already formalized in this gallery
(`gcd-algorithm-oq-02`), but correctness alone does not certify efficiency. A
formal step-count bound turns the "division-free and fast" folklore claim into a
machine-checked complexity guarantee, and it exercises Lean's tooling for
reasoning about the cost of well-founded recursive functions — a pattern that
recurs across verified algorithm libraries.

## Known Results

### What's Already Proven

- `binaryGcd_eq_gcd` (this gallery, `gcd-algorithm-oq-02`) — the algorithm is
  correct: `binaryGcd a b = Nat.gcd a b`, with termination already established by
  `a + b` strictly decreasing across recursive calls.
- Euclidean-algorithm step counts are governed by Fibonacci numbers (Lamé's
  theorem): the classical worst case for `gcd(a, b)` with `b ≤ a` occurs at
  consecutive Fibonacci numbers, giving `O(log a)` steps. Mathlib provides
  `Nat.fib`, `Nat.gcd`, and the well-founded recursion machinery underlying
  `Nat.gcd`'s own definition.
- Knuth (TAOCP Vol. 2, §4.5.2) — worst-case and average-case analysis of the
  binary GCD algorithm, establishing the `O(log(max(a,b)))` step count.

### What's Still Open

- No formal step-count bound for binary GCD exists in this gallery; the parent
  entry proves correctness and termination but not a quantitative iteration
  bound.
- A tight constant (whether the leading factor is exactly 2, and the precise
  additive constant `c`) has not been pinned down formally.

### Our Goal

Formalize in Lean a logarithmic upper bound on the number of recursive calls of
`binaryGcd`. The primary deliverable is the bit-length bound
`steps(a, b) ≤ Nat.size a + Nat.size b`, proved by well-founded induction on the
potential `a + b` (or directly on `Nat.size a + Nat.size b`). Deriving the
`2·log₂(max(a,b)) + c` corollary from `Nat.size n ≤ Nat.log 2 n + 1` is a
secondary, cleanup goal. We do not attempt the average-case analysis.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| gcd-algorithm-oq-02 | Parent proof; defines `binaryGcd`, proves correctness and `a+b` termination — the object whose step count we bound | Functional induction, coprimality/divisibility lemmas, well-founded recursion |
| gcd-algorithm | Euclidean GCD formalization; Lamé/Fibonacci step-count analysis is the classical analogue of this bound | Euclidean division, well-founded recursion on the remainder |
| bezout-identity | Companion GCD result; both compute `gcd` and share the Euclidean-recursion complexity setting | Extended Euclidean recursion, linear-combination certificate |

## Initial Thoughts

### Potential Approaches

1. **Approach A — well-founded recursion on the `a + b` potential**: Instrument
   the algorithm with an explicit step counter (or define `steps : ℕ → ℕ → ℕ`
   by the same recursion as `binaryGcd`, returning `1 + steps(...)` per call).
   Prove `steps(a, b) ≤ Nat.size a + Nat.size b` by `binaryGcd.induct` /
   well-founded induction on `a + b`, showing each recursive case decreases the
   combined bit-length by at least one and applying the induction hypothesis.
   - Why it might work: `binaryGcd.induct` already generates exactly one case
     per recursive branch, and the `a + b`-decreasing fact is available from the
     parent's termination proof; the halving cases obviously drop a bit, and the
     odd–odd case produces an even number whose subsequent halve drops a bit.
   - Risk: The odd–odd subtract-then-halve branch may reduce the combined
     bit-length by only one across *two* logical operations, so the constant
     needs care; also `Nat.size` arithmetic (`Nat.size (n/2) = Nat.size n - 1`
     for `n > 0`) must be marshaled precisely.

2. **Approach B — direct bit-length induction with `Nat.size`/`Nat.log`**:
   Strengthen the induction to carry `Nat.size a + Nat.size b` as the measure
   from the start, proving a monovariant lemma "each step strictly decreases
   `Nat.size a + Nat.size b`" and then a counting lemma that bounds iterations by
   the initial measure. Convert to the `2·log₂(max(a,b))` form via
   `Nat.size_le` / `Nat.lt_size` and `Nat.size n ≤ Nat.log 2 n + 1`.
   - Why it might work: keeps the whole argument in terms of a single explicit
     monovariant, which is the cleanest form for a complexity statement, and
     reuses Mathlib's `Nat.size`/`Nat.log` API directly.
   - Risk: relating `Nat.size` on `a - b` (odd–odd subtraction) to
     `Nat.size a` is fiddly since subtraction can drop several bits at once —
     good for the bound but requires a careful `≤` rather than exact identity.

### Key Difficulties

- The algorithm interleaves two structurally different reductions (halving vs.
  odd–odd subtraction), so the per-step decrease in the chosen measure is not
  uniform; the induction must handle both while keeping the constant honest.
- The odd–odd case only becomes a bit-dropping step after the *next* halving,
  which complicates a naive "one bit per step" accounting and is the main reason
  the leading constant is 2 rather than 1.
- Need to add or derive an explicit `steps` counter alongside `binaryGcd`
  without disturbing the existing verified correctness proof.

### What Would a Proof Need?

- Key lemma 1: `Nat.size (n / 2) = Nat.size n - 1` for `n ≥ 1` (bit drop on
  halving) and `Nat.size (a - b) ≤ Nat.size a` for `b ≤ a`.
- Key lemma 2: a monovariant `Nat.size a + Nat.size b` (or `a + b`) strictly
  decreases on each recursive call — a quantitative refinement of the parent's
  termination fact.
- Technical requirements: an explicit `steps` function matching the recursion,
  well-founded induction via `binaryGcd.induct`, and `Nat.size`/`Nat.log`
  conversion lemmas to land the final `2·log₂` corollary.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The measure argument is clean: the parent proof already establishes that
  `a + b` strictly decreases, so promoting that to a quantitative bit-length
  bound is a refinement rather than a new idea.
- Similar step-count/monovariant bounds are routinely formalized for
  well-founded recursive functions, and Mathlib supplies the needed `Nat.size`
  and `Nat.log` API plus `binaryGcd.induct`.
- The only real friction is the odd–odd two-phase step and getting the leading
  constant right; this is bookkeeping, not a deep obstruction.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 2–4 days
- If hard: 1 week (if the tight constant proves stubborn, ship the bit-length
  bound and defer the sharp `2·log₂` constant)

## References

### Papers
- Stein, Josef — "Computational problems associated with Racah algebra" (1967) —
  introduced the binary GCD algorithm using only subtraction and halving.
- Knuth, Donald E. — "The Art of Computer Programming, Vol. 2: Seminumerical
  Algorithms," §4.5.2 — worst-case and average-case step-count analysis of
  binary GCD.

### Online Resources
- https://en.wikipedia.org/wiki/Binary_GCD_algorithm — algorithm description,
  complexity discussion, and worst-case step count.

### Mathlib
- `Mathlib.Data.Nat.GCD.Basic` — `Nat.gcd`, `Nat.dvd_gcd`, `Nat.gcd_mul_left`,
  `Nat.coprime_two_left`, the divisibility lemmas underlying the algorithm.
- `Mathlib.Data.Nat.Size` — `Nat.size`, `Nat.size_le`, `Nat.lt_size`, and the
  halving/bit-length identities for the potential-function argument.
- `Mathlib.Data.Nat.Log` — `Nat.log`, `Nat.size`↔`Nat.log 2` relationships for
  converting the bit-length bound to the `2·log₂(max(a,b))` form.
- `Mathlib.Data.Nat.BinaryRec` (`Nat.binaryRec`) — binary recursion principle,
  an alternative structuring tool for bit-length induction.
- Well-founded recursion / functional induction (`binaryGcd.induct`) — supplies
  the induction principle matching each recursive branch of the algorithm.

## Metadata

```yaml
tags:
  - number-theory
  - algorithms
  - gcd
  - binary-arithmetic
related_proofs:
  - gcd-algorithm-oq-02
  - gcd-algorithm
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:20-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
