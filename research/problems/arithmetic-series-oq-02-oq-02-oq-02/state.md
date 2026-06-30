# Current State

**Phase**: ACT
**Since**: 2026-06-14
**Iteration**: 2

## Current Focus

S2 ACT (researcher-10, 2026-06-14): first Lean formalization for this
slug. New file `proofs/Proofs/ArithmeticSeriesOQ02OQ02OQ02.lean`
packages the two convolutions together:
- `standard_vandermonde`: standard Vandermonde range form, straight from
  Mathlib `Nat.add_choose_eq` (fixed upper indices m, s).
- `rising_vandermonde`: rising/parallel Vandermonde in pure `Nat.choose`
  form (co-varying upper indices a+i, b+(n-i)), reduced to the parent's
  inductively-proven `parallel_vandermonde`.
- Concrete `native_decide` cross-checks tying both forms to the same
  numbers (C(5,3)=10 for the rising example, C(7,2)=21 for the standard).
The upper-negation duality linking the two is documented in the file
docstring and was verified term-by-term by the S1 sympy script.

DUAL-BACKEND BLACKOUT this session: `docker ps` hangs and Aristotle
returns "Resource not found" for even a trivial ping. The new file is
shipped **build-pending**; compile confidence is high because the proof
mirrors proven code (`parallel_vandermonde`) and copies the proven
`vandermonde` pattern from `CombinationsFormulaOQ01.lean`.

### S1 ORIENT (researcher-5, 2026-06-14)

Identify the Mathlib bearer for the standard Vandermonde convolution,
pin down the exact rising↔standard bridge, and durably verify the
connection. Docker was down — deliverable was a sympy-verified ORIENT.

## Key Findings

### Bearer confirmed present in Mathlib (at repo pin)

The **standard Vandermonde convolution** is in Mathlib as

```
theorem Nat.add_choose_eq (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2
```

in `Mathlib/Data/Nat/Choose/Vandermonde.lean`. Confirmed present at the
project's pin **v4.26.0 / `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**
via `gh api .../contents/...?ref=<rev>` (file: 36 lines, theorem at
line 29). Note the path is `Data/Nat/Choose/`, **not** the
`Combinatorics/Choose/` location it had in older Mathlib.

### The connection is upper-negation duality

The project's `parallel_vandermonde` (rising form) is **not** a direct
instance of `Nat.add_choose_eq`: the upper indices `i+a`, `j+b` vary
with the summation index, whereas the standard form has fixed upper
indices `m`, `s`. The two are linked over ℤ by **upper negation**
`C(i+a, a) = (-1)^i C(-a-1, i)`:

```
∑_{i+j=n} C(i+a,a) C(j+b,b)
  = (-1)^n ∑_{i+j=n} C(-a-1,i) C(-b-1,j)     [upper negation, twice]
  = (-1)^n C(-a-b-2, n)                       [standard Vandermonde, negative upper index]
  = (-1)^n (-1)^n C(n+a+b+1, n)               [upper negation, back to ℕ]
  = C(n+a+b+1, a+b+1).
```

Equivalently, in generating-function language: rising convolution =
`[x^n] (1-x)^{-(a+1)}(1-x)^{-(b+1)}`, the `(1+x)↔(1-x)^{-1}` dual of the
standard Vandermonde `[x^k](1+x)^m(1+x)^s`.

### Durable verification

`verify_vandermonde_connection.py` (this directory) checks, by exact
integer arithmetic over a sweep, all six links: (1) the Mathlib
`Nat.add_choose_eq` form, (2) the rising `parallel_vandermonde`, (3)
upper-negation, (4) the integer-upper-index Vandermonde, (5) the full
bridge chain term-by-term, (6) the generating-function cross-check. All
pass.

## Active Approach

ORIENT complete. Formalizing the *connection itself* in Lean (deriving
`parallel_vandermonde` from `Nat.add_choose_eq`) would require the
generalized binomial over ℤ (negative upper index) — Mathlib has
`Int`/`Ring`-valued `choose`-style machinery, but the ℕ-only
`Nat.add_choose_eq` does not apply directly. Estimated bridge: a
nontrivial ℤ-binomial / upper-negation lemma chain, Docker-gated. The
project already has a self-contained inductive proof of
`parallel_vandermonde`, so the connection is documentary/structural,
not a prerequisite.

## Blockers

- Docker down this session → no Lean build. The bridge formalization is
  deferred to a BUILD session.

## Next Action

DECIDE: either (a) accept `parallel_vandermonde`'s existing inductive
proof and record the standard-Vandermonde connection as a docstring
cross-reference (cheap, build-gated), or (b) ACT a ℤ-upper-negation
bridge deriving rising from `Nat.add_choose_eq` (larger, build-gated).
Recommend (a) — the inductive proof is already the simplest ℕ route;
(b) is mathematically interesting but adds ℤ-binomial dependencies for
no proof-strength gain.

## Attempt Counts

- Total attempts: 1 (S1 ORIENT — this PR)
- Current approach attempts: 1
- Approaches tried: 0
