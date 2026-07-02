# Knowledge Base: prime-gap-bounds-oq-02

Rosser–Schoenfeld bounds on π(n) "from explicit zero-free regions".

---

## Problem Understanding

Rosser–Schoenfeld (1962) proved explicit inequalities for the prime-counting
function, e.g.

```
x / log x  <  π(x)  <  1.25506 · x / log x          (x ≥ 17),
```

with matching explicit bounds on θ(x), ψ(x) and the n-th prime. The sharp
constants come from a numerically verified **zero-free region** for ζ(s) plus an
explicit PNT with error term `ψ(x) = x + O(x·exp(−c√log x))`.

## Feasibility split: upper bound tractable, lower bound blocked

The two directions have very different difficulty in the current library.

### UPPER bound — a genuine 0-axiom result IS available (recommended)

Mathlib (`Mathlib.NumberTheory.Chebyshev`) already proves the explicit Chebyshev
upper bound

```
theta_le_log4_mul_x : θ x ≤ log 4 · x          (θ x = ∑_{p ≤ ⌊x⌋, p prime} log p).
```

From this, the classical elementary argument gives an **explicit upper bound on
π** with no further analytic input, hence 0 axioms:

```
θ(x) ≥ ∑_{√x < p ≤ x} log p ≥ (½ log x) · (π(x) − π(√x)),
```

because every prime `p > √x` has `log p > log √x = ½ log x`. Combined with
`θ(x) ≤ log 4 · x` and the trivial `π(√x) ≤ √x`:

```
π(x)  ≤  √x  +  (2 log 4) · x / log x  =  √x  +  (log 16) · x / log x.
```

This is a Rosser–Schoenfeld-*spirit* explicit bound (explicit constant
`2 log 4 ≈ 2.77` on `x/log x`), weaker than the sharp `1.25506` but **fully
derivable from Mathlib today**. It is also distinct from sibling `oq-01` (which
bounds the *n-th prime* and is axiomatized).

**Formalization cost / obstacle.** Mathlib's own TODO in `Chebyshev.lean` reads:
"*Upstream the results relating `theta` and `psi` to the prime counting function*"
— i.e. there is **no existing `θ ↔ Nat.primeCounting` bridge**. So this proof must
first build that bridge:
- `θ x = ∑_{p ∈ Ioc 0 ⌊x⌋ with Prime} log p` (definitional);
- relate `#{p ∈ Ioc a b with Prime}` to `Nat.primeCounting` via
  `Nat.primesBelow_card_eq_primeCounting'` / `primeCounting_sub_one`;
- subset-sum lower bound over the tail `Ioc ⌊√x⌋ ⌊x⌋` with the `log p ≥ ½ log x`
  termwise estimate.
Estimated ~120–160 lines. This is the substantive, honest contribution for oq-02.

### LOWER bound — blocked

`x/log x < π(x)` needs a Chebyshev **lower** bound `θ(x) ≥ c·x` (or `ψ(x) ≥ c·x`).
Mathlib's TODO also lists "*Prove Chebyshev's lower bound*" — it is **not present**.
Without it, the lower half of Rosser–Schoenfeld cannot be reached at 0 axioms; it
would have to be axiomatized (and the sharp constant needs full PNT + zero-free
region, neither in Mathlib).

## What Mathlib provides (verified 2026-07-02)

- `Chebyshev.theta`, `Chebyshev.psi` with API; `theta_le_log4_mul_x` (upper),
  `psi_le_const_mul_self`, `abs_psi_sub_theta_le_sqrt_mul_log`, `theta_le_psi`.
- `NumberTheory.PrimeCounting`: `monotone_primeCounting`, `tendsto_primeCounting`,
  `add_two_le_nth_prime`, `primeCounting'_add_le` (finite large-sieve upper bound),
  `primesBelow_card_eq_primeCounting'`.
- **Absent**: Chebyshev lower bound, θ/ψ ↔ π bridge, explicit PNT error term,
  numerical zero-free region. (No full PNT asymptotic for π in mainline Mathlib.)

## Relationship to existing family entries

- `prime-gap-bounds` — `pₙ ≤ 2^{n+1}` from Bertrand (**verified**).
- `prime-gap-bounds-oq-01` — Dusart-type n-th-prime bounds, **axiomatized** (3
  axioms) since the full derivation needs explicit PNT error terms. Dusart refines
  Rosser–Schoenfeld's *n-th prime* form, so oq-02 should target the **π(x) form**.
- `prime-gap-bounds-oq-03` — exponential bound meets θ, ψ (**verified**).

## Recommended next step

Prove the **0-axiom explicit upper bound** `π(x) ≤ √x + (log 16)·x/log x` above:
build the θ↔primeCounting bridge (Mathlib TODO), then the tail subset-sum estimate.
Present as `status: verified` for the upper bound; note the lower bound / sharp
constant remain open pending Mathlib's Chebyshev lower bound and explicit PNT.

## Status

PARTIAL / IN-PROGRESS. Upper-bound half is a concrete 0-axiom target (deferred
this iteration — non-trivial θ↔π bridge to build). Lower-bound half and sharp
constants are blocked on missing Mathlib content.
