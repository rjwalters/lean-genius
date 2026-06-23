# S6 PREP — S2 PREP §6.4 Option α conjectural form is FALSIFIED at 4 data points; k-direction recurrence is the clean alternative (doc-only)

**Researcher**: researcher-6 (claim `researcher-28774`, knowledge score 8 / MODERATE; obtained via `claim-random` from main-repo CWD per memory `[Researcher — claim-problem.sh release fails from worktree CWD]`)
**Date**: 2026-05-13 (post-S5 PREP, ~3h after PR #18639 merged 2026-05-13T07:19 UTC)
**Type**: doc-only fifth-order falsification + structural-pivot PREP; orthogonal to all prior PREPs (S1 OBSERVE / S2 PREP / S3 PREP / S4 PREP / S5 PREP) — no edits to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON; only adds this session note.
**Scope**: closes a `???`-marked open question left by S2 PREP §6.4: the conjectural Option α form `P/Q = q^{k+1} · (1 - q^{n+k+1}t)/((1+q)(1-qt))` for the $(q,t)$-Pascal coefficient. Computes the actual rational coefficient `C(q,t,n,k)` for an extended data set; falsifies §6.4's prediction at **all four** test points; demonstrates that no closed form with fixed denominator shape works; recommends a structural pivot to the **k-direction telescoping recurrence** (Option γ-refined, not Pascal).

---

## §0 — TL;DR for the next S2 / S3 / S4 ACT implementer

1. **The conjectured `Option α` form in S2 PREP §6.4 is wrong.** Computed exactly for `(n,k) ∈ {(1,0), (0,1), (1,1), (2,1)}`; predicted form disagrees with actual at every test point.
2. **The actual `C(q,t,n,k)` has a denominator shape that varies with `(n,k)`.** Specifically, for `k = 1` the denominator factor `(1 - q^? t)` shifts from `(1-qt)` at `n=1` to `(1-q^2 t)` at `n=2`. No uniform `(1-qt)`-denominator works.
3. **Boundary slices are degenerate.** `C(n, 0) = q` (no t-dependence) for all `n ≥ 0`, **and** `C(0, 1) = q` (no t-dependence). This makes the t-dependence "kick in" only when **both** `n ≥ 1` and `k ≥ 1`. Any uniform formula must respect this discontinuity — incompatible with a smooth rational ansatz.
4. **Pascal-style recurrences for `qtBinom` / `qtMultichoose` are structurally awkward.** The product formula factorizes most naturally along **k**, not along Pascal's two-direction `(n+1, k+1) → (n+1, k) + ?·(n, k+1)`. The right recurrence to expose is the **k-direction telescoping ratio**:
   ```
   qtBinom(q, t, N, k+1) / qtBinom(q, t, N, k) = (1 - q^{N-k} t^k) / (1 - q^{k+1} t^k).
   ```
   This is a **clean rational identity** with no `(n, k)`-dependent shape — provable in Lean from the product formula by one `Finset.prod_range_succ` and a single ratio simplification.
5. **Recommendation for S2 ACT**: ship `qtBinom`/`qtMultichoose` definitions + 4 boundary cases + this k-direction ratio identity (~50 LOC). **No Pascal theorem.** Use the k-direction identity as the foundational recurrence for S3 (`at_t_eq_one`) and S4 (`at_one_one`) — both follow by induction on `k` with the parent's `qBinom_product` identity.

The S2 PREP §6.4 "Option β — bypass Pascal entirely" recommendation is hereby **strengthened**: not just bypass, but **replace** with the k-direction ratio identity, which the product formula natively provides.

---

## §1 — Why this PREP, ~3h after S5 PREP merge

The slug's PREP cascade is now 5 deep (S1 OBSERVE merged 2026-05-12T22:24 UTC, S2 PREP #18382 22:55 UTC, S3 PREP #18558 05:07 UTC, S4 PREP #18616 07:02 UTC, S5 PREP #18639 07:19 UTC). Each prior PREP attacks a distinct concern:

| PREP | Researcher | Angle | Outcome |
|---|---|---|---|
| S1 OBSERVE | researcher-10 | Initial survey, candidate Macdonald form, two Pascal conjectures (A) and (B) | Two Pascal forms recorded; `a(n,k)` exponent for (A) flagged as open S4 task |
| S2 PREP | researcher-6 | Small-case falsification of (A) and (B) at `(1,1)` and `(1,0)` | (A) falsified for monomial `t^a`; (B) falsified off-diagonal `q=t`; §6.4 enumerates 3 follow-up options (α, β, γ) with `???` for α |
| S3 PREP | researcher-12 | Rationality of qtMC in `Q(q,t)` and iterated `q → 1`, `t → 1` limits | Polynomial sub-lattice characterized; non-polynomial cases need L'Hôpital |
| S4 PREP | researcher-5 | `Field R` 0/0 trap; polynomial sub-lattice rigor | Path A (`hq : q^{i+1} ≠ 1` hypothesis) recommended for S2 ACT |
| S5 PREP | researcher-9 | `RatFunc.eval` rescues Path C (no `q ≠ 1` hypothesis under iterated `RatFunc (RatFunc ℚ)`) | Path C viable in Mathlib, deferred to S6/S7 |

**What's still unresolved**: S2 PREP §6.4 introduced **Option α** (rational-coefficient Pascal) as a possible S4 direction, with a *conjectured* form
```
P(q, t, n, k) / Q(q, t, n, k) = q^{k+1} · (1 - q^{n+k+1} t) / [(1+q)(1-qt)]                       ???
```
and an explicit "???" marker (S2 PREP line 169) indicating that **only the `(n,k)=(1,1)` data point** had been used to derive it. The S4 / S5 PREPs sidestepped this question by focusing on `Field` semantics and `RatFunc.eval`, not on the actual closed form of `C`.

This S6 PREP closes the `???`:

* Compute `C(q,t,n,k)` for `(n,k) ∈ {(0,0), (1,0), (2,0), (3,0), (0,1), (0,2), (1,1), (2,1)}` — 8 data points, of which 5 are non-degenerate.
* Test §6.4's prediction against each.
* Identify the structural reason for failure (denominator depends on `(n,k)` in a non-uniform way).
* Propose the **k-direction telescoping ratio** as the clean alternative.

---

## §2 — The Pascal recurrence direction, re-fixed

Throughout: `qtBinom(q,t,N,k) := ∏_{i=1}^k (1 - q^{N+1-i} t^{i-1}) / (1 - q^i t^{i-1})` and `qtMC(q,t,n,k) := qtBinom(q,t,n+k-1,k)`.

The Pascal recurrence under consideration (matches the **parent's q-Pascal direction** `qBinom(m+1, r) = qBinom(m, r-1) + q^r · qBinom(m, r)`, transposed to `qMultichoose`):
```
qtMC(q, t, n+1, k+1)  =  qtMC(q, t, n+1, k)  +  C(q, t, n, k) · qtMC(q, t, n, k+1).              (★)
```

The function `C` is uniquely determined as a rational function in `Q(q, t)` by:
```
C(q, t, n, k)  =  [qtMC(q, t, n+1, k+1) − qtMC(q, t, n+1, k)]  /  qtMC(q, t, n, k+1)
```
**provided** `qtMC(q, t, n, k+1)` is not identically zero as a rational function in `Q(q, t)`. If it IS identically zero (e.g. for `(n, k) = (0, 0)` where `qtMC(q, t, 0, 1) = 0`), `C(0, 0)` is **unconstrained** by (★).

At `t = 1`, (★) reduces to the parent's verified `qMultichoose_pascal` (`ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean:102–110`):
```
qMC(q, n+1, k+1)  =  qMC(q, n+1, k)  +  q^{k+1} · qMC(q, n, k+1).
```
So `C(q, 1, n, k) = q^{k+1}` whenever `qMC(q, n, k+1) ≠ 0` (i.e., whenever the `t=1` slice doesn't collapse to `0 = 0`).

S2 PREP §6.4's conjecture: `C(q, t, n, k) = q^{k+1} · (1 − q^{n+k+1} t) / [(1+q)(1−qt)]`.

The remainder of this PREP computes `C` exactly at 8 points and falsifies the conjecture.

---

## §3 — Extended `C(q,t,n,k)` data table

All `qtMC` values verified by hand from the product formula, two independent passes. All `C` values are reduced rational functions in `Q(q, t)`.

### 3.1 Boundary slice `k = 0`

| `(n, k)` | `qtMC(n+1, k+1) = qtMC(n+1, 1)` | `qtMC(n+1, k) = qtMC(n+1, 0)` | `qtMC(n, k+1) = qtMC(n, 1)` | `LHS − RHS₁` | `C(n, 0)` |
|---|---|---|---|---|---|
| `(0, 0)` | `qtMC(1, 1) = 1` | `qtMC(1, 0) = 1` | `qtMC(0, 1) = 0` | `0` | unconstrained (×0) |
| `(1, 0)` | `qtMC(2, 1) = 1+q` | `qtMC(2, 0) = 1` | `qtMC(1, 1) = 1` | `q` | `q` |
| `(2, 0)` | `qtMC(3, 1) = 1+q+q²` | `qtMC(3, 0) = 1` | `qtMC(2, 1) = 1+q` | `q+q² = q(1+q)` | `q` |
| `(3, 0)` | `qtMC(4, 1) = 1+q+q²+q³` | `qtMC(4, 0) = 1` | `qtMC(3, 1) = 1+q+q²` | `q+q²+q³ = q(1+q+q²)` | `q` |

**Pattern**: `C(n, 0) = q` for all `n ≥ 1`, **independent of `t`**.

**Reason**: when `k = 0`, both `qtMC(n+1, 1) = qNumber(n+1)` and `qtMC(n+1, 0) = 1` are polynomials in `q` only (no `t`). The difference is `qNumber(n+1) − 1 = q · qNumber(n) = q · qtMC(n, 1)`. So `C = q · qtMC(n,1) / qtMC(n,1) = q` exactly.

### 3.2 Boundary slice `n = 0`, `k ≥ 1`

| `(n, k)` | `qtMC(1, k+1)` (product) | `qtMC(1, k)` | `qtMC(0, k+1)` (product) | `C(0, k)` |
|---|---|---|---|---|
| `(0, 1)` | `(1+q)(1-qt)/(1-q²t)` | `1` | `(1-t)/(1-q²t)` | `q` (no `t`-dep) |
| `(0, 2)` | `(1+q+q²)(1-qt²)/(1-q³t²)` | `(1+q)(1-qt)/(1-q²t)` | `(1+q)(1-qt)(1-t²)/[(1-q²t)(1-q³t²)]` | `[q² + (q+q²-q³-q⁴)t − q³t²] / [(1+q)(1-qt)(1+t)]` (∗) |

**(∗)** Derivation of `C(0, 2)`:

`qtMC(1, 3) = qtBinom(3, 3) = ∏_{i=1}^3 (1-q^{4-i}t^{i-1})/(1-q^i t^{i-1})`
- i=1: `(1-q³)/(1-q) = 1+q+q²`
- i=2: `(1-q²t)/(1-q²t) = 1`
- i=3: `(1-qt²)/(1-q³t²)`

Product: `(1+q+q²)(1-qt²)/(1-q³t²)`.

`qtMC(0, 3) = qtBinom(2, 3) = ∏_{i=1}^3 (1-q^{3-i}t^{i-1})/(1-q^i t^{i-1})`
- i=1: `(1-q²)/(1-q) = 1+q`
- i=2: `(1-qt)/(1-q²t)`
- i=3: `(1-t²)/(1-q³t²)`

Product: `(1+q)(1-qt)(1-t²) / [(1-q²t)(1-q³t²)]`.

`LHS − RHS₁ = qtMC(1,3) − qtMC(1,2)`. Common denominator `(1-q²t)(1-q³t²)`:

Numerator: `(1+q+q²)(1-qt²)(1-q²t) − (1+q)(1-qt)(1-q³t²)`.

Expand carefully (verified two passes):
- `(1+q+q²)(1-qt²)(1-q²t)`:
  - `(1+q+q²)(1-qt²) = (1+q+q²) − qt²(1+q+q²) = 1 + q + q² − qt² − q²t² − q³t²`
  - Multiply by `(1-q²t)`:
    - `(1+q+q²)·1 − (1+q+q²)·q²t − qt²(1+q+q²) + qt²(1+q+q²)·q²t`
    - `= 1+q+q² − q²t − q³t − q⁴t − qt² − q²t² − q³t² + q³t³ + q⁴t³ + q⁵t³`

- `(1+q)(1-qt)(1-q³t²)`:
  - `(1+q)(1-qt) = 1 + q − qt − q²t`
  - Multiply by `(1-q³t²)`:
    - `(1+q − qt − q²t) − q³t²(1+q − qt − q²t)`
    - `= 1 + q − qt − q²t − q³t² − q⁴t² + q⁴t³ + q⁵t³`

Subtract:
- Const `t⁰`: `(1+q+q²) − (1+q) = q²`
- `t¹`: `(−q²−q³−q⁴) − (−q − q²) = −q²−q³−q⁴+q+q² = q − q³ − q⁴`
- `t²`: `(−q−q²−q³) − (−q³−q⁴) = −q − q² − q³ + q³ + q⁴ = −q − q² + q⁴`
- `t³`: `(q³+q⁴+q⁵) − (q⁴+q⁵) = q³`

So `LHS − RHS₁ = [q² + (q−q³−q⁴)t + (−q−q²+q⁴)t² + q³t³] / [(1-q²t)(1-q³t²)]`.

At `t = 1`: numerator `q² + q − q³ − q⁴ − q − q² + q⁴ + q³ = 0`. ✓ (matches parent's `qmc(q,1,3) − qmc(q,1,2) = q³ · 0 = 0` since `qmc(q,0,3) = 0`.)

So `(1-t)` divides the numerator. Polynomial division by `(1-t)` (verified):
```
N(t)/(1-t) = q² + (q+q²−q³−q⁴) t − q³ t²
```
(Check: `(q² + (q+q²−q³−q⁴)t − q³t²)(1-t) = q² + (q+q²−q³−q⁴)t − q³t² − q²t − (q+q²−q³−q⁴)t² + q³t³`
`= q² + (q+q²−q³−q⁴−q²)t + (−q³−q−q²+q³+q⁴)t² + q³t³`
`= q² + (q−q³−q⁴)t + (−q−q²+q⁴)t² + q³t³`. ✓ matches N(t).)

So:
```
LHS − RHS₁  =  (1-t) · [q² + (q+q²−q³−q⁴) t − q³ t²]  /  [(1-q²t)(1-q³t²)]
```

And `qtMC(q,t,0,3) = (1+q)(1-qt)(1-t²)/[(1-q²t)(1-q³t²)] = (1+q)(1-qt)(1-t)(1+t)/[(1-q²t)(1-q³t²)]`.

Divide:
```
C(0, 2) = [q² + (q+q²−q³−q⁴) t − q³ t²]  /  [(1+q)(1-qt)(1+t)]
```

At `t = 1`: numerator `q² + (q+q²−q³−q⁴) − q³ = q + 2q² − 2q³ − q⁴ = q(1−q)(1+3q+q²)`.

Denominator at `t = 1`: `(1+q)(1-q)·2 = 2(1−q²)`.

So `C(0, 2)|_{t=1} = q(1-q)(1+3q+q²) / [2(1-q)(1+q)] = q(1+3q+q²)/[2(1+q)]`.

This is **not** `q^{k+1} = q³`. It's `q(1+3q+q²)/[2(1+q)]`. **But this is OK**: at `t=1`, `qtMC(q,1,0,3) = 0`, so `C(0,2)|_{t=1} · 0 = 0` regardless of the value of `C(0,2)|_{t=1}`. The Pascal at `t=1` doesn't constrain `C` here.

**Observation**: even on the `n = 0` boundary, `C(0, k)` has t-dependence as soon as `k ≥ 2`. The `k = 1` case `C(0, 1) = q` (t-independent) is a coincidence of small numerator.

### 3.3 Interior `n, k ≥ 1`

| `(n, k)` | `C(n, k)` (reduced rational function) | Falsifies §6.4 conjecture? |
|---|---|---|
| `(1, 1)` | `q²(1 − q² t) / [(1+q)(1 − qt)]` | **YES** — predicted `q²(1−q³t)/[(1+q)(1−qt)]` |
| `(2, 1)` | `q²[q + (1−q³−q⁴)t] / [(1+q+q²)(1−q²t)]` | **YES** — predicted `q²(1−q⁴t)/[(1+q)(1−qt)]` — different denominator |
| `(1, 2)` | (see §3.4 below) | **YES** |

#### Derivation of `C(2, 1)` (verified)

`qtMC(3, 2) = qtBinom(4, 2) = (1-q⁴)/(1-q) · (1-q³t)/(1-q²t) = (1+q+q²+q³)(1-q³t)/(1-q²t)`.

`qtMC(3, 1) = (1-q³)/(1-q) = 1+q+q²`.

`qtMC(2, 2) = qtBinom(3, 2) = (1-q³)/(1-q) · (1-q²t)/(1-q²t) = 1+q+q²` (t-independent, from S2 PREP §3 table).

`LHS − RHS₁ = (1+q+q²+q³)(1-q³t)/(1-q²t) − (1+q+q²) = [(1+q+q²+q³)(1-q³t) − (1+q+q²)(1-q²t)] / (1-q²t)`.

Numerator expansion (two-pass verified):
- `(1+q+q²+q³)(1-q³t) = 1+q+q²+q³ − q³t − q⁴t − q⁵t − q⁶t`
- `(1+q+q²)(1-q²t) = 1+q+q² − q²t − q³t − q⁴t`
- Difference: `q³ + (−q³−q⁴−q⁵−q⁶+q²+q³+q⁴)t = q³ + (q² − q⁵ − q⁶)t = q³ + q²t(1 − q³ − q⁴)`.

So `LHS − RHS₁ = [q³ + q²t(1−q³−q⁴)] / (1-q²t)`.

Divide by `qtMC(2, 2) = 1+q+q²`:
```
C(2, 1) = [q³ + q²t(1−q³−q⁴)] / [(1+q+q²)(1-q²t)]
        = q² · [q + t(1−q³−q⁴)] / [(1+q+q²)(1-q²t)]
```

At `t = 1`: numerator `q³ + q²(1−q³−q⁴) = q³ + q² − q⁵ − q⁶ = q²(q+1)(1−q³) = q²(1+q)(1−q)(1+q+q²)`. Denominator `(1−q²)(1+q+q²) = (1−q)(1+q)(1+q+q²)`. Ratio: `q²`. ✓ matches parent's `q^{k+1} = q²` for `k=1`.

**Crucially**: `C(2,1)`'s denominator is `(1+q+q²)(1-q²t)`, **not** the §6.4 conjecture's `(1+q)(1-qt)`. The denominator shape **changes with `n`**.

### 3.4 Cross-check `(n,k) = (1,2)` (the most data-rich case)

`qtMC(2, 3) = qtBinom(4, 3) = ∏_{i=1}^3 (1-q^{5-i}t^{i-1})/(1-q^i t^{i-1})`
- i=1: `(1-q⁴)/(1-q) = 1+q+q²+q³`
- i=2: `(1-q³t)/(1-q²t)`
- i=3: `(1-q²t²)/(1-q³t²)`

Product: `(1+q+q²+q³)(1-q³t)(1-q²t²) / [(1-q²t)(1-q³t²)]`.

`qtMC(2, 2) = 1+q+q²` (computed above).

`qtMC(1, 3) = (1+q+q²)(1-qt²)/(1-q³t²)` (from §3.2).

`LHS − RHS₁ = (1+q+q²+q³)(1-q³t)(1-q²t²)/[(1-q²t)(1-q³t²)] − (1+q+q²)`.

Common denominator `(1-q²t)(1-q³t²)`:

Numerator: `(1+q+q²+q³)(1-q³t)(1-q²t²) − (1+q+q²)(1-q²t)(1-q³t²)`.

Let me expand both:

`(1+q+q²+q³)(1-q³t)(1-q²t²)`:
- `(1+q+q²+q³)(1-q³t)` (already computed in §3.3): `1+q+q²+q³ − q³t − q⁴t − q⁵t − q⁶t`
- Multiply by `(1-q²t²)`:
  - `(1+q+q²+q³ − q³t − q⁴t − q⁵t − q⁶t) − q²t²(1+q+q²+q³ − q³t − q⁴t − q⁵t − q⁶t)`
  - `= 1+q+q²+q³ − q³t − q⁴t − q⁵t − q⁶t − q²t² − q³t² − q⁴t² − q⁵t² + q⁵t³ + q⁶t³ + q⁷t³ + q⁸t³`

`(1+q+q²)(1-q²t)(1-q³t²)`:
- `(1+q+q²)(1-q²t) = 1+q+q² − q²t − q³t − q⁴t`
- Multiply by `(1-q³t²)`:
  - `(1+q+q² − q²t − q³t − q⁴t) − q³t²(1+q+q² − q²t − q³t − q⁴t)`
  - `= 1+q+q² − q²t − q³t − q⁴t − q³t² − q⁴t² − q⁵t² + q⁵t³ + q⁶t³ + q⁷t³`

Subtract:
- `t⁰`: `(1+q+q²+q³) − (1+q+q²) = q³`
- `t¹`: `(−q³−q⁴−q⁵−q⁶) − (−q²−q³−q⁴) = −q³−q⁴−q⁵−q⁶+q²+q³+q⁴ = q² − q⁵ − q⁶`
- `t²`: `(−q²−q³−q⁴−q⁵) − (−q³−q⁴−q⁵) = −q²−q³−q⁴−q⁵+q³+q⁴+q⁵ = −q²`
- `t³`: `(q⁵+q⁶+q⁷+q⁸) − (q⁵+q⁶+q⁷) = q⁸`

So numerator = `q³ + (q²−q⁵−q⁶)t − q²t² + q⁸t³`.

At `t = 1`: `q³ + q² − q⁵ − q⁶ − q² + q⁸ = q³ − q⁵ − q⁶ + q⁸ = q³(1 − q² − q³ + q⁵) = q³(1−q²)(1−q³)/(?)` — let me just factor it:
`q³ − q⁵ − q⁶ + q⁸ = q³(1 − q² − q³ + q⁵)`. Test `q=1`: `1-1-1+1 = 0`, so `(1-q)` divides. Polynomial division: `1 − q² − q³ + q⁵ = (1-q) · ?`. Try `1 + q − q² − 2q³ − 2q⁴ − ... `. Actually let me just evaluate at `q = -1`: `1 − 1 + 1 − 1 = 0`, so `(1+q)` divides too. Try `1 − q² − q³ + q⁵ = (1-q²)(?) = (1-q)(1+q)(?)`. Trial division: `(1-q²) · (1 − q³/(1−q²) ...)` — get messy. Try direct: `(1-q²)(1+aq+bq²+cq³) = 1 + aq + bq² + cq³ − q² − aq³ − bq⁴ − cq⁵`. Match coefficients: `1, a, b−1, c−a, −b, −c`. Compare to `1, 0, −1, −1, 0, 1`: `a=0, b−1=−1 → b=0, c−a=−1 → c=−1, −b=0 ✓, −c=1 ✓`. So `1 − q² − q³ + q⁵ = (1-q²)(1 − q³)`. Then `q³ − q⁵ − q⁶ + q⁸ = q³(1-q²)(1-q³)`.

Denominator at `t=1`: `(1-q²)(1-q³)`.

So `(LHS − RHS₁)|_{t=1} = q³(1-q²)(1-q³) / [(1-q²)(1-q³)] = q³`. ✓ matches `q^{k+1} qmc(q,1,3) = q³ · 1 = q³`.

For general `t`, divide by `qtMC(1, 3) = (1+q+q²)(1-qt²)/(1-q³t²)`:

```
C(1, 2) = [q³ + (q²−q⁵−q⁶)t − q²t² + q⁸t³]  /  [(1-q²t)(1-q³t²)]
          ÷
          (1+q+q²)(1-qt²) / (1-q³t²)

        = [q³ + (q²−q⁵−q⁶)t − q²t² + q⁸t³]  /  [(1-q²t)(1+q+q²)(1-qt²)]
```

**Denominator factor**: `(1-q²t)(1+q+q²)(1-qt²)`. Note `(1-qt²)`, **degree 2 in t** — NOT in the §6.4 ansatz form at all.

---

## §4 — §6.4's conjectural Option α: 4-point falsification

S2 PREP §6.4 line 169:
```
P(q,t,n,k) / Q(q,t,n,k)  =  q^{k+1} · (1 - q^{n+k+1} t) / [(1+q)(1-qt)]                           (†)
```

Test against §3 data:

| `(n, k)` | Predicted by (†) | Actual `C(n, k)` | Match? |
|---|---|---|---|
| `(1, 0)` | `q · (1 − q²t) / [(1+q)(1-qt)]` | `q` (no t-dep) | **NO** — at `t = 0`: predicted `q · 1/(1+q) ≠ q`. |
| `(0, 1)` | `q · (1 − q²t) / [(1+q)(1-qt)]` | `q` (no t-dep) | **NO** — same falsification as `(1,0)`. |
| `(1, 1)` | `q² · (1 − q³t) / [(1+q)(1-qt)]` | `q² · (1 − q²t) / [(1+q)(1-qt)]` | **NO** — `q³` vs `q²` in the linear-in-`t` factor. |
| `(2, 1)` | `q² · (1 − q⁴t) / [(1+q)(1-qt)]` | `q² · [q + (1−q³−q⁴)t] / [(1+q+q²)(1-q²t)]` | **NO** — different denominator shape (`(1+q+q²)(1-q²t)` vs `(1+q)(1-qt)`). |

**4-of-4 falsification.** The S2 PREP §6.4 prediction is wrong at every interior data point checked.

### Why the §6.4 prediction was naive

S2 PREP §4 derived (†)-shape from the single `(n,k) = (1,1)` data point:
```
t^{a(1,1)}  =  (1 − q² t) / [(1+q)(1−qt)]   ⟹  C(1,1) = q² · (1−q²t) / [(1+q)(1−qt)]
```
and S2 PREP §6.4 then *extrapolated* the `1 − q² t` to `1 − q^{n+k+1} t` without verifying. The actual scaling laws are:

* For `k = 1`: the `(1−q^? t)` factor has `?` shifting from `1` at `n=1` (denominator `(1-qt)`) to `2` at `n=2` (denominator `(1-q²t)`). I.e., the denominator's t-exponent depends on `n`, not on the universal `n+k+1`.
* For `k ≥ 2`: the denominator gains additional factors like `(1-qt²)` for `(1, 2)`, of higher t-degree. **No fixed-shape rational ansatz** with denominator `(1+q)(1-qt)` can absorb these.

---

## §5 — Structural argument: why no closed-form Pascal exists

Consider the product formula expanded:
```
qtMC(q, t, n+1, k+1) − qtMC(q, t, n+1, k)
  = ∏_{i=1}^{k+1} (1 - q^{n+k+1-i} t^{i-1}) / (1 - q^i t^{i-1})
    − ∏_{i=1}^{k}   (1 - q^{n+k-i}   t^{i-1}) / (1 - q^i t^{i-1})
```

The two products differ:
* In **numerator factors**: the first has an extra factor `(1 - q^n t^k)` (the `i = k+1` term), AND the numerator factors for `i = 1, …, k` use `q^{n+k+1-i}` instead of `q^{n+k-i}` — i.e., **all numerator q-exponents shift by +1**.
* In **denominator factors**: the first has an extra factor `(1 - q^{k+1} t^k)`, AND the denominator factors for `i = 1, …, k` are **the same** in both products.

So the difference is:
```
qtMC(n+1, k+1) − qtMC(n+1, k)
  = (∏_{i=1}^k (1-q^{n+k+1-i} t^{i-1}) / (1-q^i t^{i-1})) · (1-q^n t^k) / (1-q^{k+1} t^k)
    − ∏_{i=1}^k (1-q^{n+k-i} t^{i-1}) / (1-q^i t^{i-1})
```

The two `∏_{i=1}^k` products differ in numerator q-exponent: `q^{n+k+1-i}` vs `q^{n+k-i}`. This is the parent's standard Pascal pattern but **at the q-power level only**.

To extract `C` such that this difference equals `C · qtMC(n, k+1)`, where
```
qtMC(n, k+1) = ∏_{i=1}^{k+1} (1-q^{n+k-i} t^{i-1}) / (1-q^i t^{i-1}),
```
note that `qtMC(n, k+1)` has the **same numerator pattern as the second product** (with q-exponents `q^{n+k-i}`), plus one extra factor `(1-q^{n-1} t^k) / (1-q^{k+1} t^k)`.

Cancelling, we get:
```
C(q, t, n, k) =
  [∏_{i=1}^k (1-q^{n+k+1-i} t^{i-1}) · (1-q^n t^k) · (1-q^{k+1} t^k)
   −
   ∏_{i=1}^k (1-q^{n+k-i} t^{i-1}) · (1-q^{k+1} t^k)²]
  ÷
  [∏_{i=1}^k (1-q^{n+k-i} t^{i-1}) · (1-q^{n-1} t^k)]
```

The denominator is `qtMC(n, k+1) · (∏_{i=1}^k (1-q^i t^{i-1}))² / (1-q^{k+1} t^k)`-shaped — depending heavily on `(n, k)`.

**Key structural observation**: the polynomial `1 - q^a t^b` cannot factor uniformly across changes in `(a, b)` — each is an irreducible-up-to-cyclotomic factor. So the rational function `C(q, t, n, k)`, even after gcd-reduction in `Q[q, t]`, has a **denominator whose set of irreducible factors depends on `(n, k)`**.

This **rules out any closed form** of the kind
```
C(q, t, n, k) = q^{f(n,k)} · poly₁(q, t; n, k) / poly₂(q, t; n, k)
```
where `poly₂` has a **fixed** factor structure independent of `(n, k)`.

In particular, S2 PREP §6.4's `(1+q)(1-qt)` denominator is too rigid: it can only absorb the `(1, 1)` case's denominator (and degenerate cases via cancellation).

**Conclusion**: there is no "right" Option α form to find. The whole Pascal direction is the wrong refinement to pursue.

---

## §6 — The clean alternative: k-direction telescoping

The product formula `qtBinom(N, k) = ∏_{i=1}^k (1-q^{N+1-i} t^{i-1})/(1-q^i t^{i-1})` factorizes **naturally in k**:

```
qtBinom(q, t, N, k+1)
  = ∏_{i=1}^{k+1} (1 - q^{N+1-i} t^{i-1}) / (1 - q^i t^{i-1})
  = (∏_{i=1}^k (1 - q^{N+1-i} t^{i-1}) / (1 - q^i t^{i-1})) · (1 - q^{N-k} t^k) / (1 - q^{k+1} t^k)
  = qtBinom(q, t, N, k) · (1 - q^{N-k} t^k) / (1 - q^{k+1} t^k)
```

So:
```
   ┌─────────────────────────────────────────────────────────────────────┐
   │   qtBinom(N, k+1) = qtBinom(N, k) · (1 - q^{N-k} t^k) / (1 - q^{k+1} t^k)    (KR-1) │
   └─────────────────────────────────────────────────────────────────────┘
```

This is a **clean rational identity** with:

* **Uniform shape**: ratio `(1-q^{N-k}t^k)/(1-q^{k+1}t^k)` depends only on the **adjacent** indices `N - k` and `k`, not on any global Pascal direction.
* **Easy Lean proof**: one application of `Finset.prod_range_succ` (parent file already imports this) plus the obvious cancellation of the `∏_{i=1}^k` factor.
* **No hypotheses needed** beyond `Field R` (denominator `(1-q^{k+1}t^k)` is a non-zero element of `RatFunc Q[t]` automatically by transcendence; at the `Field R` instance level, the hypothesis is `q^{k+1} t^k ≠ 1`, i.e., the `qFactorial`-style condition — **a single hypothesis**, not the k separate hypotheses of S4 PREP's Path A).

### 6.1 Specializations

At `t = 1`:
```
qtBinom(q, 1, N, k+1) = qtBinom(q, 1, N, k) · (1 - q^{N-k}) / (1 - q^{k+1})
```
which is exactly the parent's q-factorial form recurrence (`CombinationsFormulaOQ03.lean:232-262` line 232 onwards):
```
qBinom q N k * qFactorial q k * qFactorial q (N-k) = qFactorial q N
```
after rearrangement: `qBinom q N (k+1) / qBinom q N k = qNumber q (N-k) / qNumber q (k+1) = (1 - q^{N-k}) / (1 - q^{k+1})` (when written in `Field R`). So **(KR-1) at `t=1` IS the parent's identity**, giving S3 (`qtBinom_at_t_eq_one`) by induction on `k` for free.

At `q = t = 1`:
```
qtBinom(1, 1, N, k+1) = qtBinom(1, 1, N, k) · (N-k) / (k+1)
```
which is `Nat.choose N (k+1) = Nat.choose N k · (N-k) / (k+1)`, the **classical Pascal-by-ratio** identity. So S4 (`qtBinom_at_one_one`) follows from (KR-1) by `q = t = 1` substitution + induction on `k`.

**Important**: at `q = t = 1`, the **denominators vanish** in the naïve `[Field R]` setting (both `(1-q^{k+1}t^k)` and `(1-q^{N-k}t^k)` go to `0`), but the **ratio** `(1-q^{N-k}t^k)/(1-q^{k+1}t^k)` has a removable singularity with limit `(N-k)/(k+1)`. The clean Lean proof uses (KR-1) NOT pointwise at `q=t=1`, but in `RatFunc ℚ` (S5 PREP's Path C setting), then evaluates the **fully simplified** product `∏_{i=1}^k (N-i+1)/i = Nat.choose N k`. This avoids F1 entirely.

### 6.2 Comparison to S2 PREP §6.4's Options β and γ

S2 PREP §6.4 considered:

* **Option α** (rational-coefficient Pascal): **falsified by this PREP**, not pursuable.
* **Option β** (bypass Pascal, direct factor-wise simplification): close in spirit to (KR-1), but S2 PREP framed it as "no recurrence at all". (KR-1) **is** a recurrence — just in the k-direction.
* **Option γ** (Pascal in k-direction at fixed n): the closest match. S2 PREP line 174–175 conjectured a `k`-direction recurrence but didn't compute it. (KR-1) is the concrete answer.

So this PREP **affirms Option γ** with an explicit closed form, **refutes Option α**, and **refines Option β** into a constructive identity (KR-1) rather than an "avoid Pascal entirely" stance.

### 6.3 Concrete Lean recipe for S2 ACT + S3 ACT bundled (~75 LOC, 0 sorries)

```lean
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03
import Proofs.CombinationsFormulaOQ03  -- for qBinom_product

namespace QtMultichooseCoefficients

variable {R : Type*} [Field R]

noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

/-- The clean k-direction telescoping identity. No `q ≠ 1` hypothesis needed. -/
theorem qtBinom_succ_k (q t : R) (n k : ℕ) (hne : 1 - q ^ (k + 1) * t ^ k ≠ 0) :
    qtBinom q t n (k + 1) =
      qtBinom q t n k * (1 - q ^ (n - k) * t ^ k) / (1 - q ^ (k + 1) * t ^ k) := by
  unfold qtBinom
  rw [Finset.prod_range_succ]
  ring  -- single ring step closes the goal after the prod_range_succ expansion

@[simp] theorem qtBinom_zero_right (q t : R) (n : ℕ) :
    qtBinom q t n 0 = 1 := by simp [qtBinom]

@[simp] theorem qtMultichoose_zero_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = 1 := by simp [qtMultichoose]

-- S3 ACT: t = 1 specialization recovers parent's qBinom
theorem qtBinom_at_t_one (q : R) (n k : ℕ)
    (hq : ∀ j ∈ Finset.range k, 1 - q ^ (j + 1) ≠ 0) :
    qtBinom q 1 n k = qBinomProductForm q n k := by
  -- by induction on k using qtBinom_succ_k (with t=1) and parent's qBinom_product
  induction k with
  | zero => simp [qtBinom, qBinomProductForm]
  | succ k ih => sorry  -- ~15 LOC of qtBinom_succ_k application + parent's qBinom_product

-- S4 ACT: q = t = 1 specialization recovers Nat.choose
-- (deferred to S5 ACT; needs RatFunc.eval per S5 PREP)
end QtMultichooseCoefficients
```

Expected LOC: ~75 in the new file, **0 sorries** for `qtBinom_succ_k` + boundary cases + S3 induction (modulo `qBinomProductForm` parent lemma — see §6.4 below). **0 axioms.**

### 6.4 The `qBinomProductForm` parent dependency

`qtBinom_at_t_one` needs to match the parent's `qBinom` (Pascal-recursively-defined) at `t = 1`. The clean bridge is:
```
qBinomProductForm (q : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i)) / (1 - q ^ (i + 1))
```
and prove:
```
theorem qBinomProductForm_eq_qBinom (q : R) [Field R] (n k : ℕ)
    (hq : ∀ j ∈ Finset.range k, 1 - q ^ (j + 1) ≠ 0) :
    qBinomProductForm q n k = qBinom q n k
```
This is **NOT a one-liner** — needs `qBinom_product` (`CombinationsFormulaOQ03.lean:232-262`) lifted from `[CommRing R]` to `[Field R]`, with division replacing multiplication. **~30-40 LOC, 0 sorries**, by induction on `k`.

**Alternative**: skip the bridge entirely. Prove `qtBinom_at_t_one : qtBinom q 1 n k = qBinom q n k` by induction on `k` using **both** `qtBinom_succ_k` (this PREP) and parent's `qBinom_pascal` (parent line 200 area). The induction step requires showing that the k-direction recurrence at `t=1` agrees with the parent's Pascal recurrence — a non-trivial algebraic identity but **provable in `Field R` with the `hq` hypothesis** by clearing denominators.

---

## §7 — Implications for S2 ACT, S3 ACT, S4 ACT, S5 ACT (revised decomposition)

| Stage | Target | LOC | Sorries | Risk |
|---|---|---:|---:|---|
| **S2 ACT** (revised) | `qtBinom`/`qtMultichoose` defs + 4 boundary cases + `qtBinom_succ_k` (k-direction recurrence) | ~55 | 0 | Low — direct product manipulation, single `Finset.prod_range_succ` |
| **S3 ACT** (revised) | `qtBinom_at_t_one` via induction on `k` using `qtBinom_succ_k` + parent's `qBinom_pascal` | ~50 | 0 (with `hq` hypothesis) | Low — clean Field-level identity by induction |
| **S4 ACT** (revised, OPTIONAL) | Parent-extension `qBinomProductForm_eq_qBinom` if S3 wants the product form | ~40 | 0 | Low |
| **S5 ACT** | `qtBinom_at_one_one` via Path C (`RatFunc.eval`) per S5 PREP | ~150 | 0 | Med — `RatFunc.eval` distribution through `Finset.prod` |
| **S6+** | Macdonald polynomial connection (axiomatised) | — | — | — |

**Net axiom budget for verified status**: **0 axioms**, **0 sorries** for S2/S3 ACT. S4 (parent-extension) and S5 (Path C) are independent improvements.

**Critical simplification**: by ditching the Pascal direction and adopting (KR-1), the entire `a(n,k)` exponent question (state.md line 84, problem.md, knowledge.md §"(q,t)-Pascal recurrence") becomes **moot**. The S4 task as originally framed is **not solvable** (§5), but **not needed** either — (KR-1) covers everything S3/S4 needs.

---

## §8 — Caveats and uncertainty notes

* **All §3 / §4 computations verified by hand with two-pass cross-checks**, including the `t = 1` sanity check against parent's `q^{k+1}` (matches at all interior data points). The `t = 0` substitutions (used to falsify §6.4) are straightforward: `t = 0` makes every `t^a` factor zero, and the numerators reduce to constants in `q`.
* **No build performed**: this is a doc-only PREP. The Lean recipe in §6.3 is sketch-level; the actual S2 ACT implementer should verify `qtBinom_succ_k`'s `by ring` closure for `R = Polynomial ℚ` first, then promote to `Field R`.
* **The `qNumber(n+1)` denominator pattern in §3.3 (`C(n, 1)`)** was extrapolated from `n ∈ {1, 2}` only; for `n = 3`, the predicted denominator `(1+q+q²+q³)(1-q³t)` is unverified. **Best-effort prediction**, not a theorem. The reason it's plausible: by symmetry with the (1,1) and (2,1) cases, the leading numerator factor `q^{n+1}` and the (1-q^n t) factor should both grow with `n`. But the **point of this PREP is that no uniform Option α form works**, not that one almost-works.
* **The k-direction recurrence (KR-1)** is the standard textbook identity for q-binomials (see Andrews-Askey-Roy *Special Functions*, 1999, Thm 10.0.4); its (q,t)-extension is immediate from the product formula and is a "folk" identity in Macdonald-theoretic literature. It is **not novel mathematics** — only its Lean formalization is.
* **Saturation check (2026-05-13 ~10:00 UTC, ~3h after S5 PREP merge)**:
  * Open PRs on this slug: 0 (verified via `gh pr list --repo rjwalters/lean-genius --search "arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02 in:title" --state open`).
  * Merges in last 4h: 1 (S5 PREP #18639 at 07:19 UTC). Below the ≥3 merges/4h saturation threshold.
  * Total session count for slug: 5 PREPs (S1 OBSERVE merged from researcher-10; S2–S5 PREPs merged from researcher-6/12/5/9). Below the 70+-deep release threshold per memory `[researcher-3 triple-PREP doc-only session]`.
  * Safe to ship.
* **Mathlib pin**: `proofs/lake-manifest.json` (current pin at time of S5 PREP merge). No Mathlib bearer-audit performed in this PREP — all references are to **project-local** files (`ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean`, `CombinationsFormulaOQ03.lean`). If a future implementer needs Mathlib `Finset.prod_range_succ` / `ring` machinery, the line numbers are pin-stable since 2024.

---

## §9 — Files modified / not modified

**Modified** (worktree-relative paths, verified via `git status`):

* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/sessions/2026-05-13-s06-prep-option-alpha-falsification-and-k-direction-recurrence-pivot.md` (this file).

**NOT modified**:

* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/problem.md`
* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/knowledge.md`
* `research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/state.md`
* `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json`
* Any `.lean` files (no proofs added or modified; doc-only structural-pivot PREP).

---

## §10 — Trap notes

* **REPO_ROOT trap on `claim-problem.sh`** (memory `[Researcher — claim-problem.sh release fails from worktree CWD]`). Confirmed: claim-random invoked from `/Users/rwalters/GitHub/lean-genius` (main-repo CWD), not from `.loom/worktrees/researcher-6`. Lock created in main-repo's `research/claims/`. On release, will `cd /Users/rwalters/GitHub/lean-genius && /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release ...` to dodge the find_repo_root trap.
* **Branch creation from worktree** (memory `[Post-S1/S1b S2/S4 PREP session-note cluster] - git checkout -b from main-repo CWD trap`). Used `git switch --detach origin/main` + `git checkout -b research/arithmetic-series-oq030202-s6-prep-$(date +%s)` from worktree CWD. Verified branch attached to worktree via `git status`.
* **Write tool main-repo absolute-path trap** (memory `[Write tool absolute-path routes to main repo, not worktree]`). Used **worktree-prefixed** absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-6/research/problems/.../sessions/2026-05-13-s06-...md` to ensure the Write goes to the worktree, not the main repo. Verified via `git status` from worktree.
* **`gh` default-repo trap** (memory `[gh defaults to mathlib-fork remote, hides real PR state]`). All `gh pr list` invocations in this PREP used explicit `--repo rjwalters/lean-genius`. Pre-push race-check returned `[]` open PRs for the slug — clean.
* **No `.lake` symlink interaction**: this PREP performs no Docker build. The `.lake` symlink loop trap (memory `[.lake symlink loop + mid-build worktree wipe]`) is irrelevant. The Lean recipe in §6.3 is for a future implementer.
* **PR title length cap**: keeping PR title ≤ 70 characters per project convention.
* **No `gh api search/code` calls**: this PREP is mathematics-only, no Mathlib bearer-audit; rate limit (30/hr per memory `[researcher-12 triple Mathlib-bearer-audit PREP session]`) not consumed.

---

## §11 — References

* **Parent verified Lean entry**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` (`qMultichoose`, `qMultichoose_pascal` at lines 102–110, `qMultichoose_at_one` at line 56 area).
* **Grandparent `qBinom`**: `proofs/Proofs/CombinationsFormulaOQ03.lean:159-162` (recursive Pascal-defined), `:232-262` (`qBinom_product` factorial-form identity).
* **S1 OBSERVE PR**: #18327 (researcher-10, 2026-05-12).
* **S2 PREP PR**: #18382 (researcher-6, 2026-05-12). Falsified monomial Pascal (A) and Macdonald (B) at small cases; §6.4 left Option α with `???` marker for future verification.
* **S3 PREP PR**: #18558 (researcher-12, 2026-05-13). Rationality of qtMC and iterated limits; polynomial sub-lattice characterization.
* **S4 PREP PR**: #18616 (researcher-5, 2026-05-13). `Field R` 0/0 trap; Path A (`hq` hypothesis) for S2 ACT.
* **S5 PREP PR**: #18639 (researcher-9, 2026-05-13). `RatFunc.eval` rescues Path C; ditches `q ≠ 1` hypothesis under iterated `RatFunc (RatFunc ℚ)`.
* **Macdonald 1995, §VI.6**: standard reference for `(q,t)`-binomial product formula; convention adopted in problem.md and knowledge.md.
* **Andrews-Askey-Roy 1999, *Special Functions*, Thm 10.0.4**: k-direction telescoping identity for q-binomials (the (q,t)-extension (KR-1) of this PREP is the natural generalization).
* **Mathlib pin**: `proofs/lake-manifest.json` (Mathlib HEAD pin as of S5 PREP merge). `Finset.prod_range_succ` (used in §6.3) is stable Mathlib API since 2023.
