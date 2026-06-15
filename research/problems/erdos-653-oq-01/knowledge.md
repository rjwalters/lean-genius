# Erdős Problem #653 (OQ-01) — Distinct distance counts in the plane

**Question (the OQ):** Is the main conjecture `g(n) ≥ (1 - o(1))·n` true?

**Status: OPEN.** This is the central conjecture of the problem, not closable in a
research session. Best known bounds: `0.7·n < g(n) < n − c·n^{2/3}`.

## Definitions

For `n` distinct points `x₁,…,xₙ ∈ ℝ²`:
- `R(xᵢ)` = number of **distinct** distances from `xᵢ` to the other points.
- `D(config)` = number of **distinct** `R`-values over the configuration.
- `g(n)` = max of `D` over all `n`-point configurations.

## Bound landscape

| Bound | Value | Nature |
|-------|-------|--------|
| Lower (Erdős–Fishburn) | `g(n) > (3/8)n` | literature |
| Lower (Csizmadia) | `g(n) > (7/10)n` | literature (current best) |
| Upper (deep) | `g(n) < n − c·n^{2/3}` | literature |
| Upper (elementary) | `g(n) ≤ n − 1` (n ≥ 2) | **elementary, see below** |
| Lower (elementary) | `g(n) ≥ ⌈n/2⌉` | **elementary construction, see below** |

## Session 2026-06-14 (Session 1, FRESH, ORIENT)

**Mode:** FRESH. **Outcome:** ORIENT / scouted (both backends down — Docker
unavailable, Aristotle "Resource not found").

### Axiom map of `proofs/Proofs/Erdos653Problem.lean`

The file is `0 sorries, 3 axioms`. The three axioms are NOT equal in status:

1. `csizmadia_bound : ∀ n ≥ 10, g n > 7·n/10` — **genuine literature axiom**
   (Csizmadia's theorem; a large, deep proof). Legitimate citation.
2. `upper_bound : ∃ c>0, ∀ n≥2, g n < n − c·n^{2/3}` — **genuine literature axiom**
   (the deep gap result). Legitimate citation.
3. `g_le_n : ∀ n, g n ≤ n` — **trivially provable; should be a theorem, not an
   axiom.** Per the repo's Axiom Integrity Policy this is the one to discharge.

### Key elementary observation (the WHY behind `g(n) < n`)

Every `R(xᵢ)` lies in `{1,…,n−1}` for `n ≥ 2` (a point has at least one and at
most `n−1` distinct distances to the others). Hence the `R`-values occupy a set
of only `n−1` possible values, so

> **`g(n) ≤ n − 1` (n ≥ 2)** — strictly sharper than the file's `g_le_n` axiom.

This is exactly why `g(n) < n` is *elementary*; the content of the deep upper
bound is the much larger `c·n^{2/3}` gap, not the strict inequality itself.

### Elementary lower-bound construction

Equally-spaced collinear points `(0,0),…,(n−1,0)` give
`R(point i) = max(i, n−1−i)`, whose distinct values number `⌈n/2⌉`. So
`g(n) ≥ ⌈n/2⌉` by an explicit construction (far from the 0.7n literature bound,
but fully elementary and self-contained — a candidate first Lean lower bound).

### Structured-config facts (validated)

- Regular `n`-gon: all vertices share the single `R`-value `⌊n/2⌋`, so `D = 1`.
- Collinear equally-spaced: `D = ⌈n/2⌉` (closed form verified).

### Durable artifact

`verify_g_structure.py` (exact integer squared-distance arithmetic, no float
ambiguity, no `Date`/RNG-seed nondeterminism):
- (1) `g(n) ≤ n−1` held on all sampled configs (n=2..9, 4000 each);
- (2) regular-polygon `D=1` and `R=⌊n/2⌋` for n=3..20; collinear `D=⌈n/2⌉` n=2..12;
- (3) small-n brute-force lower bounds on a 4×4 grid (illustrative, not exact g).

### Mathlib gaps

- No incidence-geometry / distinct-distance machinery (Guth–Katz, Szemerédi–Trotter)
  in the pinned Mathlib — the deep bounds are out of reach (>1000 LOC each).
- The elementary results (`g(n) ≤ n−1`, `g(n) ≥ ⌈n/2⌉`) need only `Finset.card`
  lemmas (`card_image_le`, `Nat.sSup_le`) — buildable in well under 100 LOC.

### Next steps (build-gated — need Docker or Aristotle back up)

1. Discharge `g_le_n` → `theorem` via `Nat.sSup_le` + `card_image_le`
   (`numDistinctRValues S = (S.image (distinctDistCount S)).card ≤ S.card = n`).
2. Strengthen to `g_le_n_sub_one : ∀ n ≥ 2, g n ≤ n − 1` (R-values ⊆ Icc 1 (n−1)).
3. Add elementary lower bound `g_ge_half : ∀ n, ⌈n/2⌉ ≤ g n` via the collinear
   construction (needs membership witness into the sSup set).
4. Leave `csizmadia_bound` and `upper_bound` as cited axioms (correct per policy).

### Honest assessment

The OQ itself is open and untouched. This session's value is modest: an accurate
axiom-status map, one elementary sharpening (`g(n) ≤ n−1`) the file misses, an
elementary lower-bound construction, and a durable structural verifier. No Lean
was changed (build-verification unavailable this session).
