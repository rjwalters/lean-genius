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

## Session 2026-06-14 (Session 2, researcher-3, ORIENT — elementary lower-bound frontier)

**Mode:** CONTINUE (build-free; Docker `docker info` times out, Aristotle previously
`Resource not found`). The S1 ACT plan (discharge `g_le_n`, add `g(n) ≤ n−1` and `g(n) ≥ ⌈n/2⌉`)
is fully specified but build-gated. This session sharpens the **lower-bound** picture S1 left as a
"candidate first Lean lower bound," answering: *is ⌈n/2⌉ the best elementary construction, and is
it worth trying to push the collinear idea further?* (extends `verify_g_structure.py`, all asserts
pass, exact integer squared-distance arithmetic).

**Finding (4a) — ⌈n/2⌉ is the 1D optimum.** Exhaustive search over ALL collinear integer configs
with positions in `[0, 2n+6]` gives `max D = ⌈n/2⌉` for n=3..7 — equal spacing is optimal on a
line, and **no collinear (1D) configuration beats ⌈n/2⌉**. So the S1 elementary lower bound is the
*ceiling* of the 1D approach: a 1D Lean lower bound tops out at ⌈n/2⌉ = 0.5n and cannot be nudged
toward the 0.7n literature bound by re-spacing points on a line. (Empirical over a wide position
range, not a proof; robust enough to direct strategy.)

**Finding (4b) — 2D strictly beats it (exact witnesses).** The collinear bound is **not tight**;
two-dimensional configs achieve `D > ⌈n/2⌉` already at small n (verified from scratch, integer
grid, exact squared distances):
- `n=4`: pts `(0,0),(0,1),(0,2),(1,1)` — R-vec `[3,1,3,2]`, **D=3 > ⌈4/2⌉=2**.
- `n=6`: pts `(0,0),(0,1),(0,2),(1,1),(2,0),(2,1)` — R-vec `[4,3,5,2,5,3]`, **D=4 > ⌈6/2⌉=3**.

**Strategic consequence for the ACT.** The elementary lower-bound frontier is **intrinsically
2-dimensional**: the clean, Lean-friendly `g(n) ≥ ⌈n/2⌉` collinear construction (S1) is the best a
1D argument can give, and any improvement toward Csizmadia's 0.7n must use genuinely 2D point sets.
This reframes the lower-bound ACT: formalize `g(n) ≥ ⌈n/2⌉` as the *complete* elementary 1D result
(not a way-station to be improved on a line), and treat ">0.5n" as a separate, 2D, harder target.
**Honesty:** this session does **not** exhibit a closed-form 2D family with `D > ⌈n/2⌉` for all `n`
(the witnesses are small-n, brute-force) — finding one is the genuine open elementary question and
is NOT claimed here. No Lean written (Docker down); the three axioms (`csizmadia_bound`,
`upper_bound` legit literature; `g_le_n` still the dischargeable one) are unchanged.

### Files Touched (Session 2)

- `research/problems/erdos-653-oq-01/verify_g_structure.py`: +2 checks (4a 1D-optimality,
  4b 2D-beats witnesses), +summary lines.
- `research/problems/erdos-653-oq-01/knowledge.md`: this Session 2 entry.
