# Erdős Problem #574 (OQ-01) — Turán Number for Consecutive Cycle Pairs

**Question.** For `k ≥ 2`, is
`ex(n; {C_{2k-1}, C_{2k}}) = (1 + o(1)) · (n/2)^{1+1/k}` ?
I.e. does additionally forbidding the odd cycle `C_{2k-1}` cost nothing
asymptotically beyond forbidding `C_{2k}` alone?

**Status:** OPEN. Gallery entry is a statement-level stub (custom
`SimpleGraph'`, placeholder `exConsecutiveCycles`, 0 theorems, 0 sorries,
0 axioms).

---

## Session 2026-06-14 (Session 1) — ORIENT

**Mode:** FRESH
**Outcome:** progress (ORIENT — durable lower-bound verification, framing sharpened)

### Key structural observation: the LOWER bound is unconditional

The conjecture is an asymptotic *equality*. It splits cleanly:

- **Upper bound** `ex(n;{C_{2k-1},C_{2k}}) ≤ (1+o(1))(n/2)^{1+1/k}`:
  trivially `≤ ex(n; C_{2k})` (more forbidden subgraphs ⟹ fewer edges).
  This is the GENUINELY OPEN half — and is in fact *at least as hard* as
  determining the leading constant of `ex(n; C_{2k})`, which is itself
  open for general `k` (known only for `k = 2, 3, 5`).

- **Lower bound** `ex(n;{C_{2k-1},C_{2k}}) ≥ (1-o(1))(n/2)^{1+1/k}`:
  **UNCONDITIONAL for the values where the even-cycle construction is
  known** (`k = 2, 3, 5`). Reason: the dense `C_{2k}`-free graphs from
  incidence geometry (projective planes / generalized polygons; Wenger
  1991, Lazebnik–Ustimenko–Woldar 1995) are **bipartite**. A bipartite
  graph has *no odd cycle whatsoever*, so it is automatically
  `C_{2k-1}`-free. Forbidding the odd cycle is therefore "free" on the
  lower-bound side — not conjecturally, but as a theorem.

So the open content of #574 is purely an **upper-bound** matching
question, inheriting the open even-cycle-constant problem. The "free"
phenomenon on the lower side is already a proof, not evidence.

### Durable verification (k = 2): exact leading constant

For `k = 2` (forbid `C_3` and `C_4`) the incidence graph of the
projective plane `PG(2,q)` (`q` prime) is bipartite, `(q+1)`-regular,
girth 6, with `q²+q+1` points and the same number of lines. Computed
directly (`verify_lower_bound.py`, all checks pass for `q = 2,3,5,7`):

| q | n   | edges | bipartite | C₃-free | C₄-free | edges/(n/2)^{3/2} |
|---|-----|-------|-----------|---------|---------|-------------------|
| 2 | 14  | 21    | ✓         | ✓       | ✓       | 1.1339            |
| 3 | 26  | 52    | ✓         | ✓       | ✓       | 1.1094            |
| 5 | 62  | 186   | ✓         | ✓       | ✓       | 1.0776            |
| 7 | 114 | 456   | ✓         | ✓       | ✓       | 1.0596            |

The ratio is **exact in closed form**:
```
edges        (q+1)(q²+q+1)        q+1
--------- = ------------------ = ---------------  ⟶ 1   (from above)
(n/2)^1.5   (q²+q+1)^{3/2}       √(q²+q+1)
```
because `(q+1)/√(q²+q+1) = √(1 + q/(q²+q+1)) → 1`. So the construction
attains the conjectured **leading constant** `(1/2)^{1+1/k}` exactly in
the limit (not merely the order `n^{3/2}`), confirming the `k = 2` lower
bound `ex(n;{C_3,C_4}) ≥ (1-o(1))(n/2)^{3/2}`.

### Why this is not just enumeration theater
Small-`q` numbers alone would be weak (the `o(1)` dominates), but here
they back a *closed-form* limit, so the verification certifies the
asymptotic constant, not just a few data points.

### Mathlib gaps (for an eventual Lean lower-bound proof)
- Mathlib has `SimpleGraph.isBipartite` / 2-colorings and the
  no-odd-closed-walk fact, which would give `C_{2k-1}`-freeness of a
  bipartite witness essentially for free.
- Mathlib does **not** have: projective-plane / generalized-polygon
  incidence graphs as a packaged construction, the Bondy–Simonovits
  even-cycle upper bound, or extremal-number (`ex`) machinery for graphs.
  Building the `PG(2,q)` witness + its girth-6 proof is a few-hundred-line
  finite-geometry project; the upper bound is research-level (OPEN).

### Next steps
- ACT (lower bound, `k = 2`): formalize the `PG(2,q)` incidence graph in
  Mathlib's `SimpleGraph`, prove bipartite ⟹ `C_3`-free and girth ≥ 6 ⟹
  `C_4`-free, and the edge count `(q+1)(q²+q+1)`. This is a buildable,
  unconditional lower-bound theorem (Docker required; currently down).
- Generalize the "bipartite ⟹ `C_{2k-1}`-free" lemma to all `k` — this is
  the reusable core and is `O(50)` LOC against Mathlib's bipartite API.
- Upper bound stays OPEN; do not submit to Aristotle.

### Files
- `research/erdos-574-oq-01/verify_lower_bound.py` (new, runs clean)
- `research/erdos-574-oq-01/knowledge.md` (this file)
