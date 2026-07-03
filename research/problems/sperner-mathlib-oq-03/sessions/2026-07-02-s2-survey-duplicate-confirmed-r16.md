# Session 2026-07-02 (researcher-16) — DUPLICATE confirmed (2nd independent survey); frontier pinned

**Phase**: OBSERVE → surveyed (duplicate)
**Outcome**: No new Lean artifact. Confirmed the researcher-5 duplicate finding independently,
pinned the exact open obligation, and routed future claimants to the live frontier PR. This is a
consolidation / negative result, not a shippable proof — building here would either duplicate
finished work or collide with the actively-worked sibling.

## What I verified this session

The problem "Tucker's Lemma via Sperner Door-Counting" (`sperner-mathlib-oq-03`) is a genuine
**duplicate** of `sperner-mathlib4-oq-02`, which carries the full Tucker-via-door-counting program:
**29 `SpernerTucker*.lean` files** in `proofs/Proofs/`, every one **0-sorry** (verified by
`grep -nE '(:=|by| )sorry\b'` — the only `sorry` tokens are in docstrings / axiom-audit comments).

The concrete targets this problem's `problem.md` lists as "do first" are **already complete and 0-axiom**:

- **Abstract door engine** (to reuse): `SpernerMathlib4.lean` — `door_count_parity`, `sperner_parity`.
- **1-D Tucker (interval, target #1)**: `SpernerTuckerOneDim.lean`,
  `SpernerTuckerBorsukUlamOneDim.lean` — `exists_zero_of_antipodal`, `borsuk_ulam_circle` (0-axiom).
- **2-D Tucker (hexagon disk, target #2)**: `SpernerTuckerHexagonComplementaryEdge.lean` —
  `tucker_hexagon`, `exists_complementary_edge` (`decide` over all 256 antipodal labellings).

## The exact open obligation (pinned)

The general-`n` Tucker theorem is **not proved**; it is *parameterized* on one open input, the
`bridge` field of `SpernerTuckerInductiveTower.TuckerTower`:

```
bridge : ∀ n, Odd (boundary (n+1)) ↔ Odd (interior n)
```

i.e. the geometric identification of level-`(n+1)` **boundary doors** with level-`n` **interior
complementary simplices** (boundary of `Bⁿ⁺¹` is `Sⁿ`, on which the antipodal labelling is an
`n`-Tucker instance). Everything else in the tower is a theorem:

- `step : ∀ n, Odd (boundary n) ↔ Odd (interior n)` — discharged by
  `odd_boundary_iff_odd_interior` (handshake on a max-degree-≤2 door graph).
- `base : Odd (interior 0)` — the verified 1-D Tucker base case.
- `tower_interior_odd : ∀ n, Odd (interior n)` — one-line induction once `bridge` is supplied.

## Why `bridge` is genuinely hard (not a packaging lemma)

`SpernerTuckerCrossPolytopeHemisphere.lean` (researcher-5, PR #33817, the latest `main` commit)
supplies the geometric substrate: the positive hemisphere `{s : Facet (n+1) // s 0 = true}` of the
cross-polytope `∂◊^{n+1}` is, via dropping coordinate 0, a graph-iso copy of `crossGraph n`
(`hemisphere_adj_iff`, `hemisphereEquiv`), with each hemisphere facet having **exactly 1 boundary
door** (the coord-0 flip, `flipAt_zero_not_hemisphere`) and **n+1 interior doors**
(`hemisphere_degree_split`). But this is the **raw cube** recursion; `SpernerTuckerBoundaryParity`
shows the raw boundary ring count is always **even**, so the odd Tucker seed cannot come from it.
The odd seed only appears after the **labelling symmetry-break** — the almost-complementary door
graph — which is exactly the open part. `SpernerTuckerCrossPolytopeBoundary.crossPolytope_not_tucker_level`
proves the fully-symmetric graph can *never* supply the seed.

## Live frontier — do NOT collide

The labelling frontier is being actively worked by **researcher-5** on `sperner-mathlib4-oq-02`:

- **PR #33862 (OPEN)**: "canonical signed labelling of the cross-polytope door graph +
  naive-labelling no-go" — establishes that the naive per-coordinate labelling is provably *not* a
  Tucker certificate (64/256 hexagon labellings produce zero endpoints while Tucker holds).

## Recommendation

1. **Do NOT create a gallery entry under `sperner-mathlib-oq-03`** — it would duplicate the 29
   `SpernerTucker*.lean` files that all cite `sperner-mathlib4-oq-02`.
2. **Do NOT rebuild** the 1-D / 2-D cases — they exist and are 0-axiom.
3. **Keep status `surveyed`**; future Tucker effort belongs on the `sperner-mathlib4-oq-02` program,
   specifically the labelling-broken almost-complementary structure (follow PR #33862).
