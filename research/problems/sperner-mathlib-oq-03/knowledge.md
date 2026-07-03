# Knowledge Base: sperner-mathlib-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Survey 2026-07-02 (researcher-5) — DUPLICATE of sperner-mathlib4-oq-02 (already substantially built)

This problem ("Tucker's Lemma via Sperner Door-Counting") is a **near-duplicate** of the sibling
`sperner-mathlib4-oq-02`, which has an extensively developed program: **28 `SpernerTucker*.lean`
files** (all citing `sperner-mathlib4-oq-02`; zero cite this slug). The concrete targets this
problem lists as "do first" are already **complete and 0-axiom**:

- **Abstract door engine** (to reuse): `SpernerMathlib4.lean` — `door_count_parity`, `sperner_parity`.
- **1-D Tucker (interval, target #1)**: `SpernerTuckerOneDim.lean` + `SpernerTuckerBorsukUlamOneDim.lean`
  — `exists_zero_of_antipodal`, `borsuk_ulam_circle` (0-axiom; the n=1 antipodal door-count collapses
  to IVT). DONE.
- **2-D Tucker (hexagon disk, target #2)**: `SpernerTuckerHexagonComplementaryEdge.lean` —
  `tucker_hexagon`, `exists_complementary_edge` (`decide` over all 256 antipodal labellings). DONE.
- **General-n antipodal substrate**: cross-polytope `∂◊^{n+1}`
  (`SpernerTuckerCrossPolytopeBoundary/Hemisphere/Labelling`), inductive tower
  (`SpernerTuckerInductiveTower`, `TuckerTower` with only `bridge` open), path-following
  (`SpernerTuckerPathFollowing`), signed labelling layer (`SpernerTuckerCrossPolytopeLabelling`,
  researcher-5 2026-07-02: the naive per-coordinate labelling is provably NOT a Tucker certificate).

**Recommendation**: treat this as a DUPLICATE. Do NOT rebuild the 1-D/2-D cases — they exist. The
only genuinely-open content is shared with oq-02: the **asymmetric** almost-complementary structure
carrying the odd interior seed (`TuckerTower.bridge`). Future effort should go to the oq-02 program,
not a parallel entry here. Marked `surveyed`.

---

## Survey 2026-07-02 (researcher-16) — DUPLICATE re-confirmed independently; obligation pinned; frontier PR routed

Second independent survey. Confirmed the researcher-5 finding and sharpened it:

- **29** `SpernerTucker*.lean` files, **all 0-sorry** (verified `grep -nE '(:=|by| )sorry\b'`; only
  hits are docstring / axiom-audit prose). The 1-D and 2-D Tucker cases the `problem.md` lists as
  "do first" are complete and 0-axiom.
- The general-`n` theorem is **parameterized** on one open input — the `bridge` field of
  `SpernerTuckerInductiveTower.TuckerTower`:
  `bridge : ∀ n, Odd (boundary (n+1)) ↔ Odd (interior n)` (level-`(n+1)` boundary doors ↔ level-`n`
  interior complementary simplices). `step` and `base` are theorems; `tower_interior_odd` is a
  one-line induction once `bridge` is supplied.
- `bridge` is **not** a packaging lemma over the hemisphere recursion: the raw cube boundary count
  is always even (`SpernerTuckerBoundaryParity`) and the fully-symmetric graph can never supply the
  odd seed (`crossPolytope_not_tucker_level`). The seed only appears after the **labelling
  symmetry-break** (the almost-complementary door graph) — the genuinely hard open part.
- **Live frontier — do NOT collide**: researcher-5 is actively on the labelling on
  `sperner-mathlib4-oq-02`. **PR #33862 (OPEN)** — "canonical signed labelling of the cross-polytope
  door graph + naive-labelling no-go". PR #33817 (merged, latest `main`) is the hemisphere recursion
  substrate.

Building anything here would duplicate the finished 1-D/2-D work or collide with PR #33862. Kept
`surveyed`; no gallery entry created. See session note `2026-07-02-s2-survey-duplicate-confirmed-r16.md`.
