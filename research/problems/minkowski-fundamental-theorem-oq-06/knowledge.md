# Knowledge Base: minkowski-fundamental-theorem-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

The **Minkowski–Hlawka theorem** is the non-constructive *existence* counterpart to the
gallery's parent (Minkowski's convex-body *obstruction* theorem). It asserts the densest
lattice packing in dimension `n ≥ 2` has density

    δ_n ≥ ζ(n) / 2^(n-1)

equivalently: every symmetric bounded measurable `S` with `vol(S) < 2·ζ(n)` is avoided
(off the origin) by some unimodular lattice. The standard proof averages
`#(Λ ∩ S \ {0})` over the space of unimodular lattices `X_n = SL_n(ℤ)\SL_n(ℝ)` via
**Siegel's mean-value theorem** and extracts a better-than-average lattice — without
exhibiting one.

---

## Insights

### Session 2026-06-14 (ORIENT) — gap audit + constants pinned

**Mode**: FRESH · **Outcome**: ORIENT (survey, effectively blocked for full proof)

**What I did**
- Confirmed Hlawka is *not* in the gallery: only the obstruction parent exists
  (`MinkowskiFundamentalTheorem.lean`, sorry-free, proves a different theorem). `grep -i
  hlawka proofs/` hits only `Erdos997Problem.lean` (unrelated).
- Audited Mathlib at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  `MeasureTheory/Group/GeometryOfNumbers.lean` contains only **Blichfeldt**
  (`exists_pair_mem_lattice_not_disjoint_vadd`) and **Minkowski convex-body**
  (`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_{lt,le}_measure`). No Siegel
  mean-value (`gh search` = 0), no packing density (`gh search packingDensity` = 0).
  "Minkowski–Hlawka theorem" is a **title-only** entry in Mathlib `docs/1000.yaml` (no
  `decl:`/`author:`) → an *unmet* target upstream.
- Wrote a durable numerical artifact `verify_minkowski_hlawka.py` (all checks pass).

**Key findings**
- **Normalization (correction to seed).** For *symmetric* `S` the threshold is
  `vol(S) < 2·ζ(n)`, not `< ζ(n)`. Chain: take `S = ball(2r)`; an avoiding unimodular
  lattice has min distance `≥ 2r`, so radius-`r` balls pack with density
  `vol(ball r) = vol(S)/2^n = 2ζ(n)/2^n = ζ(n)/2^(n-1)`. The seed's `< ζ(n)` is the
  star-body / ±-identified convention.
- **Bound hierarchy** (verified n ∈ {2..8, 24}): `2^(-n) ≤ ζ(n)/2^(n-1) ≤ δ_n^known`
  (A2, D3, D4, D5, E6, E7, E8, Leech). MH is a valid but very weak lower bound vs known
  optima (e.g. n=8: MH `0.00784` vs E8 `0.2537`).
- **Improvement factor.** `MH / trivial = 2ζ(n) → 2` as `n→∞`. So Hlawka beats the
  elementary maximal-packing bound `δ_n ≥ 2^(-n)` by only ~a factor of 2; both decay like
  `2^(-n)` and the exponential gap to the (also exponential) Kabatiansky–Levenshtein
  *upper* bound is untouched.

**Decision: SURVEY / effectively BLOCKED for full proof.** The standard route requires
Siegel's mean-value theorem over `SL_n(ℝ)/SL_n(ℤ)` (>1000 LOC of missing measure theory).

**Actionable next targets** (both Docker-gated):
1. *Staged*: state Hlawka with Siegel's identity as an explicit hypothesis
   (axiom/structure field), then prove "better-than-average ⇒ existence" with ±-pairing →
   `δ_n ≥ ζ(n)/2^(n-1)`. Isolates the one deep lemma; badge=axiom, status=axiomatized.
2. *Elementary stepping stone* (~200–400 LOC, Mathlib-only): the saturation bound
   `δ_n ≥ 2^(-n)` via maximal packing + radius-doubling cover. The "easy constant" that MH
   sharpens by `2ζ(n)`.

**Files**: `verify_minkowski_hlawka.py`, `src/data/research/problems/minkowski-fundamental-theorem-oq-06.json`.

---

## Dead Ends

- Full formalization via Siegel's mean-value theorem from current Mathlib — blocked: the
  homogeneous space `SL_n(ℤ)\SL_n(ℝ)`, its finite invariant measure, and Siegel's identity
  are all absent upstream.
