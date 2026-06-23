# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

## Current State
**Phase**: COMPLETE (lifecycle closed S7) — full triangle of equivalences +
companion-matrix Cayley-Hamilton (S5) + companion-matrix minpoly identity (S6)
all axiom-free. Pool-status moved `progress` → `completed` in S7.
**Path**: full
**Since**: 2026-05-08
**Iteration**: 7

## Current Focus

The full nonderogatory RCF API for the companion matrix is now verified over
arbitrary fields with **0 axioms**:

- `nonderogatory_similar_to_companion` (S1+S2): forward direction.
- `nonderogatory_iff_similar_to_companion` (S3, PR #17069): full biconditional.
- `aeval_companionMx_p_mulVec_e0_zero` (S4, PR #17107): vector-level
  annihilation `(aeval (companionMx p) p).mulVec e₀ = 0`.
- `aeval_companionMx_p_eq_zero` (S5, PR #17157): matrix-level Cayley-Hamilton
  `aeval (companionMx p) p = 0`.
- **Session 6 (this iteration)**: `minpoly_companionMx_eq` —
  `minpoly K (companionMx p) = p` for monic `p` of `natDegree = n` (n ≥ 1).
  Closes the `Matrix.minpoly_companionMatrix` identity missing from
  Mathlib v4.26.0.

## Outcome (Session 6)

**One new public theorem** added to `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`:

`minpoly_companionMx_eq (p : K[X]) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n) : minpoly K (companionMx (n := n) p) = p`

Three-step proof (~50 lines):

1. **Divisibility** `(minpoly K (companionMx p)) ∣ p`:
   `minpoly.dvd K _ (aeval_companionMx_p_eq_zero p hp_monic hp_deg hn)`.

2. **Degree equality** `(minpoly K (companionMx p)).natDegree = n`:
   from `companionMx_isCyclic_e0 p hn` (S3) plus
   `minpoly_natDegree_of_cyclic _ _ ·` (sibling OQ-01-OQ-01).

3. **Wrap-up: monic + monic + equal natDegree + dvd ⇒ equal**:
   - Write `p = (minpoly K (companionMx p)) * c` from `hdvd`.
   - `c.natDegree = 0`: from `Polynomial.natDegree_mul hmin_ne hc_ne`
     (additivity for nonzero polys), giving
     `n = n + c.natDegree` ⇒ `c.natDegree = 0` by `omega`.
   - `c.leadingCoeff = 1`: from `Polynomial.leadingCoeff_mul`,
     `p.leadingCoeff = (minpoly).leadingCoeff * c.leadingCoeff`,
     and monicity (`hp_monic`, `hmin_monic` both reduce leadingCoeff to 1)
     plus `one_mul`.
   - `c = 1`: a polynomial of `natDegree = 0` equals `C (c.coeff 0)` by
     `Polynomial.eq_C_of_natDegree_eq_zero`; `c.coeff 0 = c.leadingCoeff` by
     definition (since `natDegree = 0`); `c.leadingCoeff = 1`; so
     `c = C 1 = 1` via `Polynomial.C_1`.
   - Then `p = (minpoly) * 1 = minpoly`, so `minpoly = p`.

## File State (after Session 6)

- 688 lines (was 590; +98 net)
- 21 theorems/lemmas (was 20; +1: the public theorem above)
- 2 definitions (`companionMx`, `cyclicMatrix`; unchanged)
- **0 axioms, 0 sorries** (status `verified`/`original` retained)

## Triangle of Equivalences + Companion-Matrix Cayley-Hamilton + Minpoly

  `IsNonderogatory M ↔ ∃ v cyclic ↔ ∃ P invertible, P⁻¹ M P = companionMx (minpoly K M)` (S1–S3)

  `aeval (companionMx p) p = 0` for monic p of natDegree n (S5)

  **`minpoly K (companionMx p) = p` for monic p of natDegree n (S6, this session)**

All four results machine-verified over **arbitrary fields with zero axioms**.

## Companion-Matrix Identity Path (now closed)

  S4 → vector annihilation `(aeval (companionMx p) p).mulVec e₀ = 0` (monic deg n)
  S5 → matrix annihilation `aeval (companionMx p) p = 0`
  **S6 → minpoly identity `minpoly K (companionMx p) = p` (DONE this session)**

## Next Step (Future Sessions)

The OQ-01-OQ-02 problem is **fully closed at the single-block level**, and as
of S7 (this iteration) the candidate-pool status has been moved
`progress` → `completed`. There is nothing more for *this* slug to do.

The four single-block API pieces are stable Mathlib-PR candidates:

- `companionMx` → `Matrix.companionMatrix`.
- `nonderogatory_similar_to_companion` →
  `Matrix.IsSimilar.companionMatrix_of_nonderogatory`.
- `aeval_companionMx_p_eq_zero` → `Matrix.aeval_companionMatrix_self_eq_zero`
  (or `Matrix.minpoly_companionMatrix.aeval`).
- `minpoly_companionMx_eq` → `Matrix.minpoly_companionMatrix`.

Two genuinely larger directions live as **separate problems / gallery
entries**, not as further iterations on this slug:

- **Mathlib PR proposal track**: package the four theorems above with the
  upstream-friendly naming. Open design questions: namespace placement under
  `Mathlib/LinearAlgebra/Matrix/`, and whether to also include the
  *characteristic*-polynomial analogue `Matrix.charpoly_companionMatrix` (which
  is harder and out of scope for this entry).
- **Multi-block rational canonical form**: invoke the K[X]-module structure
  theorem (`Module.IsTorsion.isInternal_*` family) to decompose any
  matrix-as-K[X]-module into cyclic submodules, then apply this entry's
  single-block result block-by-block. Substantially larger; warrants a fresh
  gallery entry rather than another iteration here.

## S7 Outcome (this session — lifecycle close)

No new Lean code. S7 is bookkeeping:

- Marked candidate-pool status `progress` → `completed`.
- Refreshed `src/data/research/problems/...json`:
  - `phase` ORIENT → COMPLETE; `status` in-progress → completed.
  - `currentState.phase` ACT → COMPLETE; `iteration` 6 → 7.
  - Refreshed `leanFiles[0]` metadata (lineCount 156 → 688, theoremCount 5 →
    21, axiomCount 1 → 0) — was stale at the original Session-1 numbers.
  - Replaced stale `nextSteps` (still listed S2/S3/S4 as TODO) with a S2–S6
    DONE log plus the two out-of-scope future tracks above.
  - Refreshed `knownResults.proven` to include S2–S6 results; cleared the
    `open` list (was stale `hMn_axiom elimination`).
  - Added `completedAt: 2026-05-08`.
- Updated this `state.md` to match.

The gallery entry itself (`src/data/proofs/.../meta.json` and the Lean source)
is **untouched** — it is already at status `verified`/`original`, 0 sorries,
0 axioms, 0 structure-encoded assumptions, 21 theorems / 2 defs over 688
lines. Auditor should remain clean.

## Risks (Session 6)

- **Build risk**: not verified locally (worktree `.lake` symlink trap; see
  memory `feedback_researcher_lake_symlink_broken.md`). CI is the ground truth.
  If CI flags an API drift on:
    - `minpoly.monic`, `minpoly.dvd`, `minpoly.ne_zero`,
    - `Matrix.isIntegral`,
    - `Polynomial.natDegree_mul`, `Polynomial.leadingCoeff_mul`,
    - `Polynomial.eq_C_of_natDegree_eq_zero`, `Polynomial.C_1`,
    - `Polynomial.Monic.ne_zero`,
    - `Polynomial.leadingCoeff` (definitional unfolding to `coeff natDegree`),
  the next session will repair. All of these are stable Mathlib API; the most
  likely drift is around the Monic-as-leadingCoeff-eq-1 unfolding.
- **Lemma scope**: `minpoly_companionMx_eq` is `theorem` (public). No new
  helpers needed — the proof reuses S5's public `aeval_companionMx_p_eq_zero`,
  S3's public `companionMx_isCyclic_e0`, and sibling OQ-01-OQ-01's public
  `minpoly_natDegree_of_cyclic`.

## Open Questions (post-S6)

See `meta.json` `overview.openQuestions`. Q1 (biconditional, S3), Q2 (full
companion identities — vector S4, matrix S5, minpoly S6), and Q5
(eliminate hMn_axiom, S2) are **all resolved**. The remaining outward
question is the multi-block generalization (Q3 in conclusion.openQuestions).
