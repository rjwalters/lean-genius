# S2c PREP — Ripple-scope correction for S2b PREP's Fix B/D: zero existing call sites

**Date**: 2026-05-13
**Researcher**: researcher-12
**Mode**: PREP (doc-only; ripple-scope audit refining S2b PREP §3.6's blast-radius estimate)
**Phase target**: AXIOM-FIX (Mechanic/Doctor PR shipping Fix B + Fix D in S2b PREP terms)
**Status**: pristine orthogonal to S1 OBSERVE (#18384), S2 PREP (#18475), S4 PREP (#18492), S2b PREP (#18535). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S2b PREP (#18535) §3.6 ("Critical-path recommendation") states:

> All current call sites (in `OQ-02`, `OQ-04`, `EhrhartCrossPolytope`,
> `EhrhartSimplexProven`) need to be updated to supply a `volume`
> field; that is a mechanical change.

S2b PREP §4 ("Honesty / scope caveats") similarly notes the Fix
"ripples through OQ-02, OQ-04, the `EhrhartCrossPolytope` and
`EhrhartSimplexProven` companion proofs".

**Direct grep verification shows this claim is incorrect.** None of
the named files import `Proofs.EhrhartPolynomials` or use the
`LatticePolytope` / `LatticePolygon` structure that S2b PREP proposes
to modify. The S2b PREP's proposed Fix B (move `volume` into the
structure) has **zero existing call sites** and **single-file blast
radius**: it touches only `Proofs/EhrhartPolynomials.lean`.

This correction matters because:

1. The S2b PREP "Recommended fix" (§1.5) cites cross-file ripple cost
   as a factor (Fix C vs Fix B trade-off, Fix B vs Fix E trade-off).
   With ripple cost = 0 across the board, the choice criteria
   collapse to **single-file LOC delta only**.
2. The S2b PREP §3.6 "Critical-path recommendation" describes the
   AXIOM-FIX PR as needing cross-file coordination ("ripples through
   OQ-02, OQ-04, ..."). With zero ripple, the AXIOM-FIX PR can be
   a single-file Mechanic patch.
3. The "axiom is load-bearing for downstream proofs" framing
   implicit in S2b PREP's prioritization is wrong: the axiom has
   **zero internal use sites** in `EhrhartPolynomials.lean` itself
   and **zero external use sites** in the gallery. It only becomes
   load-bearing if/when OQ-05 S3 ACT chooses to invoke it.

This PREP records the ripple-scope correction, updates the AXIOM-FIX
sequencing recommendation, and proposes a 1-file Mechanic patch
template.

This PREP is doc-only.

## 1. Direct grep verification (2026-05-13 ~06:40 UTC)

### 1.1 What S2b PREP claims

S2b PREP §3.6:

> All current call sites (in `OQ-02`, `OQ-04`, `EhrhartCrossPolytope`,
> `EhrhartSimplexProven`) need to be updated to supply a `volume`
> field; that is a mechanical change.

### 1.2 Direct grep — imports of `Proofs.EhrhartPolynomials`

```bash
$ grep -rn "^import Proofs.EhrhartPolynomials" proofs/
proofs/Proofs.lean:636:import Proofs.EhrhartPolynomials
proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:526:import Proofs.EhrhartPolynomials
```

Only **two files** import `Proofs.EhrhartPolynomials`:

1. `proofs/Proofs.lean` — the master Lake index file. This is a
   compilation manifest, not a consumer.
2. `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`
   — direct grep for `LatticePolytope`, `LatticePolygon`,
   `ehrhart_*` in this file:

   ```bash
   $ grep -nE "LatticePolytope|LatticePolygon|ehrhart_" \
       proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean
   (no matches)
   ```

   The import is **unused** — likely a stale leftover from a prior
   Aristotle batch that referenced something now removed.

### 1.3 The other Ehrhart family files don't import `EhrhartPolynomials`

```bash
$ for f in EhrhartCubeProven EhrhartSimplexProven EhrhartCrossPolytope \
           EhrhartCubeProvenOQ03 EhrhartCubeProvenOQ04 \
           EhrhartPolynomialOQ03 PicksTheorem PicksTheoremOQ01OQ02; do
    echo "=== $f.lean ==="
    grep "^import" proofs/Proofs/$f.lean | head -3
  done
```

Result (verified 2026-05-13 ~06:40 UTC):

| File | Imports `EhrhartPolynomials`? |
|---|---|
| `EhrhartCubeProven.lean` | No (only `Mathlib`) |
| `EhrhartSimplexProven.lean` | No (only `Mathlib`) |
| `EhrhartCrossPolytope.lean` | No (only `Mathlib`) |
| `EhrhartCubeProvenOQ03.lean` | No (only `Mathlib`) |
| `EhrhartCubeProvenOQ04.lean` | No (only `Mathlib`) |
| `EhrhartPolynomialOQ03.lean` | No (only `Mathlib`) |
| `PicksTheorem.lean` | No (only specific `Mathlib.*`) |
| `PicksTheoremOQ01OQ02.lean` | No (only specific `Mathlib.*`) |

**The four files named by S2b PREP §3.6 — OQ-02 (= EhrhartCrossPolytope),
OQ-04 (= EhrhartCubeProvenOQ04), EhrhartCrossPolytope, EhrhartSimplexProven
— do not import `Proofs.EhrhartPolynomials`.**

### 1.4 Each Ehrhart family file has its own data structures

`EhrhartPolynomialOQ03.lean:59` declares a **parallel** `LatticePolytope`
structure (different from `EhrhartPolynomials.LatticePolytope`):

```lean
-- In EhrhartPolynomialOQ03.lean, line 59:
structure LatticePolytope where      -- no `(d : ℕ)` parameter
  ...
```

This is structurally distinct from `EhrhartPolynomials.LatticePolytope (d : ℕ)`.
A Mathlib-side `decide` or `import` cannot conflate them.

The other Ehrhart files (`EhrhartCubeProven.lean`, etc.) work directly
with concrete `Fin d → ℝ` or `(Fin d → ℤ) × ...` constructions and
do not depend on either `LatticePolytope` formalization.

### 1.5 Internal use of `ehrhart_leading_coeff_volume` in `EhrhartPolynomials.lean`

```bash
$ grep -n "ehrhart_leading_coeff_volume" proofs/Proofs/EhrhartPolynomials.lean
141:axiom ehrhart_leading_coeff_volume (d : ℕ) (P : LatticePolytope d)
```

**Exactly one occurrence — the declaration at line 141.** The axiom
is not invoked anywhere else in the file.

`ehrhart_macdonald_reciprocity` (line 178) is similarly declared
once, never internally invoked.

### 1.6 Net ripple inventory

| File | Modification needed under Fix B | Status |
|---|---|---|
| `proofs/Proofs/EhrhartPolynomials.lean` | Edit `LatticePolytope` structure + `axiom ehrhart_leading_coeff_volume` (~12 LOC delta) | Required |
| `src/data/proofs/ehrhart-polynomials/meta.json` | Sync `lineCount` post-edit | Required |
| `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean` | Optionally drop the unused `import Proofs.EhrhartPolynomials` line | Optional (audit nit) |
| All other gallery files | None | None |

**Net: 1 file required + 1 meta sync + 0 ripple. The S2b PREP §3.6
"mechanical change... across four files" claim is overstated.**

## 2. Implications for the AXIOM-FIX recommendation

### 2.1 S2b PREP Fix B → simplified

S2b PREP §1.4 Fix B template (verbatim):

```lean
structure LatticePolytope (d : ℕ) where
  latticePointCount : ℕ → ℕ
  volume            : ℚ              -- NEW field
  volume_pos        : 0 < volume     -- NEW field
  nonempty          : 0 < latticePointCount 1
  count_zero        : latticePointCount 0 = 1

axiom ehrhart_leading_coeff_volume (d : ℕ) (P : LatticePolytope d) :
    (ehrhartPoly P).leadingCoeff = P.volume
```

Under S2c PREP's ripple correction:

- The 5 existing concrete `LatticePolytope` instances in
  `EhrhartPolynomials.lean` (lines 322-end, including `unitCube`,
  `standardSimplex`, `reeveTetrahedron`, `crossPolytope`, and the
  test-polygon constructors) need new `volume` / `volume_pos` fields.
- All `LatticePolygon` instances (extending `LatticePolytope 2`)
  inherit the new fields automatically — but if they wanted to
  override `volume` to equal `area`, they would need to supply both.

A simpler alternative under zero-ripple:

**Fix B' — `volume_eq_area` field on `LatticePolygon`, axiom only at `LatticePolytope`**:

```lean
structure LatticePolytope (d : ℕ) where
  latticePointCount : ℕ → ℕ
  volume            : ℚ
  volume_pos        : 0 < volume
  nonempty          : 0 < latticePointCount 1
  count_zero        : latticePointCount 0 = 1

axiom ehrhart_leading_coeff_volume (d : ℕ) (P : LatticePolytope d) :
    (ehrhartPoly P).leadingCoeff = P.volume

-- (LatticePolygon unchanged: inherits volume + volume_pos from parent.
--  The area field of LatticePolygon may or may not equal volume; the
--  bridge would add a side-condition or new field for area = volume
--  in 2D as needed.)
```

**Net LOC delta vs S2b PREP Fix B**: ~0. The recommendation is
unchanged, but the "ripple cost" framing in §3.6 should be replaced
with "0-ripple, 1-file change".

### 2.2 S2b PREP Fix D → simplified

S2b PREP §2.4 Fix D template (verbatim):

```lean
structure LatticePolygon extends LatticePolytope 2 where
  …
  interior_at_one : ∀ ic, interiorCount toLatticePolytope ic →
                    ic 1 = interiorPoints
```

Under ripple correction, Fix D has identical 0-ripple profile: it
adds one field to `LatticePolygon` (line 200 of `EhrhartPolynomials.lean`)
and 0 external files need updates.

Existing `LatticePolygon` instances inside `EhrhartPolynomials.lean`
(if any) need the new field. Let me check:

```bash
$ grep -n "LatticePolygon" proofs/Proofs/EhrhartPolynomials.lean
200:structure LatticePolygon extends LatticePolytope 2 where
261:structure LatticePolytope3D extends LatticePolytope 3 where
```

`LatticePolygon` is **declared** at line 200 but never **instantiated**
in `EhrhartPolynomials.lean`. So Fix D adds a field that 0 existing
instances need to fill. **Net LOC ripple inside `EhrhartPolynomials.lean`:
0**.

### 2.3 Updated AXIOM-FIX PR scope

The Mechanic/Doctor PR that ships Fix B + Fix D should be:

```
File: proofs/Proofs/EhrhartPolynomials.lean
  - Lines 82-88: LatticePolytope structure
    + 2 fields: volume : ℚ, volume_pos : 0 < volume
    Delta: +2 LOC (+ ~2 LOC commentary)
  - Line 141: axiom ehrhart_leading_coeff_volume
    Replace `(volume : ℚ) (hv : 0 < volume) : (ehrhartPoly P).leadingCoeff = volume`
    with `: (ehrhartPoly P).leadingCoeff = P.volume`
    Delta: -1 LOC, -1 LOC (net -2 LOC)
  - Line 200: LatticePolygon structure
    + 1 field: interior_at_one : ∀ ic, interiorCount toLatticePolytope ic → ic 1 = interiorPoints
    Delta: +3 LOC

File: src/data/proofs/ehrhart-polynomials/meta.json
  - Sync lineCount from 521 to ~524 (or current after build)

Total: ~5 net LOC delta, 1 file edit + 1 meta sync.
```

This is a **15-minute Mechanic patch**, not a multi-file refactor.

### 2.4 Updated stage table (revising S2b PREP §3.5)

| Stage | Deliverable | Files touched | LOC delta | Status |
|-------|-------------|---------------|-----------|--------|
| S1 | OBSERVE survey | 4 (slug dir + JSON) | +0 | done (PR #18384) |
| S2 PREP | Lean blueprint | 1 (slug session) | +0 | done (PR #18475) |
| S4 PREP | Q2 bridge memo | 1 (slug session) | +0 | done (PR #18492) |
| S2b PREP | Axiom audit | 1 (slug session) | +0 | done (PR #18535) |
| **S2c PREP** | **Ripple correction** (this PR) | **1 (slug session)** | **+0** | **in flight** |
| AXIOM-FIX | Fix B + Fix D | **1 Lean + 1 meta** | **~5 LOC** | unscheduled |
| S2 ACT | Create `EhrhartCubeProvenOQ05.lean` (3 sorries) | 4 (proof + index + meta + JSON) | ~80 LOC | unblocked |
| S3 ACT | Q1: `ehrhartPoly_2d_explicit` | 1 (slug proof) | ~200 LOC | blocked on AXIOM-FIX |
| S4 ACT | Q2: `simpleLatticePolygon_to_latticePolygon` | 1 (slug proof) | ~150 LOC | unblocked |
| S5 ACT | Q2 close: `picks_theorem_derived` | 1 (slug proof) + JSON | ~80 LOC | blocked on S3 |

**Key delta from S2b PREP §3.5**: the AXIOM-FIX row is reduced from
"multi-file ripple" to **single-file ~5 LOC** patch.

## 3. Sequencing flexibility

S2b PREP §3.6 recommended:

> Spawn one Mechanic or Doctor PR with Fix B + Fix D ... Then resume
> the OQ-05 roadmap at S2 ACT / S3 ACT in parallel.

This is still correct, but the **sequencing constraint is loose**.
Three orderings work:

### 3.1 Ordering A — AXIOM-FIX first, then S2/S3 ACT (S2b PREP's recommendation)

```
[AXIOM-FIX merge] → [S2 ACT merge] → [S3 ACT merge] → [S4 ACT merge] → [S5 ACT merge]
```

Pros: Clean dependency chain, fixes the inconsistency first.
Cons: AXIOM-FIX requires Mechanic/Doctor; researcher cannot ship it.

### 3.2 Ordering B — S2 ACT first (stubs only, no axiom invocation), then AXIOM-FIX, then S3+

```
[S2 ACT merge: stubs] → [AXIOM-FIX merge] → [S3 ACT merge] → ...
```

Pros: Researcher can ship S2 ACT (stubs) immediately; AXIOM-FIX
becomes a peer-priority Mechanic patch rather than a blocker.
Cons: The 3-sorry stub file briefly references the inconsistent
axiom (in theorem types), but does not invoke it (proofs are `sorry`).

### 3.3 Ordering C — S2 ACT bundles the AXIOM-FIX

Researcher ships a single PR that:
- Creates `EhrhartCubeProvenOQ05.lean` with 3 stubs
- Patches `EhrhartPolynomials.lean` (Fix B + Fix D, ~5 LOC)
- Updates `src/data/proofs/ehrhart-polynomials/meta.json`

Pros: Single PR delivers unblocked S3 ACT setup.
Cons: Crosses the Lean-research/gallery-data and infrastructure-fix
boundaries in one PR, which complicates Judge review.

### 3.4 Recommendation

**Ordering B**. It maximizes researcher autonomy while keeping the
AXIOM-FIX in Mechanic/Doctor territory where the Axiom Integrity
Policy expertise lives. The S2 ACT stub PR is purely scaffolding (no
axiom invocation), so it can land before or after the AXIOM-FIX.

If a Mechanic happens to be running concurrently and picks up the
AXIOM-FIX before S2 ACT lands, Ordering A is the result and no
coordination is needed.

## 4. What this PREP does not claim

- **Not a refutation of S2b PREP's mathematical content.** Issue #1
  (inconsistent axiom) and Issue #2 (unlinked `interiorPoints`) are
  real and S2b PREP §1-§2 correctly diagnosed them.
- **Not a change to Fix B or Fix D.** The proposed structural fixes
  are still the right shape. This PREP only updates the **scope and
  sequencing** of the eventual AXIOM-FIX PR.
- **Not a removal of the S2b PREP's prerequisite for S3 ACT.** The
  axiom inconsistency still blocks honest S3 derivation. The
  AXIOM-FIX is still on the critical path **before S3 ACT can
  meaningfully proceed**.
- **Not a claim that AngleTrisection's stale import is a bug.** It's
  an unused import; harmless to leave or trivial to remove.

## 5. Anti-targets

This PREP **does not**:

- Edit `proofs/Proofs/EhrhartPolynomials.lean` (the AXIOM-FIX is for
  Mechanic/Doctor, not researcher).
- Edit `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`
  (the stale import is out of slug scope).
- Edit any other Lean file.
- Modify the S2b PREP file (`2026-05-13-s2b-prep-axiom-audit-inconsistency.md`)
  — the ripple-scope claim stays as historical record; this PREP
  supersedes it for future-reader consumption.
- Modify `state.md`, `problem.md`, `knowledge.md`, or the JSON tracker.
- Modify any other prior session file.
- Ship S2 ACT (stubs) — defer to next session (Ordering B Step 1).
- Ship the AXIOM-FIX directly — defer to Mechanic/Doctor (Ordering B Step 2).

## 6. Race awareness / orthogonality

At PREP push time (2026-05-13 ~06:45 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none) | — |

Most recent merge on slug: PR #18535 (S2b PREP, merged 04:08 UTC),
~2h35min prior. Saturation window: 3 PREP merges in the past 4 hours
(S2 PREP, S4 PREP, S2b PREP all merged 03:07-04:08 UTC). **At the
edge of the ≥3-merges/4h threshold**, but the most recent merge was
~2.5h ago, signaling pace slowdown.

This PREP creates exactly one new file:

```
research/problems/ehrhart-cube-proven-oq-05/sessions/2026-05-13-s2c-prep-ripple-scope-correction-zero-consumers.md
```

Race safety: this PREP makes a load-bearing **scope refinement** of
S2b PREP §3.6 without modifying any predecessor file. If the Mechanic
were to ship the AXIOM-FIX during this PREP's review window, the
refinement is still useful as documentation but no longer
prescriptive. The PREP's main value is **catching the overstated
ripple cost before** the AXIOM-FIX PR is drafted.

## 7. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/ehrhart-cube-proven-oq-05/sessions/2026-05-13-s2c-prep-ripple-scope-correction-zero-consumers.md`
- 0 edits to existing files
- 0 Lean changes
- 0 Docker builds
- 0 axiom / sorry deltas in any compiled file

The correction is **scope-grade** (S2b PREP's recommendation stands;
this PREP only narrows the implementation cost from "multi-file
ripple" to "single-file 5-LOC patch"). It is **not a refutation** —
S2b PREP's mathematical findings (Issues #1 and #2) are confirmed
correct. The narrow correction is: **the AXIOM-FIX PR has zero
ripple to OQ-02, OQ-04, EhrhartCrossPolytope, or EhrhartSimplexProven,
because none of those files import `Proofs.EhrhartPolynomials`**.

## 8. Acceptance criteria for the AXIOM-FIX (Mechanic/Doctor) PR

Updated relative to S2b PREP §3.6:

- [ ] Edit `proofs/Proofs/EhrhartPolynomials.lean` only.
- [ ] Add 2 fields to `LatticePolytope` (line 82-88): `volume : ℚ`,
      `volume_pos : 0 < volume`. Delta: ~+4 LOC including docstring.
- [ ] Update 5 concrete `LatticePolytope` instances later in the file
      (`unitCube`, `standardSimplex`, etc.) to supply `volume` and
      `volume_pos`. **Pre-grep verification**: locate each instance
      and inventory the geometric volume (e.g., `unitCube : volume = 1`,
      `standardSimplex (d := 3) : volume = 1/6`, etc.).
- [ ] Replace `ehrhart_leading_coeff_volume` (line 141) signature with
      the `P.volume`-based form. Delta: -2 LOC net.
- [ ] Add 1 field to `LatticePolygon` (line 200): `interior_at_one`.
      Delta: ~+3 LOC including docstring.
- [ ] Sync `src/data/proofs/ehrhart-polynomials/meta.json` lineCount.
- [ ] Build verification:
      `./proofs/scripts/docker-build.sh Proofs.EhrhartPolynomials`.
- [ ] **Do not** edit OQ-02, OQ-04, EhrhartCrossPolytope,
      EhrhartSimplexProven, EhrhartCubeProven, EhrhartCubeProvenOQ03,
      EhrhartCubeProvenOQ04, EhrhartPolynomialOQ03 — verified zero
      ripple to these files at the 2026-05-13 06:40 UTC repo snapshot.
- [ ] **Do not** edit `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`
      — its stale `import Proofs.EhrhartPolynomials` is unused; removal
      is an optional audit-nit out of AXIOM-FIX scope.

The Mechanic/Doctor PR is **expected to be ~15 LOC delta, 1 Lean
file, 1 meta sync** — substantially smaller than S2b PREP §3.6's
implicit estimate.
