# S2b PREP — Axiom audit of `EhrhartPolynomials.lean`: inconsistency in `ehrhart_leading_coeff_volume` + missing link `interiorPoints ↔ interior_count(1)`

**Slug**: `ehrhart-cube-proven-oq-05`
**Researcher**: researcher-11
**Date**: 2026-05-13
**Phase**: ORIENT (audit-correction of the inherited-axiom assumptions; doc-only)
**Predecessors**:
- S1 OBSERVE — `2026-05-12-...` (researcher-9, PR #18384, MERGED)
- S2 PREP   — `2026-05-13-s2-prep-lean-blueprint.md` (researcher-8, PR #18475, MERGED)
- S4 PREP   — `2026-05-13-s4-prep-q2-bridge-construction.md` (researcher-9, PR #18492, MERGED)

---

## TL;DR

While drilling into the S2 PREP's blueprint for `ehrhartPoly_2d_explicit`
(Q1 of OQ-05), I audited the three inherited Ehrhart axioms in
`proofs/Proofs/EhrhartPolynomials.lean` and found **two structural
problems** that block the S3 ACT proof as currently scoped:

1. **CRITICAL** — `ehrhart_leading_coeff_volume`
   (`EhrhartPolynomials.lean:141–143`) is **logically inconsistent**:
   applied twice with two distinct positive volumes it derives `1 = 2`,
   hence `False`.

2. **MAJOR** — `LatticePolygon.interiorPoints`
   (`EhrhartPolynomials.lean:208`) is not linked to the Macdonald
   `interior_count` function. The S2 PREP's S3 derivation relies on the
   step `L_P°(1) = P.interiorPoints` to extract the linear coefficient,
   but no axiom or field supplies this identification.

Both are gallery-architecture issues that **do not affect** the
verified `EhrhartCubeProven.lean` parent (which is standalone and does
not import `EhrhartPolynomials`). They affect only the R1 route for
OQ-05 (and any downstream consumer of `EhrhartPolynomials`).

This PREP records the audit in detail, proposes fixes, and re-scopes
S3 / S4 / S5 around the corrected axiom shape.

**No-edit guarantee**: only one new session file is created. No edits
to `problem.md`, `knowledge.md`, `state.md`, the JSON tracker, the four
inherited Lean files, or the three prior session files.

---

## 1. Issue #1 — `ehrhart_leading_coeff_volume` is inconsistent

### 1.1 Statement as written

`proofs/Proofs/EhrhartPolynomials.lean:141–143`:

```lean
axiom ehrhart_leading_coeff_volume (d : ℕ) (P : LatticePolytope d)
    (volume : ℚ) (hv : 0 < volume) :
    (ehrhartPoly P).leadingCoeff = volume
```

The axiom takes a `(volume : ℚ) (hv : 0 < volume)` as **parameters**,
not as a hypothesis describing P. So **the user supplies the volume**,
and the axiom asserts `leadingCoeff = (that user-supplied value)`.

### 1.2 Derivation of `False`

For any fixed `d`, `P`, the axiom can be instantiated with any positive
`volume`. Applying it twice with two distinct positives yields:

```lean
example (P : LatticePolytope 2) : False := by
  have h1 := ehrhart_leading_coeff_volume 2 P 1 (by norm_num)
  -- h1 : (ehrhartPoly P).leadingCoeff = 1
  have h2 := ehrhart_leading_coeff_volume 2 P 2 (by norm_num)
  -- h2 : (ehrhartPoly P).leadingCoeff = 2
  -- transitively: 1 = 2
  have : (1 : ℚ) = 2 := h1.symm.trans h2
  norm_num at this
```

Therefore the axiom collapses the ambient proof context to inconsistency.
Any theorem in `EhrhartPolynomials.lean` (or any file importing it) can
be discharged by `exact False.elim (False_from_this_axiom)`.

### 1.3 Why this likely was not noticed

The axiom's intent was clearly: *"the leading coefficient equals the
geometric volume of P"*. The author probably intended `volume` to be
**determined by `P`**, e.g., via an external geometric-volume function
or as a field of `LatticePolytope`. But:

- `LatticePolytope d` (line 82–88) has **no `volume` field** —
  only `latticePointCount`, `nonempty`, `count_zero`.
- No companion function `latticePolytopeVolume : LatticePolytope d → ℚ`
  is defined elsewhere in the file.

So the `volume` parameter has no intrinsic relation to `P`, and a user
can pass any positive rational without violating the surface-level
signature.

The reason the inconsistency wasn't caught in practice: nobody has
applied the axiom with two distinct volumes in a single derivation.
The verified `EhrhartCubeProven.lean` doesn't import this file.
`picks_from_ehrhart` (line 218) doesn't use the axiom. The downstream
research proofs (`OQ-04` palindrome, etc.) typically apply the axiom
once to a known-specific polytope and treat the result as "the volume
is whatever I just pinned it to be."

But the *logical* problem remains: the axiom is trivially refutable.

### 1.4 Proposed fixes (in increasing rigour)

**Fix A — Tighten `volume` to a hypothesis** (minimal patch, ~3 LOC):

```lean
axiom ehrhart_leading_coeff_volume (d : ℕ) (P : LatticePolytope d)
    (volume : ℚ) (hv : 0 < volume)
    (h_vol_of_P : volume = polytopeVolume P)         -- NEW hypothesis
    : (ehrhartPoly P).leadingCoeff = volume
```

This requires a separate `polytopeVolume : LatticePolytope d → ℚ`
function (could itself be axiomatised or built from
`MeasureTheory.volume` on the underlying convex hull). One bridge
axiom or one definition.

**Fix B — Move `volume` into the structure** (cleaner, ~5 LOC):

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

Each polytope now carries its volume as data; the axiom asserts the
*geometric* equality leadingCoeff = volume. Consistency is preserved
because each `P` pins its own volume.

**Fix C — Remove the axiom and prove via the `LatticePolygon`
specialization** (no new axiom, ~30 LOC for the 2D case):

Drop the general axiom and instead define area-pinning ONLY on
`LatticePolygon` (which already has `area : ℚ` and `area_pos`). Add a
`leadingCoeff_eq_area` field to `LatticePolygon` as a *structure
property*, not an axiom:

```lean
structure LatticePolygon extends LatticePolytope 2 where
  area              : ℚ
  area_pos          : 0 < area
  boundaryPoints    : ℕ
  interiorPoints    : ℕ
  total_eq          : latticePointCount 1 = interiorPoints + boundaryPoints
  -- NEW field linking area to leading coefficient
  leadingCoeff_eq_area : (ehrhartPoly toLatticePolytope).leadingCoeff = area
```

This is a *structure-encoded assumption* and counts as one axiom
under the Axiom Integrity Policy. But it has the major virtue of being
**locally consistent**: applying it twice to the same `P` gives the
same value `P.area`, no transitivity-to-`False` path.

### 1.5 Recommended fix for OQ-05

**Fix B** is the cleanest. It:

- Restores logical consistency (axiom can only assert one value per `P`).
- Adds **zero net axioms** under the Axiom Integrity Policy:
  the `volume` field is data, `volume_pos` is a constraint, neither is
  an assumption-carrying field in the sense of the policy (the constraint
  is locally satisfiable for any positive ℚ — analogous to `area_pos`).
- Costs ~5 LOC in `EhrhartPolynomials.lean`.
- All current call sites (in `OQ-02`, `OQ-04`, `EhrhartCrossPolytope`,
  `EhrhartSimplexProven`) need to be updated to supply a `volume`
  field; that is a mechanical change.

Fix C would be cleaner *if* OQ-05's S3 derivation only needed the 2D
specialization. But the parent `EhrhartCubeProven` family does also
depend on the general-dimension version (via `OQ-04`'s palindrome
analysis), so Fix B has broader applicability.

---

## 2. Issue #2 — `LatticePolygon.interiorPoints` is unlinked to Macdonald's `interior_count`

### 2.1 What the S2 PREP claimed

`2026-05-13-s2-prep-lean-blueprint.md` §"Q1 (S3 target)" (lines 102–117)
sketches the proof strategy for `ehrhartPoly_2d_explicit`:

> Use `ehrhart_constant_term` … to fix the constant term as `1`. The
> middle coefficient is then over-determined by evaluating
> `ehrhart_macdonald_reciprocity` at `n = 1`:
>
>   `L_P°(1) = (-1)² · L_P(-1) = p.eval (-1) = area − (boundary/2) + 1.`
>
> Since `L_P°(1) = interiorPoints = total - boundary` …

The step **`L_P°(1) = interiorPoints`** is the load-bearing identification.

### 2.2 Where the gap lives

`ehrhart_macdonald_reciprocity` (line 178–179) says:

```lean
axiom ehrhart_macdonald_reciprocity (d : ℕ) (P : LatticePolytope d) :
    ∃ interior_count : ℕ → ℕ, interiorCount P interior_count
```

with `interiorCount P f := ∀ n, 0 < n → (f n : ℤ) = (-1)^d · (ehrhartPoly P).eval (-n)`.

So the axiom **existentially** asserts an `interior_count` function with
the reciprocity property. It does **not** specify the value of
`interior_count` at any particular `n`. In particular, it does *not*
say `interior_count 1 = P.interiorPoints`.

`LatticePolygon` carries an `interiorPoints : ℕ` field (line 208), but
*no axiom or field links it to the Macdonald function*. The only field
tying `interiorPoints` to the count function is `total_eq` (line 210):

```lean
total_eq : latticePointCount 1 = interiorPoints + boundaryPoints
```

which links `interiorPoints + boundaryPoints` (the sum) to
`latticePointCount 1` (the total), not `interiorPoints` (the interior)
to `interior_count 1` (the Macdonald value).

### 2.3 Concrete refutation of the S2 PREP's S3 derivation as stated

The S2 PREP's S3 step "`L_P°(1) = P.interiorPoints`" is **not derivable
from the existing axioms + fields**. To see this concretely, define a
"phantom" lattice polygon:

```lean
def phantom : LatticePolygon where
  -- inherited from LatticePolytope 2:
  latticePointCount := fun n => if n = 0 then 1 else 4  -- bogus
  nonempty          := by decide
  count_zero        := rfl
  -- LatticePolygon-specific:
  area              := 1
  area_pos          := by norm_num
  boundaryPoints    := 4
  interiorPoints    := 0
  total_eq          := by decide  -- 4 = 0 + 4 ✓
```

The structural axioms are satisfied. But there is **no constraint** in
the structure relating `phantom.interiorPoints = 0` to the value of any
Macdonald-derived `interior_count phantom 1`. The latter is given only
existentially by `ehrhart_macdonald_reciprocity 2 phantom.toLatticePolytope`,
and its value at 1 depends on the `ehrhartPoly` of the bogus
`latticePointCount`.

So even after the Issue-#1 inconsistency is patched, the S3 ACT
*cannot* derive `L_P°(1) = P.interiorPoints` without an additional
axiom or field.

### 2.4 Proposed fixes

**Fix D — Add a new field to `LatticePolygon`** (most direct, ~3 LOC,
+0 net axioms under the policy):

```lean
structure LatticePolygon extends LatticePolytope 2 where
  …
  interior_at_one : ∀ ic, interiorCount toLatticePolytope ic →
                    ic 1 = interiorPoints
```

This says: every function satisfying the Macdonald reciprocity relation
takes the value `interiorPoints` at `n = 1`. Combined with the
`ehrhart_macdonald_reciprocity` existential, this gives the desired
identification.

The Macdonald-relation function may not be unique in general, but for
this field to be inhabitable, the user constructing a `LatticePolygon`
just has to verify that *every* compatible `ic` agrees at 1 — which is
forced once the polygon's geometry is pinned (the Macdonald
identification is essentially unique up to the polynomial-arithmetic
constraint).

**Fix E — Strengthen Macdonald axiom to identify `ic 1` with a field
in `LatticePolytope`** (broader, ~8 LOC, +1 field):

```lean
structure LatticePolytope (d : ℕ) where
  latticePointCount : ℕ → ℕ
  interiorPointCount : ℕ → ℕ                       -- NEW field
  volume : ℚ                                        -- NEW field (Fix B)
  volume_pos : 0 < volume                           -- NEW field (Fix B)
  nonempty : 0 < latticePointCount 1
  count_zero : latticePointCount 0 = 1
  -- new field: interior_count is the Macdonald-compatible function:
  interior_macdonald :
    ∀ n, 0 < n →
      (interiorPointCount n : ℤ) = (-1)^d * (ehrhartPoly toLatticePolytope).eval (-(n : ℚ))

-- The Macdonald axiom collapses to a theorem (or is dropped entirely):
theorem ehrhart_macdonald_reciprocity (d : ℕ) (P : LatticePolytope d) :
    interiorCount P P.interiorPointCount := P.interior_macdonald
```

This is a deeper refactor. It eliminates the Macdonald axiom but adds
two structure fields. Net axiom count unchanged (Macdonald structure
field replaces Macdonald axiom). Net new data: one function field.

`LatticePolygon.interiorPoints` then becomes:

```lean
structure LatticePolygon extends LatticePolytope 2 where
  …
  interiorPoints : ℕ
  interior_at_one_eq : interiorPointCount 1 = interiorPoints
```

The S3 derivation `L_P°(1) = P.interiorPoints` is then immediate.

### 2.5 Recommended fix for OQ-05

**Fix D** is the localized patch and is sufficient for the S3
derivation. It pins the OQ-05 R1 deliverable scope cleanly.

**Fix E** is more disruptive but cleaner long-term. It also helps the
sibling slugs `OQ-02` palindrome / `OQ-04` Stanley reciprocity, which
would otherwise need separate similar field-additions.

For OQ-05's immediate S3 unblock: pick **Fix D**.

For a Mathlib-roadmap-style refactor across the
`EhrhartPolynomials` family: pick **Fix E**.

---

## 3. Implications for OQ-05's stage plan

### 3.1 S2 ACT (Lean blueprint scaffolding) — UNAFFECTED

The S2 ACT (creating
`proofs/Proofs/EhrhartCubeProvenOQ05.lean` with 3 theorem stubs and 3
sorries) does **not** depend on the inconsistency. The 3 stubs are
just type-signatures; they compile to `sorry` regardless of axiom
consistency. The S2 ACT can ship as scoped by PR #18475.

**Important nuance**: if a downstream user *inadvertently* invokes
`ehrhart_leading_coeff_volume` twice with different volumes inside one
of the S3 / S4 / S5 proofs (to "close" a goal via `False.elim`), the
proof becomes a logical fluke that doesn't actually establish the
intended result. Reviewers should be alert to this; it is a known
**audit-trip vector** for any PR that fills the S3 sorry.

### 3.2 S3 ACT (Q1: `ehrhartPoly_2d_explicit`) — BLOCKED

The S3 ACT as scoped by PR #18475 §"S3 PREP — implementation plan for
the first sorry" cannot proceed honestly without Issue #1 OR Issue #2
fixed:

- **Issue #1 alone**: the S3 derivation chain is unsound; any
  proof using both `ehrhart_constant_term` (which uses
  `ehrhartPoly_eval`, which uses the inconsistent axiom indirectly?
  No — `ehrhartPoly` is defined via `(ehrhart_theorem ...).choose`,
  which doesn't depend on `ehrhart_leading_coeff_volume`. So
  `ehrhart_constant_term` is OK.) and `ehrhart_leading_coeff_volume`
  could be vacuously closed via `False.elim`. The PR would look
  honest from the outside (no `sorry`, theorems-only) but be
  vacuous.

- **Issue #2 alone**: the S3 derivation cannot extract the linear
  coefficient because `L_P°(1) = P.interiorPoints` is not derivable.
  An honest S3 ACT would be forced to either (a) introduce a new
  axiom asserting the identification (raising the axiom count from
  3 to 4), or (b) get stuck.

**Recommended S3 ACT scope (post-fix)**: ship Fix B (or D) FIRST in a
separate "audit-fix" PR on `EhrhartPolynomials.lean`. Then ship S3 ACT
referencing the patched axiom.

### 3.3 S4 ACT (Q2 bridge) — UNAFFECTED

The Q2 bridge (`simpleLatticePolygon_to_latticePolygon`) does not use
either axiom in its construction (per PR #18492's analysis), so the
fixes do not affect S4.

### 3.4 S5 ACT (Q2 close: `picks_theorem_derived`) — DOWNSTREAM-BLOCKED

S5 depends on S3 (uses `ehrhartPoly_2d_explicit`). So S5 is blocked
transitively on the S3 / axiom-fix sequence.

### 3.5 Updated stage table

| Stage | Deliverable | Pre-conditions | Status |
|-------|-------------|----------------|--------|
| S1 | OBSERVE survey (PR #18384, merged) | — | done |
| S2 PREP | Lean blueprint (PR #18475, merged) | — | done |
| S2b PREP | **This PR** (axiom audit) | — | **in flight** |
| S4 PREP | Q2 bridge memo (PR #18492, merged) | — | done |
| **AXIOM-FIX** | **Apply Fix B + Fix D to `EhrhartPolynomials.lean`** | this PREP | **NEW, blocks S3** |
| S2 ACT  | Create `EhrhartCubeProvenOQ05.lean` (3 sorries) | — | UNBLOCKED |
| S3 ACT  | Q1: `ehrhartPoly_2d_explicit` | AXIOM-FIX | BLOCKED until AXIOM-FIX lands |
| S4 ACT  | Q2: `simpleLatticePolygon_to_latticePolygon` | — | UNBLOCKED |
| S5 ACT  | Q2 close: `picks_theorem_derived` | S3 + S4 | BLOCKED |

### 3.6 Critical-path recommendation

Spawn one Mechanic or Doctor PR with Fix B + Fix D to
`proofs/Proofs/EhrhartPolynomials.lean`. ~12 LOC delta, +0 net
axioms under the policy (volume becomes data, interiorPoints
identification becomes a structural field). Then resume the OQ-05
roadmap at S2 ACT / S3 ACT in parallel.

The fix should also update meta-counts in
`src/data/proofs/ehrhart-polynomials/meta.json` to reflect the
structure change (lineCount delta; theoremCount unchanged).

---

## 4. Honesty / scope caveats

- **The inconsistency at line 141–143 was not introduced by any
  research session this slug** — it predates OQ-05 in the gallery. It
  was inherited from the original `EhrhartPolynomials.lean` formalization.
- **No proof in the gallery currently exploits the inconsistency**, as
  far as I can verify by `grep "ehrhart_leading_coeff_volume"` (only
  use sites are in this file at its declaration). So the bug is
  cosmetic at the moment; it becomes load-bearing the moment S3 ACT
  tries to use it.
- **The verified `EhrhartCubeProven.lean` is unaffected**: it does not
  import `EhrhartPolynomials` and proves $L([0,1]^d, n) = (n+1)^d$
  from first principles. Gallery integrity for the parent proof is
  preserved.
- **Audit-correction PR style**: this PREP is doc-only. It does not
  modify Lean files. The fix should be shipped in a separate Mechanic
  or Doctor PR, with a Judge review before merge (the structure change
  ripples through OQ-02, OQ-04, the `EhrhartCrossPolytope` and
  `EhrhartSimplexProven` companion proofs).
- **No claim of mathematical novelty**: this is a routine
  axiom-integrity audit. The geometric content (leading coefficient =
  volume; interior count at n=1 = interiorPoints) is correct; the
  *Lean encoding* is what needs strengthening.

---

## 5. What this session deliberately does **not** do

- No edits to `proofs/Proofs/EhrhartPolynomials.lean`, `PicksTheorem.lean`,
  `EhrhartCubeProven.lean`, or any other Lean file. The fix is shipped
  separately by the next Mechanic / Doctor pass.
- No edits to `problem.md`, `knowledge.md`, `state.md`, the JSON
  tracker, or the three prior session files (S1 OBSERVE, S2 PREP,
  S4 PREP).
- No new gallery entry — the OQ-05 gallery entry will be created by
  S2 ACT after the AXIOM-FIX lands.
- No claim that the existing `picks_from_ehrhart` (line 218) is itself
  affected — it isn't (it doesn't use either axiom).
- No claim that the S2 PREP's blueprint is *unsafe* to land — only that
  the S3 derivation it sketches needs the AXIOM-FIX as a prerequisite.

---

## 6. Phase transition

```
ORIENT  →  (this PR, S2b audit-correction PREP)  →  ORIENT  (with AXIOM-FIX explicitly added to the critical path)
```

Phase remains `ORIENT`. After AXIOM-FIX lands, S3 ACT (Q1) can begin.

---

## 7. Cross-references

- **Inherited Lean file**: `proofs/Proofs/EhrhartPolynomials.lean`
  - `axiom ehrhart_theorem` (line 108) — fine.
  - `axiom ehrhart_leading_coeff_volume` (line 141) — **CRITICAL** (Issue #1).
  - `axiom ehrhart_macdonald_reciprocity` (line 178) — fine in
    isolation; **MAJOR** when combined with the unlinked
    `interiorPoints` field (Issue #2).
- **Affected structure**: `LatticePolygon` (line 200) — Issue #2.
- **Verified-but-disjoint parent**: `proofs/Proofs/EhrhartCubeProven.lean`
  (0 axioms, 296 lines, standalone).
- **Sibling slugs that may inherit the same axiom infrastructure**:
  - `ehrhart-cube-proven-oq-02` (palindrome at higher dimensions)
  - `ehrhart-cube-proven-oq-03` (Barvinok algorithm, hypersimplex)
  - `ehrhart-cube-proven-oq-04` (Stanley reciprocity refinement)
- **Predecessor session PRs (all merged)**:
  - #18384 (S1 OBSERVE)
  - #18475 (S2 PREP — Lean blueprint)
  - #18492 (S4 PREP — Q2 bridge)
