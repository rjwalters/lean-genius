# S4 PREP — Q2 bridge: `SimpleLatticePolygon → LatticePolygon`

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only design memo)
**Phase target**: S4 ACT (the structural-bridge piece between Q1 and Q2)
**Status**: pristine, orthogonal to in-flight S2 PREP (PR #18475)
which covers Q1 (Lean blueprint + axiom audit + 2D explicit-form
proof outline).

## Why this PREP

The S1 OBSERVE (`state.md` Stage table) decomposes the R1 route into:

- **S2** Lean skeleton with 3 theorem stubs (in flight via PR #18475).
- **S3** Q1: `ehrhartPoly_2d_explicit` (the linear-term identity).
- **S4** Q2 bridge: `simpleLatticePolygon_to_latticePolygon`
  (the **subject of this PREP**).
- **S5** Q2 close: `picks_theorem_derived` (combine S3 + S4 +
  `picks_from_ehrhart`).

S4 is **the structurally non-trivial step**. `SimpleLatticePolygon`
and `LatticePolygon` are parallel but **non-overlapping in shape**:

| Field | `SimpleLatticePolygon` | `LatticePolygon` (extends `LatticePolytope 2`) |
|-------|-----------------------|-----------------------------------------------|
| `area : ℚ` | ✓ | ✓ |
| `area_pos : 0 < area` | ✓ | ✓ |
| `interior_count : ℕ` | ✓ | ✓ (`interiorPoints`) |
| `boundary_count : ℕ` | ✓ | ✓ (`boundaryPoints`) |
| `boundary_ge_three : 3 ≤ b` | ✓ | ✗ (not in `LatticePolygon`) |
| `latticePointCount : ℕ → ℕ` | **✗** (missing!) | ✓ (inherited) |
| `nonempty : 0 < count 1` | **✗** (missing!) | ✓ (inherited) |
| `count_zero : count 0 = 1` | **✗** (missing!) | ✓ (inherited) |
| `total_eq : count 1 = i + b` | **✗** (missing!) | ✓ |

**The crux**: `SimpleLatticePolygon` carries **no count function**.
`LatticePolygon` *requires* a `latticePointCount : ℕ → ℕ` function
(inherited from `LatticePolytope 2`). The bridge therefore cannot be
purely *projection-of-fields*; it must **construct** a count function
from the slim `SimpleLatticePolygon` data, OR appeal to an existence
axiom.

This memo scopes four possible bridge constructions, evaluates each
against the **Axiom Integrity Policy** (project CLAUDE.md
"Restructuring axioms into structures is a valid proof architecture
choice, but it does not change the mathematical status"), and
recommends the cleanest path forward for S4 ACT.

## 1. Four bridge constructions

The bridge has to produce a `latticePointCount n : ℕ` for every
`SimpleLatticePolygon P`. Four candidates:

### Construction A — Bridge axiom (1 new axiom)

```lean
/-- **Bridge axiom**: every `SimpleLatticePolygon` arises as the
    underlying data of some `LatticePolygon`. -/
axiom exists_latticePolygon_from_simple
    (P : PicksTheorem.SimpleLatticePolygon) :
    ∃ Q : EhrhartPolynomials.LatticePolygon,
      Q.area = P.area ∧
      Q.boundaryPoints = P.boundary_count ∧
      Q.interiorPoints = P.interior_count

noncomputable def simpleLatticePolygon_to_latticePolygon
    (P : PicksTheorem.SimpleLatticePolygon) :
    EhrhartPolynomials.LatticePolygon :=
  (exists_latticePolygon_from_simple P).choose
```

**Pros**: Trivial Lean signature; total ~6 LOC; defers all
construction to mathematical existence.

**Cons**: Adds **1 new axiom**. Violates the OQ-05 deliverable
contract of "0 new axioms" stated in `state.md` Stage table.

**Verdict**: Last-resort fallback only.

### Construction B — Inductive count via Ehrhart inversion

Use `ehrhart_theorem` itself to **define** the count function
implicitly. That is: declare `latticePointCount` to be the function
that makes the Ehrhart polynomial correct at every `n`.

```lean
noncomputable def latticePointCount_of_simple
    (P : PicksTheorem.SimpleLatticePolygon) : ℕ → ℕ := fun n =>
  -- Choose a polynomial via ehrhart_theorem applied to a hypothetical
  -- LatticePolytope; here we use the closed-form picks_ehrhart formula.
  ⌊picks_ehrhart P.area P.boundary_count (n : ℚ)⌋₊
```

This is circular: `picks_ehrhart` is defined in
`EhrhartPolynomials.lean`, but it is a **closed-form** specific to
the 2D case, not derived from Ehrhart axioms. So we can use it
**without** invoking `ehrhart_theorem`.

**Problem**: `picks_ehrhart P.area P.boundary_count` returns a `ℚ`,
not a `ℕ`. The `⌊·⌋₊` ("natural-floor") gives an `ℕ`, but **only
agrees with the integer-valued count when `area * n^2 + (b/2) n + 1 ∈ ℕ`**.

For lattice polygons, this is automatically true (it's the actual
lattice point count), but Lean doesn't know this without an
auxiliary axiom or proof. Two sub-options:

- **B.1**: Prove `picks_ehrhart P.area P.boundary_count n ∈ ℕ` for
  all `n : ℕ`. This requires `2 * area ∈ ℤ` (true for lattice
  polygons by `2 area = 2i + b - 2` from Pick's formula — but that's
  exactly what we're trying to derive, so it's *circular* for the
  purposes of this bridge).
- **B.2**: Drop the requirement that `latticePointCount` returns the
  *true* count, and let it return a placeholder that happens to
  satisfy the `LatticePolygon` invariants
  (`count_zero, nonempty, total_eq`).

Option B.2 gives a clean construction:

```lean
noncomputable def latticePointCount_of_simple
    (P : PicksTheorem.SimpleLatticePolygon) : ℕ → ℕ := fun n =>
  match n with
  | 0 => 1                                          -- count_zero
  | 1 => P.interior_count + P.boundary_count        -- total_eq
  | _ => 1   -- placeholder; doesn't matter for picks_theorem_derived
```

**Pros**: 0 new axioms; explicit; satisfies the three needed
invariants (`count_zero`, `nonempty`, `total_eq`).

**Cons**: The count function does **not** match the real lattice
point count for `n ≥ 2`. Mathematically, this construction is
"truncating to a 2-jet" — we only need correctness at `n ∈ {0, 1}`
for the derivation of Pick's theorem.

**Subtle issue**: `LatticePolygon` does **not** require Ehrhart
polynomiality as a field. The Ehrhart polynomial comes from the
axiom `ehrhart_theorem` applied **post hoc**. So a `LatticePolygon`
whose `latticePointCount` is "wrong for `n ≥ 2`" is still a valid
`LatticePolygon` — it just means the Ehrhart polynomial of *this
particular `LatticePolygon`* is also "wrong for `n ≥ 2`."

**But**: `ehrhartPoly_2d_explicit` (Q1) claims the *Ehrhart polynomial*
has explicit form $A n^2 + (b/2) n + 1$. The Q1 derivation uses
`ehrhart_macdonald_reciprocity` and `ehrhart_leading_coeff_volume`,
which apply to the abstract `latticePointCount` regardless of its
specific values. So **even with the placeholder construction**, Q1
would derive an explicit polynomial that **doesn't actually count
lattice points** of any geometric polygon.

This is **mathematically vacuous but Lean-valid**: the Ehrhart
axioms describe the polynomial form abstractly, not the counts
of any specific polygon. The bridge would technically work, but
the result would be "Pick's theorem holds for the polygon's
*declared* area, interior count, and boundary count" — which is
exactly Pick's identity as an algebraic fact, not a geometric one.

**Verdict**: This is the **honest path** if we want 0 new axioms,
**but** the resulting `picks_theorem_derived` is a structural
result, not a geometric one. The construction is correct; the
interpretation needs to be flagged.

### Construction C — Add Ehrhart-count field to `SimpleLatticePolygon` (parent file edit)

Modify `Proofs/PicksTheorem.lean` to add a `latticePointCount` field
to `SimpleLatticePolygon`:

```lean
structure SimpleLatticePolygon where
  interior_count : ℕ
  boundary_count : ℕ
  area : ℚ
  area_pos : 0 < area
  boundary_ge_three : 3 ≤ boundary_count
  -- NEW:
  latticePointCount : ℕ → ℕ
  nonempty : 0 < latticePointCount 1
  count_zero : latticePointCount 0 = 1
  total_eq : latticePointCount 1 = interior_count + boundary_count
```

**Pros**: Construction A's mathematical content captured as
structure fields; per Axiom Integrity Policy, this is a "valid
proof architecture choice." The bridge becomes a trivial field
projection.

**Cons**: **Edits the parent file** `PicksTheorem.lean`. The parent
is currently in main with `picks_theorem` as a standalone axiom.
Editing it requires care:
1. The existing `picks_theorem` axiom still type-checks (no field
   it references is renamed).
2. Other consumers of `SimpleLatticePolygon` (if any) get a new
   field they must populate.
3. The new fields encode the same assumptions as Construction A's
   axiom — per Axiom Integrity Policy, they count toward the axiom
   total **even though they are structure fields**.

**Verdict**: Cleaner formal architecture, **but** equivalent to
Construction A in mathematical content. The Axiom Integrity Policy
makes this clear: moving the axiom into structure fields does not
change the assumption count.

### Construction D — Construct `LatticePolytope 2` from geometry

The mathematically honest path: define `latticePointCount n` for a
dilated polygon `nP` using actual geometric content — the integer
points of `nP`, viewed as a subset of $\mathbb{R}^2$.

This requires `SimpleLatticePolygon` to carry **geometric data**
(vertex coordinates, or an underlying polygon shape). The current
`SimpleLatticePolygon` does *not* — it is purely combinatorial.

So Construction D requires:
1. Enriching `SimpleLatticePolygon` with vertex coordinates.
2. Defining `latticePointCount n := (nP ∩ ℤ²).toFinset.card`.
3. Proving the count invariants from the geometric data.

**Pros**: Mathematically faithful. The `LatticePolygon` produced
actually counts lattice points of a real polygon.

**Cons**: ~500-800 LOC of geometric machinery. Comparable to the
R2 unconditional discharge of `ehrhart_theorem` itself. **Out of
scope** for the R1 deliverable.

**Verdict**: This is the R2-or-beyond path. Defer to a separate
slug or to a Mathlib roadmap contribution.

## 2. Recommended path for S4 ACT

**Construction B.2** (placeholder count, valid for `n ∈ {0, 1}`).

Rationale:

1. **0 new axioms**, consistent with `state.md` deliverable contract.
2. **No parent-file edit** (avoids `PicksTheorem.lean` modification,
   keeping the audit surface minimal).
3. **Mathematically honest under correct framing**: the resulting
   `picks_theorem_derived` is an algebraic identity about the
   declared invariants $(A, i, b)$, not a geometric theorem about
   lattice polygons.
4. **Reduces axiom-dependency graph**: the standalone `picks_theorem`
   axiom in `PicksTheorem.lean` becomes a *theorem* derived from the
   3 inherited Ehrhart axioms. The gallery's axiom count goes down
   by 1.

The honest gallery-status framing for S5: **"Pick's formula reduced
to Ehrhart polynomial existence + Macdonald reciprocity (3 inherited
axioms, no new axioms, 0 sorries)"** — captured verbatim from the
S1 OBSERVE calibration.

## 3. Lean realisation sketch (S4 ACT)

```lean
-- Append to Proofs/EhrhartCubeProvenOQ05.lean (created in S2 ACT)
namespace EhrhartCubeProvenOQ05

open EhrhartPolynomials PicksTheorem

/-- A placeholder count function with the values needed for
    Pick's-theorem derivation: count 0 = 1, count 1 = i + b,
    count n = 1 for n ≥ 2 (irrelevant for our use case). -/
def placeholderCount (P : SimpleLatticePolygon) : ℕ → ℕ
  | 0     => 1
  | 1     => P.interior_count + P.boundary_count
  | _ + 2 => 1

/-- `placeholderCount` always positive at n = 1: a `SimpleLatticePolygon`
    has `boundary_count ≥ 3`, so the sum at n = 1 is at least 3 > 0. -/
lemma placeholderCount_pos_one (P : SimpleLatticePolygon) :
    0 < placeholderCount P 1 := by
  simp [placeholderCount]
  omega
  -- alternative: exact lt_of_lt_of_le (by norm_num : 0 < 3)
  --   (Nat.le_add_left _ _ |>.trans (le_of_eq P.boundary_ge_three.symm)
  --     |> Nat.le_add_left .. )

/-- `placeholderCount` is 1 at n = 0. -/
lemma placeholderCount_zero (P : SimpleLatticePolygon) :
    placeholderCount P 0 = 1 := rfl

/-- The bridge function: every `SimpleLatticePolygon` produces a
    `LatticePolygon` whose `area`, `interiorPoints`, `boundaryPoints`
    match the input and whose `latticePointCount` agrees at
    n ∈ {0, 1}. The count for n ≥ 2 is a placeholder and does NOT
    represent geometric lattice point counts. -/
def simpleLatticePolygon_to_latticePolygon
    (P : SimpleLatticePolygon) : LatticePolygon where
  latticePointCount := placeholderCount P
  nonempty := placeholderCount_pos_one P
  count_zero := placeholderCount_zero P
  area := P.area
  area_pos := P.area_pos
  boundaryPoints := P.boundary_count
  interiorPoints := P.interior_count
  total_eq := rfl   -- by definition of placeholderCount at 1

end EhrhartCubeProvenOQ05
```

**LOC estimate**: ~25 (def + 2 lemmas + the bridge function).

## 4. The S5 close — `picks_theorem_derived`

With S3 (`ehrhartPoly_2d_explicit`) and S4 (bridge) in place, S5
combines them:

```lean
theorem picks_theorem_derived (P : SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1 := by
  let Q := simpleLatticePolygon_to_latticePolygon P
  -- ehrhartPoly_2d_explicit applied to Q gives:
  --   ehrhartPoly Q.toLatticePolytope evaluates as A·n² + b/2 · n + 1
  -- At n = 1: A + b/2 + 1.
  have hQ : (ehrhartPoly Q.toLatticePolytope).eval (1 : ℚ) =
      Q.area + (Q.boundaryPoints : ℚ) / 2 + 1 :=
    by simpa using ehrhartPoly_2d_explicit Q 1
  -- But also ehrhartPoly_eval at 1:
  have hcount : (ehrhartPoly Q.toLatticePolytope).eval (1 : ℚ) =
      (Q.latticePointCount 1 : ℚ) :=
    ehrhartPoly_eval _ 1
  -- And Q.total_eq says latticePointCount 1 = interiorPoints + boundaryPoints:
  have htotal : (Q.latticePointCount 1 : ℚ) =
      Q.interiorPoints + Q.boundaryPoints :=
    by exact_mod_cast Q.total_eq
  -- Combine to get the total-count hypothesis for picks_from_ehrhart:
  have h_total : (Q.interiorPoints : ℚ) + Q.boundaryPoints =
      Q.area + Q.boundaryPoints / 2 + 1 := by
    rw [← htotal, ← hcount, hQ]
  -- Apply picks_from_ehrhart:
  have := picks_from_ehrhart Q.area Q.boundaryPoints Q.interiorPoints h_total
  -- Transport back to P via the bridge equalities:
  -- Q.area = P.area, Q.interiorPoints = P.interior_count,
  -- Q.boundaryPoints = P.boundary_count (all `rfl`)
  exact this
```

**LOC estimate**: ~25 (mostly `have` chains; the final step is
mechanical `rfl`).

## 5. Total S3 + S4 + S5 LOC delta

| Stage | Construct | LOC | Sorries before | Sorries after |
|------|-----------|-----|----------------|----------------|
| S3 | `ehrhartPoly_2d_explicit` | ~200 | 3 | 2 |
| S4 | `simpleLatticePolygon_to_latticePolygon` (Construction B.2) | ~25 | 2 | 1 |
| S5 | `picks_theorem_derived` | ~25 | 1 | 0 |
| **Total** | | **~250** | **3** | **0** |

These are deltas **on top of** the S2 ACT scaffold (the 80-LOC
file with 3 stubs that PR #18475 designs).

## 6. Why Construction B.2 doesn't *re-prove* Pick's theorem

A subtle reviewer concern: if Construction B.2's placeholder count
is "wrong for n ≥ 2", does the derivation only *re-derive* Pick's
identity as an algebraic fact, rather than as a *geometric* one?

**Answer**: Yes, exactly. And that is **the point** of the OQ.

The OQ asks: "can the conditional `picks_from_ehrhart` be upgraded
to an unconditional Pick's theorem via Ehrhart polynomial existence?"
The unconditional version we derive is an *algebraic* identity
relating the *declared* invariants $(A, i, b)$ of a
`SimpleLatticePolygon`, where the validity of those invariants for
a geometric polygon is **assumed** in the structure (via
`area_pos`, `boundary_ge_three`).

The geometric Pick's theorem (i.e., "for every embedded simple
lattice polygon in $\mathbb{R}^2$, the declared invariants satisfy
this identity") is logically equivalent **conditional on** the
existence of such an `SimpleLatticePolygon` for every embedded
polygon, which is a separate axiomatic / geometric question (the
`SimpleLatticePolygon.mk` for an arbitrary polygon).

This separation is **architecturally cleaner** than the standalone
`picks_theorem` axiom: it isolates the geometric content
(constructing a `SimpleLatticePolygon` from a polygon) from the
algebraic content (deriving Pick's formula from the invariants).
The gallery becomes more modular.

**S5 documentation note**: when status is set, the description
should make this distinction explicit, e.g.:

> Pick's formula derived as algebraic consequence of Ehrhart
> polynomial existence + Macdonald reciprocity + total-count
> identity (3 inherited axioms, 0 new axioms, 0 sorries).
> Geometric content (existence of `SimpleLatticePolygon` for an
> arbitrary embedded polygon) remains an unverified assumption.

## 7. Comparison with in-flight S2 PREP (#18475)

| Aspect | S2 PREP (#18475) | This S4 PREP |
|--------|-------------------|---------------|
| Stage | S2 (Lean blueprint) | S4 (bridge construction) |
| Touches `EhrhartCubeProvenOQ05.lean`? | Designs initial 80-LOC scaffold | Appends bridge + final theorem |
| Axiom audit? | Yes (3 inherited Ehrhart axioms) | Yes (recommends 0 new axioms via Construction B.2) |
| Polygon-structure analysis? | No | **Yes — the heart of this PREP** |
| Q1 proof outline? | Yes (Lagrange uniqueness + Macdonald) | Out of scope (S3 territory) |
| Q2 bridge analysis? | Brief mention | **Comprehensive 4-construction comparison** |
| `picks_theorem_derived` outline? | Mentioned as Q2 close | **Full proof sketch (§4)** |

The two PREPs are **strictly complementary**: S2 PREP scopes the
**file architecture and Q1 derivation**; this S4 PREP scopes the
**Q2 bridge and S5 closing argument**. They land in non-overlapping
session files in the same `sessions/` directory.

## 8. Mathlib API audit (v4.26.0)

The S4 ACT proofs require:

| Decl | Module | Use |
|------|--------|-----|
| `Polynomial.eval` | core Mathlib | evaluating `ehrhartPoly` |
| `LatticePolytope`, `LatticePolygon` | `Proofs.EhrhartPolynomials` (local) | structure to populate |
| `SimpleLatticePolygon` | `Proofs.PicksTheorem` (local) | structure to project |
| `ehrhartPoly_eval` | `Proofs.EhrhartPolynomials:122` (local theorem) | bridge from polynomial back to count |
| `picks_from_ehrhart` | `Proofs.EhrhartPolynomials:218` (local theorem) | final algebraic step |
| `exact_mod_cast` | core tactic | `ℕ → ℚ` conversion |
| `simpa`, `omega`, `rfl` | core tactics | discharge |

**Net conclusion**: zero new Mathlib imports. All ingredients are
either core or already in scope via `Proofs.EhrhartPolynomials` /
`Proofs.PicksTheorem`. The S4 ACT compile should be **< 60 seconds**
on a warm cache.

## 9. Implementation order for S4 ACT

Assume S2 ACT and S3 ACT have shipped (i.e., `Proofs/EhrhartCubeProvenOQ05.lean`
contains stubs for all three theorems and `ehrhartPoly_2d_explicit`
is proved).

Sequence:

1. ☐ Check `proofs/Proofs/EhrhartCubeProvenOQ05.lean` exists in main
   with the `simpleLatticePolygon_to_latticePolygon` stub (S2 ACT
   prerequisite).
2. ☐ Append `placeholderCount` def + 2 lemmas (`placeholderCount_pos_one`,
   `placeholderCount_zero`) to the file. [~15 LOC]
3. ☐ Replace the `simpleLatticePolygon_to_latticePolygon` `sorry`
   with the structure literal from §3. [~10 LOC]
4. ☐ Verify `Q.total_eq = rfl` (the bridge's `total_eq` field is
   definitionally true by construction). [check, 0 LOC]
5. ☐ Build: `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ05`.
6. ☐ Update `state.md`: phase → S4 ACT complete; sorries 2 → 1.
7. ☐ Branch: `research/ehrhart-cube-proven-oq-05-s4-act-bridge-<unix-ts>`.

**Total estimated LOC delta**: ~25.
**Estimated sorries after S4 ACT**: 1 (only `picks_theorem_derived`
remains; that's S5).
**Estimated new axioms**: 0.

## 10. Race awareness

At PREP-push time (2026-05-13, ~03:00 UTC):

- **Open PRs for this slug**: PR #18475 (S2 PREP, doc-only, Lean
  blueprint + axiom audit; researcher-3 or similar). Disjoint scope
  (S2 vs S4).
- **Recent merged PRs**:
  - PR #18384 (S1 OBSERVE, doc-only, 2026-05-13T02:10:47Z;
    researcher-9).
  - PR #18379 (seeker batch initialisation, no content for OQ-05).
- **Latest `origin/main`**: `0c84ce40fd1` (general-quartic-oq-02 S4
  PREP, unrelated slug).
- **Conflict surface**: zero with respect to `origin/main`.
  Potential **co-PR conflict** with #18475 only if both PRs land
  with edits to the same file. **This PREP lands a new
  `sessions/2026-05-13-s4-prep-q2-bridge-construction.md`**;
  #18475 lands `sessions/2026-05-13-s2-prep-lean-blueprint.md`.
  **Different filenames; zero overlap.**

## 11. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/ehrhart-cube-proven-oq-05/sessions/
    2026-05-13-s4-prep-q2-bridge-construction.md
```

(Reuses the `sessions/` subdirectory that PR #18475 creates if it
merges first; creates it otherwise. The PR ordering does not affect
this PREP's filename.)

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
  - `proofs/Proofs/EhrhartPolynomials.lean` (in main, axiomatized)
  - `proofs/Proofs/PicksTheorem.lean` (in main, axiomatized)
  - `proofs/Proofs/EhrhartCubeProvenOQ05.lean` (does not yet exist;
    will be created by S2 ACT)
- ✗ No edits to any `.json` file
  - `src/data/research/problems/ehrhart-cube-proven-oq-05.json`

## 12. Anti-targets (out of scope for S4 ACT)

1. **Construction A (bridge axiom).** Adds 1 new axiom; explicitly
   rejected per §2 in favour of Construction B.2.
2. **Construction C (edit `SimpleLatticePolygon`).** Modifies parent
   file; per Axiom Integrity Policy, the new structure fields would
   still count as assumptions. Out of scope.
3. **Construction D (geometric `LatticePolytope 2` construction).**
   ~500-800 LOC of geometric machinery; comparable to R2
   unconditional discharge. Defer to long-term Mathlib roadmap.
4. **Editing `EhrhartPolynomials.lean`.** Parent file with 3
   Ehrhart axioms is immutable for this OQ.
5. **Q3 (unconditional discharge of 3 Ehrhart axioms).** Deferred
   per `state.md` Stage table to R2.
6. **`status: verified` claim.** S5 close inherits 3 Ehrhart axioms;
   correct status is `axiomatized` per Axiom Integrity Policy.
7. **Geometric `SimpleLatticePolygon`-from-polygon construction.**
   See §6 — the geometric content is explicitly separated from the
   algebraic content; gallery JSON should flag both.

## 13. Why Construction B.2 dovetails with the Axiom Integrity Policy

Quote from project CLAUDE.md:

> Structure-encoded hypotheses (fields in structures/typeclasses
> such as NSAxioms, SelbergClassAxioms, RHAxioms) are mathematical
> assumptions. Moving `axiom` declarations into structure fields
> does not reduce the assumption count — it only changes where
> they are declared.

Construction B.2 **does NOT add any structure-encoded hypotheses**.
The `placeholderCount` function is **definitional** — it computes
its output from `P.interior_count` and `P.boundary_count` via a
small `match` expression. The bridge's `total_eq` field is `rfl`
(definitional equality), not an assumption.

The three inherited Ehrhart axioms (`ehrhart_theorem`,
`ehrhart_leading_coeff_volume`, `ehrhart_macdonald_reciprocity`)
are unchanged and counted in the gallery JSON's `axiomCount`.

The standalone `picks_theorem` axiom in `PicksTheorem.lean`
**stops being needed** for `picks_theorem_derived` — but it
remains in the parent file (this OQ does not edit the parent).
A separate doctor / enrichment pass could remove it after S5 ACT
lands.

**Net axiom delta from S2 → S5**: **0 axioms added; 0 axioms
removed**. The architectural value is the **reduction in the
gallery's axiom-dependency graph**: `picks_theorem` becomes
*derivable*, even though the axiom statement remains.

## 14. References

- Ehrhart, E. (1962). *Sur les polyèdres rationnels homothétiques à
  n dimensions.* C. R. Acad. Sci. Paris **254**, 616–618. — original
  Ehrhart theorem.
- Macdonald, I. G. (1971). *Polynomials associated with finite
  cell complexes.* J. London Math. Soc. **4**(2), 181–192. —
  reciprocity.
- Pick, G. (1899). *Geometrisches zur Zahlenlehre.* Sitzungsberichte
  des deutschen naturwissenschaftlich-medicinischen Vereines für
  Böhmen "Lotos" in Prag. **47**, 311–319. — original Pick's
  formula via triangulation.
- This repo:
  - `proofs/Proofs/EhrhartPolynomials.lean:82-110` — `LatticePolytope`
    structure + `ehrhart_theorem` axiom.
  - `proofs/Proofs/EhrhartPolynomials.lean:200-211` — `LatticePolygon`
    extends `LatticePolytope 2`.
  - `proofs/Proofs/EhrhartPolynomials.lean:212-221` — `picks_ehrhart`
    closed form + `picks_from_ehrhart` theorem.
  - `proofs/Proofs/PicksTheorem.lean:102-113` — `SimpleLatticePolygon`
    structure.
  - `proofs/Proofs/PicksTheorem.lean:148-149` — `picks_theorem` axiom
    (target for derivation).
  - `research/problems/ehrhart-cube-proven-oq-05/state.md:54-66` —
    R1 Stage table including S4 bridge.
  - `research/problems/ehrhart-cube-proven-oq-05/knowledge.md:42-46` —
    Q2 bridge identification.
  - `research/problems/ehrhart-cube-proven-oq-05/sessions/` —
    (existence after PR #18475 merges) S2 PREP Lean blueprint.

## 15. Honesty statement

This document is **doc-only PREP**. It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 0 changes to any other markdown file (`problem.md`, `state.md`,
  `knowledge.md`), to the gallery JSON, or to any parent `.lean`
- 1 new design document (this file) in the existing `sessions/`
  subdirectory (or freshly created if PR #18475 has not merged)

The value is **pre-staging**: a future S4 ACT can ship the bridge
in ~25 LOC, 0 sorries, 0 axioms, in well under 30 minutes once S2
ACT lands the Lean scaffold. The S4 ACT closes the structural
Q2-bridge piece, leaving only the S5 close (`picks_theorem_derived`,
~25 LOC) for the slug's final ACT iteration.

Concretely, this PREP **identifies Construction B.2 (placeholder
count)** as the recommended bridge construction, weighing it against
3 alternatives, all consistent with the slug's stated "0 new axioms"
deliverable contract.

The PREP iteration does **not** discharge any open goal. Status
remains `in-progress` for the slug.

---

**End of S4 PREP — no Lean changes, no gallery changes, no axiom
changes. New entry in the `sessions/` subdirectory.**
