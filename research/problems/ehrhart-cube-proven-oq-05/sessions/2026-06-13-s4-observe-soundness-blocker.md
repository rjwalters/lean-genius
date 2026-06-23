# S4 OBSERVE — soundness blocker in the bridge/closing target

**Researcher**: researcher-5
**Date**: 2026-06-13
**Phase**: OBSERVE (re-scoping the S4/S5 plan)
**Base**: origin/main @ fb829e819f7
**Lean changes**: none (build-free; Docker daemon down — see §7)

## TL;DR

The recommended S4 path (Construction B.2 "placeholder count", from
`sessions/2026-05-13-s4-prep-q2-bridge-construction.md`) is **unsound**,
and more fundamentally the S5 target `picks_theorem_derived` is, *as
currently stated*, a **universally false proposition**. The root cause
is shared with a pre-existing defect in the parent file: the
`PicksTheorem.SimpleLatticePolygon` structure is **under-constrained**,
so the universally-quantified Pick identity is false on it.

Consequence: OQ-05's stated "0 new axioms, 0 sorries" deliverable
contract is **not achievable in a consistent extension**. A sound close
requires adding at least one assumption (a geometric-realizability
hypothesis / field). The honest gallery status for the eventual S5
deliverable is therefore `axiomatized`, not `verified`.

## 1. The structure is under-constrained

`proofs/Proofs/PicksTheorem.lean:102-112`:

```lean
structure SimpleLatticePolygon where
  interior_count : ℕ
  boundary_count : ℕ
  area : ℚ
  area_pos : 0 < area
  boundary_ge_three : 3 ≤ boundary_count
```

The only constraints are `0 < area` and `3 ≤ boundary_count`. There is
**no field linking `area` to `(interior_count, boundary_count)`** via
Pick's identity, and **no geometric-realizability witness** (no vertex
data, no underlying lattice polytope, no count function). The structure
docstring claims "The axioms ensure these are consistent with geometric
reality," but there are no such axioms/fields — the claim is not backed
by the definition.

Therefore the anonymous constructor admits geometrically-impossible
instances, e.g.

```lean
def badPolygon : SimpleLatticePolygon :=
  ⟨1, 3, 1000, by norm_num, by norm_num⟩
  -- interior_count = 1, boundary_count = 3, area = 1000
```

This typechecks: `area_pos` is `0 < 1000` and `boundary_ge_three` is
`3 ≤ 3`. Pick's identity for these data would require
`area = 1 + 3/2 - 1 = 3/2`, but `area = 1000`.

## 2. The S5 target is a false proposition

The S5 goal (`EhrhartCubeProvenOQ05.lean:158-160`) is

```lean
theorem picks_theorem_derived (P : SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1
```

Instantiating at `badPolygon` gives `(1000 : ℚ) = 3/2`, which is false.
A `∀`-statement with a concrete counterexample is **false**, so a
`sorry`-free, axiom-free proof of `picks_theorem_derived` **cannot
exist** in a consistent logic. Any apparent completion must therefore
be deriving `False` somewhere inside its supporting construction (see
§3). This is not a difficulty of the discharge — it is an impossibility
given the current statement.

### 2a. The same defect already sits in the parent axiom

`proofs/Proofs/PicksTheorem.lean:148-149`:

```lean
axiom picks_theorem (P : SimpleLatticePolygon) :
    A(P) = picks_formula i(P) b(P)
```

This axiom is the *same* universally-quantified Pick identity over the
*same* under-constrained structure. Instantiating it at `badPolygon`
yields `(1000 : ℚ) = 3/2`, from which `False` follows:

```lean
-- BUILD-UNVERIFIED sketch (Docker down): expected to typecheck
example : False := by
  have h := picks_theorem badPolygon   -- (1000 : ℚ) = 1 + 3/2 - 1
  norm_num [picks_formula] at h
```

So the gallery's existing `picks_theorem` axiom is, as stated,
**inconsistent** — not merely "an assumption," but a *false*
universally-quantified assumption. This is a pre-existing integrity
issue independent of OQ-05; it should be routed to the auditor/mechanic
(see §6). OQ-05's whole premise ("derive `picks_theorem` from the
Ehrhart axioms, removing the standalone axiom") inherits the defect:
you cannot soundly *derive* a false statement.

## 3. Why Construction B.2 fails specifically

The S4 PREP recommends a placeholder count
(`sessions/2026-05-13-s4-prep-q2-bridge-construction.md` §2-3):

```lean
def placeholderCount (P : SimpleLatticePolygon) : ℕ → ℕ
  | 0     => 1
  | 1     => P.interior_count + P.boundary_count
  | _ + 2 => 1
```

Two independent problems, both fatal:

1. **Non-polynomial count vs. `ehrhart_theorem`.** The value sequence
   `1, i+b, 1, 1, 1, …` is not the value sequence of any degree-2
   polynomial (a degree-≤2 polynomial equal to `1` at `n = 0,2,3,4`
   is the constant `1`, contradicting both `natDegree = 2` and the
   value `i+b` at `n=1` unless `i+b=1`, which then contradicts
   `natDegree = 2`). But the bridge feeds this count into a
   `LatticePolygon`, and `ehrhart_theorem 2 Q`
   (`EhrhartPolynomials.lean:114-116`) asserts the existence of a
   degree-2 polynomial matching the count at **all** `n`. That
   existential is **false** for the placeholder count, so this
   instantiation of the axiom is itself inconsistent — `False` is
   derivable from `ehrhartPoly_degree Q` + `ehrhartPoly_eval Q` at
   `n = 2, 3`.

2. **The PREP predates two required fields.** The 2026-05-13 PREP's
   bridge literal (§3) supplies only
   `latticePointCount / nonempty / count_zero / area / area_pos /
   boundaryPoints / interiorPoints / total_eq`. The current
   `LatticePolygon` (`EhrhartPolynomials.lean:211-234`, after the
   2026-06-09 AXIOM-FIX and the S3 `volume_eq_area` addition) **also
   requires**:
   - `volume : ℚ`, `volume_pos : 0 < volume` (inherited from
     `LatticePolytope`),
   - `volume_eq_area : volume = area`,
   - `interior_at_one : ∀ ic, interiorCount toLatticePolytope ic →
     ic 1 = interiorPoints`.

   `volume`/`volume_pos`/`volume_eq_area` are dischargeable (set
   `volume := area`). But `interior_at_one` is a genuine proof
   obligation: it must show `ic 1 = interiorPoints` for *every*
   Macdonald-compatible `ic`, i.e. `(ehrhartPoly Q).eval (-1) =
   interiorPoints`. For the placeholder polytope this is only
   "provable" by explosion from the inconsistent `ehrhart_theorem`
   instantiation of problem (1) — which is exactly the unsoundness,
   surfacing as a field obligation.

So Construction B.2 does not yield a sound `LatticePolygon`; it yields
an inconsistent one, and the inconsistency is what would let
`picks_theorem_derived` (a false statement, §2) appear "proved."

## 4. Sound resolution — the deliverable must carry an assumption

To make `picks_theorem_derived` a **true** (hence soundly provable)
statement, `P` must be constrained to geometrically-realizable data.
Equivalent honest options:

- **Add a realizability field/hypothesis** to `SimpleLatticePolygon`
  (e.g. a witness that `(i,b,A)` arise from an actual lattice polygon,
  or directly the total-count identity `count 1 = i + b` together with
  the Ehrhart data). This is Construction C of the S4 PREP. Per the
  Axiom Integrity Policy, a structure-encoded hypothesis **is** an
  assumption and counts toward the axiom total.

- **Restate the target conditionally**:
  `picks_theorem_derived (P) (h : realizable P) : …`. The hypothesis
  `h` is the assumption.

- **Bridge axiom** (Construction A): assume every `SimpleLatticePolygon`
  arises from a `LatticePolygon`. Adds 1 axiom.

All three add **≥ 1 assumption**. The 2026-05-13 PREP's claim that
Construction B.2 achieves "0 new axioms" is therefore mistaken: B.2
achieves zero *declared* axioms only by routing through an inconsistent
construction, which is strictly worse than an honest assumption.

### Re-scoped deliverable

OQ-05 should target, and the gallery JSON should state:

> Pick's formula derived from Ehrhart polynomial existence + Macdonald
> reciprocity + a geometric-realizability assumption on the polygon
> (3 inherited Ehrhart axioms + 1 realizability assumption, 0 sorries).
> Status: `axiomatized`.

This is a genuine architectural improvement over the standalone
`picks_theorem` axiom (it isolates the geometric content from the
algebraic content and grounds the algebra in Ehrhart theory), but it is
**not** a 0-assumption result, and it is **not** `verified`.

## 5. What is NOT affected

- `EhrhartCubeProven.lean` (the parent gallery entry,
  `ehrhart-cube-proven`) is genuinely self-contained: it counts the
  unit cube via `Fintype.card_fun`, never constructs a
  `SimpleLatticePolygon`, and its `square_picks_general` is a concrete
  `ring` identity about explicit numbers. Its `verified / 0 axioms`
  status is correct.
- `ehrhartPoly_2d_explicit` (S3, the Q1 content) is unaffected by this
  finding: it is a statement about an *arbitrary* `LatticePolygon`'s
  Ehrhart polynomial and uses only the three Ehrhart axioms. The
  unsoundness enters only when one tries to *manufacture* a
  `LatticePolygon` from the slim `SimpleLatticePolygon` data (the S4
  bridge).

## 6. Recommendations / handoff

1. **OQ-05 (this slug)**: abandon Construction B.2. Adopt Construction
   C or a conditional restatement (§4). Update the S5 deliverable
   framing to `axiomatized` with the realizability assumption stated.
   This requires editing `EhrhartCubeProvenOQ05.lean` (and possibly
   `PicksTheorem.lean`) and a Docker build — deferred until the build
   route returns (§7).
2. **Parent `picks_theorem` axiom**: flag the inconsistency of
   `axiom picks_theorem` over the under-constrained
   `SimpleLatticePolygon` (§2a) to the **auditor / mechanic**. The fix
   (constrain the structure, or restate the axiom conditionally) is a
   parent-file edit + build, out of this slug's scope.
3. **Do not** set OQ-05 to `verified` at any point; the eventual close
   is `axiomatized`.

## 7. Honesty / verification status

- **Build-free session.** No `.lean` file is modified. Only research
  markdown (this file, `knowledge.md`, `state.md`) changes.
- **Docker daemon is DOWN** at session time (`docker info` hangs/timed
  out; disk recovered to 14% used). The `example : False` sketches in
  §2a/§3 are therefore **build-unverified**. They are, however,
  elementary: instantiating a `∀` with a concrete counterexample and a
  `norm_num`. The mathematical argument (a universally-quantified Pick
  identity over an under-constrained structure is false) does not
  depend on Lean and is robust.
- Recommend the auditor confirm the `example : False` snippets compile
  once the Docker build route is restored.

## 8. Files referenced

- `proofs/Proofs/PicksTheorem.lean:102-112` — `SimpleLatticePolygon`
  (under-constrained).
- `proofs/Proofs/PicksTheorem.lean:138-149` — `picks_formula`,
  `picks_theorem` axiom.
- `proofs/Proofs/EhrhartCubeProvenOQ05.lean:143-160` — S4 bridge stub,
  S5 `picks_theorem_derived` stub.
- `proofs/Proofs/EhrhartPolynomials.lean:82-94` — `LatticePolytope`.
- `proofs/Proofs/EhrhartPolynomials.lean:114-116` — `ehrhart_theorem`.
- `proofs/Proofs/EhrhartPolynomials.lean:211-234` — `LatticePolygon`
  (current field set, incl. `volume_eq_area`, `interior_at_one`).
- `sessions/2026-05-13-s4-prep-q2-bridge-construction.md` — the S4 PREP
  whose Construction B.2 this OBSERVE supersedes.

---

**End of S4 OBSERVE — no Lean changes, no gallery JSON changes. New
session file + `knowledge.md`/`state.md` updates. Finding: the S4/S5
target is unsound as stated; OQ-05 needs ≥1 realizability assumption,
and the parent `picks_theorem` axiom is inconsistent and should be
audited.**
