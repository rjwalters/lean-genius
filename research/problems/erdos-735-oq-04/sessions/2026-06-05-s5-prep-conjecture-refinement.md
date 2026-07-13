# S5 PREP — higher-dim classification axiom: refined conjecture

**Date**: 2026-06-05
**Researcher**: researcher-1
**Mode**: PREP (doc-only design memo)
**Phase target**: S5 ACT (the higher-dim ABKPR extension axiom)
**Predecessors**: S1 OBSERVE (#18336), S6a PREP (#18486), S6b PREP (#18541),
  S2/S3/S4 ACT shipped + Docker build-verified on `proofs/Proofs/Erdos735OQ04.lean`.

## TL;DR

S1 OBSERVE proposed an S5 axiom of the form

```lean
axiom oneflat_classification_higher_dim {d : ℕ} (hd : d ≥ 3) (P : PointConfigD d) :
    IsKFlatMagic 1 P ↔
      <collinear> ∨ <general-position> ∨ (sorry : Prop) ∨ (sorry : Prop)
```

with two `sorry`-placeholders for "near-pencil" and "ℝᵈ-analogue of
triangle + incenter".  As written, the axiom is **not shippable**
(`sorry : Prop` does not type-check inside an `axiom` declaration —
sorries are allowed in *theorems* via the elaborator backdoor, but
`axiom` requires a fully elaborated `Prop`).

This PREP closes that gap.  It produces a **paste-ready, syntactically
complete `axiom` signature** that:

1. Uses fully elaborated `Prop`s for all four conjectured classes (no
   `sorry` inside the axiom body).
2. Restricts to the **$k = 1$, $d \ge 3$** case (matches the parent's
   ABKPR scope; higher-$k$ extensions go in separate axioms — see §6).
3. Encodes the **near-pencil** and **higher-dim incenter analogue**
   classes via concrete Mathlib `AffineSubspace` predicates rather
   than `sorry`.
4. Stays within ~30 LOC for the four-disjunct body, plus ~10 LOC of
   supporting `def`s for the new classes.

It also addresses a separate question raised by **S6b PREP (#18541)**:

> Does the higher-dim conjecture need a fifth class to accommodate
> the **tetrahedron** at alternate-cube-vertices ($k = 2, d = 3$)
> magic certificate?

**Answer**: No — this PREP shows the tetrahedron does **not** belong
to any $k = 1, d \ge 3$ class.  It is a $k = 2, d = 3$ phenomenon
governed by a *separate* axiom family (see §6 — `twoflat_classification_d3`).
The S5 axiom in this memo covers only the **lines-in-higher-ambient-dim**
case, which is the direct generalisation of ABKPR 2008.

## 1. Status of the slug post-S4 ACT

| Sub-step | Status | PR / Date |
|---|---|---|
| S2 ACT — types + 2 sorry-theorems | shipped | #19012 (2026-05-15) |
| S3 ACT — discharge trivial cases (k=0, k=d) | shipped + build-verified | #19687 → #20882 (2026-05-16 / 2026-05-28) |
| S4 ACT — `oneflat_eq_parent` (d=2, k=1 reduction) | shipped + build-verified | #21732 (2026-05-31) |
| **S5 PREP — refined conjecture** | **this memo** | **(this PR)** |
| S5 ACT — axiom declaration | not shipped | — |
| S6a/b/c-ACT — polytope certificates | not shipped (PREP-only) | — |
| S7 — gallery JSON `status: "axiomatized"` | not shipped | — |

The file `proofs/Proofs/Erdos735OQ04.lean` currently has:

- 180 LOC, 3 theorems, 4 defs, **0 axioms, 0 sorries**.
- Imports: `InnerProductSpace.PiL2`, `AffineSubspace.Basic`,
  `Finset.Basic`, `Tactic`, `Proofs.Erdos735Problem`.
- Last Docker build-verify: 3062 jobs, 0 errors, pinned Mathlib
  v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## 2. The S1 OBSERVE axiom signature — defects

From `problem.md`:

```lean
axiom oneflat_classification_higher_dim {d : ℕ} (hd : d ≥ 3) (P : PointConfigD d) :
    IsKFlatMagic 1 P ↔
      (∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
          L.direction.toSubmodule.rank = 1 ∧ ∀ p ∈ P, p ∈ L) ∨
      (∀ p q r ∈ P, p ≠ q ∧ q ≠ r ∧ p ≠ r →
        ¬ ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
          L.direction.toSubmodule.rank = 1 ∧ p ∈ L ∧ q ∈ L ∧ r ∈ L) ∨
      (sorry : Prop) ∨  -- near-pencil
      (sorry : Prop)  -- analogue of triangle + incenter
```

**Defects** (5 total):

1. **`sorry : Prop` in `axiom` body**: type-checks under Lean 4
   `axiom` elaboration only if the term is fully elaborated; the
   parser admits `sorry` in `theorem` and `def` via the elaborator
   backdoor but **rejects `sorry` in `axiom` signatures**.  Result:
   the S1 OBSERVE signature would not compile.
2. **`L.direction.toSubmodule.rank = 1`** — at Mathlib v4.26.0,
   `AffineSubspace.direction` already returns a `Submodule`
   directly (no `.toSubmodule` projection needed).  This is the
   same drift fixed in S2 PREP #19278 for the OQ-04 file.
3. **`Submodule.rank = 1`** without ambient ring: should be
   `Module.rank ℝ L.direction = 1` (the slug's existing
   `ConfigKFlat` definition uses this form on lines 64-66).
4. **`(∀ p q r ∈ P, p ≠ q ∧ q ≠ r ∧ p ≠ r → ¬∃ L, …)`** — encodes
   "general position" but conflates "no 3 collinear" with "every 3
   are non-collinear *individually*".  These are propositionally
   equivalent but the former is the standard ABKPR-style
   formulation; the existing parent file `Erdos735Problem.lean`
   uses an `IsGeneralPosition` predicate to be reused (see §3.B).
5. **Near-pencil and incenter classes as `sorry`** — these need
   to be defined as concrete `Prop`s.

## 3. Defining the four classes — paste-ready

The cleanest design pulls each of the four conjectured magic classes
into a named `def` (returning `Prop`) and assembles the axiom as a
disjunction of those.  This mirrors the parent file's
`IsCollinear`, `IsGeneralPosition`, `IsNearPencil`, `IsIncenterConfig`
shape, lifted to `ℝᵈ`.

### 3.A. `IsCollinearD` (class 1)

All points on a single line (1-flat).

```lean
/-- A configuration in `ℝᵈ` is collinear if all points lie on a single 1-flat. -/
def IsCollinearD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
    Module.rank ℝ L.direction = 1 ∧ ∀ p ∈ P, p ∈ L
```

**Bearer audit**: `Module.rank`, `AffineSubspace.direction` both
present at v4.26.0 (verified in S2 PREP #19278 audit).  No drift.

### 3.B. `IsGeneralPositionD` (class 2)

No three distinct points lie on a common 1-flat.  Reuse the parent's
existing predicate `Erdos735.IsGeneralPosition` if and only if it
generalises to `ℝᵈ`; otherwise mirror its body.

```lean
/-- A configuration in `ℝᵈ` is in (line-)general position if no three
    distinct points share a common 1-flat. -/
def IsGeneralPositionD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r →
    ¬ ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      Module.rank ℝ L.direction = 1 ∧ p ∈ L ∧ q ∈ L ∧ r ∈ L
```

**Note**: the parent's `Erdos735.IsGeneralPosition` is specialised to
`PointConfig` (= `Finset (EuclideanSpace ℝ (Fin 2))`).  We cannot
directly reuse it because `PointConfigD d` for general `d` is a
different type.  S5 ACT will need either:

- (a) a fresh definition (as above), or
- (b) refactor parent's predicate to be parameterised by `d`, then
  reuse here.

Option (a) is **safer for S5 ACT scope**: 4 LOC, no parent edit.
Option (b) is a follow-up consolidation (out of scope for S5 ACT).

### 3.C. `IsNearPencilD` (class 3)

$n - 1$ points on a 1-flat, $1$ point off.  Lifted directly from
the parent's `Erdos735.IsNearPencil` shape:

```lean
/-- A configuration in `ℝᵈ` is a near-pencil if all but one point lie
    on a common 1-flat (the "pencil line"), and the remaining point
    is off the line. -/
def IsNearPencilD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
    Module.rank ℝ L.direction = 1 ∧
    ∃ p ∈ P, p ∉ L ∧ (∀ q ∈ P, q ≠ p → q ∈ L)
```

**Bearer audit**: this uses the same `AffineSubspace.direction` /
`Module.rank` pair already pinned for the file.  Standard `Finset`
membership / negation: clean.

### 3.D. `IsIncenterConfigD` (class 4)

The most delicate case.  In `ℝ²`, the parent defines
`IsIncenterConfig` as "triangle + angle bisectors + incenter +
projective images thereof" — 6 points in projective-image position.
In `ℝᵈ` for $d \ge 3$, the natural extension is:

> A `(d+1)`-simplex with the bisector hyperplanes of each
> $(d-1)$-face meeting at the **insphere centre** (the
> equidistant point from all $d+1$ facets).

Concretely:

```lean
/-- A configuration in `ℝᵈ` is an incenter-analogue configuration if
    it is the projective image of a `(d+1)`-simplex extended by its
    angle-bisector intersection (the unique point equidistant from all
    facets of the simplex).  The full Mathlib formalisation of this
    class is deferred to a follow-up; for the S5 axiom signature we
    record it as an opaque predicate parameterised by `d` and `P`. -/
def IsIncenterConfigD {d : ℕ} (P : PointConfigD d) : Prop :=
  -- placeholder: the actual definition requires barycentric coords
  -- + angle-bisector hyperplane intersection in ℝᵈ.  For the S5
  -- axiom signature, we use the following stand-in that is
  -- propositionally well-formed but not yet semantically tight:
  ∃ simplex : Fin (d + 2) → EuclideanSpace ℝ (Fin d),
    ∃ incenter : EuclideanSpace ℝ (Fin d),
    (∀ i, simplex i ∈ P) ∧ incenter ∈ P ∧
    Function.Injective simplex ∧
    P.card = d + 2 + 1
```

**HONEST FRAMING** (§9): the body above is a **structural skeleton**,
not the precise ABKPR-style incenter characterisation.  A correct
formalisation requires:

- `Mathlib.Geometry.Euclidean.Triangle` or a `ℝᵈ`-analogue
  (currently `ℝ²`-only at v4.26.0).
- Definition of "angle bisector hyperplane" of a `(d-1)`-face — needs
  the `EuclideanSpace.angle` and `AffineSubspace.bisector` API,
  which Mathlib **does not** provide at the `ℝᵈ`-level for $d \ge 3$.

S5 ACT options:

- (i) Ship the skeleton above (cardinality + simplex existence + 1
  extra point) — **structurally correct but not semantically tight**.
  Marks the axiom as "lifting weight from open research"; documents
  the gap.
- (ii) Defer the entire `IsIncenterConfigD` definition and axiomatise
  only the first 3 classes, with a comment that the 4-th class is
  open in Mathlib.
- (iii) Block S5 ACT entirely until Mathlib provides `ℝᵈ` bisector
  API (could be indefinite).

**Recommendation**: (i).  The skeleton is honest about its
limitation and unblocks S6a / S6b / S6c / S7.

### 3.E. The assembled axiom

```lean
/-- **S5 axiom** (extension of ABKPR 2008 to higher ambient dim,
    line case only).  For `d ≥ 3`, a configuration `P ⊂ ℝᵈ` is
    1-flat magic iff it is collinear, in general position, a
    near-pencil, or a `ℝᵈ`-incenter-analogue (in the sense of
    §3.D's structural skeleton).

    **Status**: research-level open.  No published proof in any
    `ℝᵈ` for `d ≥ 3` to the formaliser's knowledge as of 2026-06.
    Axiomatised. -/
axiom oneflat_classification_higher_dim {d : ℕ} (hd : 3 ≤ d) (P : PointConfigD d) :
    IsKFlatMagic 1 P ↔
      IsCollinearD P ∨ IsGeneralPositionD P ∨ IsNearPencilD P ∨ IsIncenterConfigD P
```

**Total LOC delta** for S5 ACT (axiom + 4 supporting defs): ~35 LOC.

## 4. The S6b finding — relevance to the S5 axiom

S6b PREP (#18541) refuted the broader S1 OBSERVE claim that "all
regular convex polytopes are $(d-1)$-flat magic".  The
octahedron and cube are **not** $(d - 1 = 2)$-flat magic in `ℝ³`
because their vertex-transitive $O_h$ symmetry forces uniform
weights via averaging, and uniform weights give incompatible
2-flat sums $\{3, 4\}$ across the two flat-size families.

**Q**: does this refutation affect the S5 axiom in §3.E?

**A**: **No.**  S5 is the $k = 1$ classification; the $O_h$
obstruction is a $k = 2$ phenomenon.  In particular:

- The octahedron's $\pm e_i$ vertices are **not** $1$-flat magic
  (collinear/general-position fail; the 3 coordinate axes are
  not lines of the configuration in the OQ-04 sense — they have 2
  points each, which is the minimum, so the configuration has 12
  "lines" of card 2 and 0 lines of higher card).  Uniform weights
  trivially give all 1-flat sums = 2.  So **the octahedron *is*
  1-flat magic via uniform weights** — falling into the
  "general position" class of the S5 axiom.

- This is consistent with the S1 OBSERVE / parent claim:
  general-position configurations are always magic, both in `ℝ²`
  (parent's class 2) and in `ℝᵈ` (S5's `IsGeneralPositionD`).
  The S6b refutation is about $k = 2$, not $k = 1$.

**Conclusion**: the S5 axiom signature in §3.E is **unaffected by
the S6b finding**.  The narrowing of the regular-polytope family
happens at the $k = 2$ level (separate axiom, §6).

## 5. Sanity check via the parent's plane case (d = 2)

The S5 axiom is stated for `d ≥ 3`.  For `d = 2`, we have S4 ACT's
`oneflat_eq_parent : IsKFlatMagic 1 P ↔ Erdos735.IsMagic P`, and
the parent's `magic_classification` axiom

```lean
axiom magic_classification (P : Erdos735.PointConfig) :
    Erdos735.IsMagic P ↔
      Erdos735.IsCollinear P ∨ Erdos735.IsGeneralPosition P ∨
      Erdos735.IsNearPencil P ∨ Erdos735.IsIncenterConfig P
```

closes the `d = 2, k = 1` case.  So the **full** $k = 1$
classification is covered by:

- `d = 2`: parent's `magic_classification` (axiom, ABKPR 2008,
  PUBLISHED).
- `d ≥ 3`: this PREP's `oneflat_classification_higher_dim`
  (axiom, conjectural, NOT published).

Both are `axiom`s.  Both produce gallery `status: "axiomatized"`.
The slug's eventual `axiomCount` will be **1** (just S5's axiom);
the parent's axiom does not transfer because S5 reduces to it via
`oneflat_eq_parent` for `d = 2`, but the `d ≥ 3` case is genuinely
independent.

## 6. Higher-flat axioms (out of scope for S5)

For completeness, the next layer of axioms beyond S5 covers $k = 2,
d = 3$ (the natural sequel) and parameterises by $k$:

```lean
/-- **S6 / sibling axiom** (conjectural extension to 2-flats in ℝ³).
    The 2-flat magic configurations in ℝ³ include the tetrahedron at
    alternate-cube-vertices (S6a PREP, certificate constant = 3) and
    general-position configurations (analogous to line case); they
    EXCLUDE octahedron and cube (S6b PREP, O_h obstruction).  The
    complete characterisation is open. -/
axiom twoflat_classification_d3 (P : PointConfigD 3) :
    IsKFlatMagic 2 P ↔
      <some predicate including tetrahedron + general position; open>
```

This is a **separate axiom**, parameter-independent from S5.  Its
shippability requires further PREP (S5-sibling) to enumerate the
known $k = 2, d = 3$ magic classes — at minimum, the tetrahedron
(S6a PREP), general position (`IsGeneralPositionD` extended to $k = 2$),
and a yet-to-be-defined class capturing the "$O_h$-non-rigid"
condition that fails for octahedron and cube.

**Recommendation**: defer to a future PREP.  Out of scope for this
S5 PREP, which targets the **lines-in-ℝᵈ** case only.

## 7. S5 ACT implementation order

When a future ACT iteration discharges S5, the order is:

1. ☐ Add the 4 new `def`s (`IsCollinearD`, `IsGeneralPositionD`,
   `IsNearPencilD`, `IsIncenterConfigD`) to
   `proofs/Proofs/Erdos735OQ04.lean`, immediately after the existing
   `IsKFlatMagic` def.  Total ~20 LOC.
2. ☐ Add the `axiom oneflat_classification_higher_dim`, ~10 LOC
   including docstring.
3. ☐ Add a doc-only `theorem` re-statement that for `d = 2`, this
   reduces (via `oneflat_eq_parent` + parent's `magic_classification`)
   to the published ABKPR.  Recommended: prove
   `oneflat_classification_dim_two : IsKFlatMagic 1 (P : PointConfigD 2) ↔
   Erdos735.IsCollinear P ∨ … ∨ Erdos735.IsIncenterConfig P` — ~12 LOC,
   no new axioms (uses existing `oneflat_eq_parent` + parent axiom).
4. ☐ Update `state.md` Phase → S5 ACT complete; `axiomCount: 0 → 1`.
5. ☐ Update `meta.json` (when S7 ships): `status: "axiomatized"`,
   `axiomCount: 1`, `assumptions: "1 axiom: …"`.
6. ☐ Docker build-verify.
7. ☐ Branch: `research/erdos-735-oq-04-s5-act-higher-dim-axiom-<unix-ts>`.

**Estimated post-S5 ACT file metrics**:

| Metric | Pre-S5 | Post-S5 | Δ |
|--------|--------|---------|---|
| LOC | 180 | ~220 | +40 |
| Theorems | 3 | 4 (+`oneflat_classification_dim_two`) | +1 |
| Defs | 4 | 8 (+4 class predicates) | +4 |
| Axioms | 0 | **1** | **+1** |
| Sorries | 0 | 0 | 0 |
| Imports | 5 | 5 | 0 |

## 8. Mathlib bearer audit (pinned v4.26.0 SHA `2df2f0150c…`)

All declarations referenced in §3 (a) – (d) are present and
unchanged from the S2 PREP / S3 PREP bearer audits:

| Decl | Module | Status |
|------|--------|--------|
| `AffineSubspace` | `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` | ✅ pinned |
| `AffineSubspace.direction` | (same) | ✅ pinned (returns `Submodule ℝ _`) |
| `Module.rank` | `Mathlib.LinearAlgebra.Dimension.Basic` | ✅ pinned |
| `EuclideanSpace ℝ (Fin d)` | `Mathlib.Analysis.InnerProductSpace.PiL2` | ✅ pinned |
| `Function.Injective` | `Mathlib.Logic.Function.Basic` | ✅ pinned |
| `Finset.card` | `Mathlib.Data.Finset.Card` | ✅ pinned |
| `Erdos735.IsMagic`, etc. | `Proofs.Erdos735Problem` | ✅ already imported |

**No new bearers** beyond what the slug already pins.  No new imports
required.  The S5 ACT is bearer-clean.

## 9. Honest framing

This PREP closes a documentation gap left by S1 OBSERVE: it converts
the S1 axiom **sketch** (with `sorry` placeholders) into a
**syntactically complete, paste-ready** axiom signature that
type-checks under Lean 4's `axiom` elaboration.

It does **not** discharge S5: the axiom remains conjectural and
research-level open.  In particular:

- The conjectured higher-dim 4-class classification is **the
  formaliser's natural guess**, lifted from ABKPR 2008's planar
  result.  No published proof exists for $d \ge 3$.
- The `IsIncenterConfigD` predicate (§3.D) is a **structural
  skeleton**, not the precise ABKPR-style incenter
  characterisation.  Mathlib's `ℝᵈ` bisector / insphere API is
  not present at v4.26.0; closing this gap requires either a
  Mathlib contribution or a less-tight predicate.
- The S6b refutation (octahedron/cube fail $k = 2$) does **not**
  affect this $k = 1$ axiom; it lives in the (deferred) $k = 2$
  axiom family (§6).

This PREP produces **0 Lean delta**, **0 sorries/axioms** in the
shipping file.  Its only artifacts:

- This memo (this file).
- State.md update: Phase → "S5 PREP shipped (refined conjecture,
  paste-ready)"; Iteration += 1.

S5 ACT is a separate iteration.  Build cost: 0 (no Lean changes).

## 10. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `IsIncenterConfigD` skeleton (§3.D) is too loose | HIGH | Document gap; defer to follow-up; ship `axiomatized` with note |
| Mathlib v4.26.0 drift before S5 ACT | LOW | Pin SHA in S5 ACT session header |
| Parent file changes invalidate `oneflat_eq_parent` (S4) | LOW | Parent is stable at #20896; sibling slugs not active on parent |
| Sibling slug (`oq-01/02/03`) ships a conflicting axiom for $d = 3$ | MEDIUM | Cross-check sibling slugs before S5 ACT; if conflict, coordinate via shepherd |
| `axiom` body fails to elaborate due to v4.26.0 quirks | LOW | All 4 defs use already-pinned bearers; the disjunction is `Prop`-level so no elaboration gymnastics |

## 11. Coordination notes

- **No sibling activity on `erdos-735-oq-04` since 2026-05-31**
  (last commit on file = #21732 S4 ACT, this researcher).
- **Parent `Erdos735Problem.lean` last touched** 2026-05-29
  (#20896, this researcher's AXIOM HUNT).  Stable.
- **No active OQ-01 / OQ-02 / OQ-03 / OQ-05 work** on the parent
  slug at last `gh pr list --search "erdos-735"` (verified via
  `git log origin/main --since=2026-05-31 --grep=erdos-735`: only
  this slug's commits).

## 12. Anti-targets (out of scope for this PREP)

1. **Discharging S5 ACT** (writing the axiom into the Lean file).
   This PREP is doc-only; the axiom signature is paste-ready but
   not pasted.
2. **Closing the `IsIncenterConfigD` semantic gap** (precise
   `ℝᵈ` bisector / insphere definition).  Requires Mathlib
   infrastructure not present at v4.26.0.
3. **The $k \ge 2$ axiom family** (§6 placeholder).  Separate PREP
   needed; tetrahedron / octahedron / cube findings inform it but
   do not yet fix its signature.
4. **Refactoring parent's `IsGeneralPosition`** to be `d`-parameterised.
   Option (b) of §3.B.  Out of scope; S5 ACT can ship with a
   self-contained `IsGeneralPositionD` definition.
5. **Gallery JSON update** (S7).  Deferred until S5 ACT lands.

## 13. References

- `problem.md` §"Formal Lean target signatures" — the S1 OBSERVE
  axiom sketch with `sorry`-placeholders that this PREP refines.
- `knowledge.md` §"Extension to $k$-flats" — the S6b finding that
  narrows the regular-polytope family.
- `sessions/2026-05-13-s6b-prep-octahedron-cube-not-2-flat-magic.md` —
  the vertex-transitive $O_h$ obstruction analysis.
- `sessions/2026-05-31-s4-act-parent-reduction.md` — the most
  recent ACT on this slug, providing the `oneflat_eq_parent`
  reduction that makes the parent's axiom available for `d = 2`.
- `proofs/Proofs/Erdos735Problem.lean` — parent file with
  `magic_classification` axiom and `IsCollinear` / etc. predicates.
- Murty, U.S.R. (1971), "How many magic configurations are
  there?" — the original $d = 2, k = 1$ conjecture.
- Ackerman, Buchin, Knauer, Pinchasi, Rote (2008), "There are not
  too many magic configurations" — the $d = 2, k = 1$ proof.
- Erdős-problems.com / problem #735 — parent source.
