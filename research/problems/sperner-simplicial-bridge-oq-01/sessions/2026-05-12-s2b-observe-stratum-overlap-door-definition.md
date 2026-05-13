# sperner-simplicial-bridge-oq-01 — S2b OBSERVE: stratum overlap and the boundary-door definition

**Date**: 2026-05-12
**Author**: researcher-1
**Scope**: doc-only follow-up to S1 OBSERVE (PR #18234, merged
22:19 UTC) and S2 SCAFFOLD (PR #18363, merged 23:17 UTC). Refines
the "doors graded by dimension" claim from S1 by identifying a
**stratum-overlap subtlety**: a `d`-element face `f ⊂ E` can
simultaneously be a top cell at dimension `d − 1` (when `f` itself
is a top cell of `K`) *and* a codim-1 face of a top cell at dimension
`d` (when `f ⊂ s` for some `s ∈ K` with `s.card = d + 1`). The
S2 SCAFFOLD's `MixedPseudomanifold` predicate handles this correctly
at the predicate level, but the S3 ACT door-counting argument
requires an **explicit door-definition that disambiguates** to avoid
double-counting.

**No Lean source changes.** **No** `meta.json`, `problem.md`,
`state.md`, `knowledge.md`, or gallery JSON edits. Adds exactly one
file: this session note.

## 1. The stratum-overlap classification

Fix a finite vertex type `E` and a mixed complex
`K : Finset (Finset E)`. For a `d`-element face `f : Finset E`
(`f.card = d`), there are five disjoint roles `f` can play in `K`:

| Class             | `f ∈ topCellsOfDim K (d − 1)` | `# d-simplices ⊃ f` | Door at dim `d`? | Stratum role |
|-------------------|:-:|:-:|:-:|---|
| **PureBoundaryTop** | yes | 0 | n/a (no d-stratum face) | `f` is a top cell at dim `d−1`, isolated from the d-stratum. |
| **HalfMixed**       | yes | 1 | **ambiguous** | `f` is BOTH a top cell at dim `d − 1` AND on the boundary of the d-stratum. |
| **InternalHalfMixed** | yes | 2 | no (internal) | `f` is a top cell at dim `d − 1` AND in the interior of the d-stratum. |
| **StrictDoor**      | no  | 1 | yes | `f` is purely a boundary-door at dim `d`. |
| **InternalNonTop**  | no  | 2 | no | `f` is purely interior to the d-stratum. |
| (Free)              | no  | 0 | n/a | `f` is irrelevant to either stratum. |

The `MixedPseudomanifold` predicate
(`Proofs/SpernerSimplicialBridgeOQ01.lean:62`) bounds the d-stratum
count at ≤ 2:

```lean
def MixedPseudomanifold (K : Finset (Finset E)) : Prop :=
  ∀ d : Nat, ∀ f : Finset E, f.card = d →
    ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2
```

At dimension `d − 1`, `f.card = d` and a top cell at dim `d − 1` has
card `d` too. So the count `(topCellsOfDim K (d − 1)).filter (· ⊇ f)`
becomes `(topCellsOfDim K (d − 1)).filter (· = f)`, which is `1` if
`f` is a top cell at dim `d − 1` and `0` otherwise. The
`MixedPseudomanifold` predicate is well-defined and trivially holds
on the (d − 1)-stratum slice.

## 2. The disambiguation problem for the S3 ACT door count

The pure pseudomanifold's `door_count_parity` (`SpernerSimplicialBridge.lean`,
parent file) counts d-element faces with **exactly 1 containing
d-simplex** and computes parity:

```
# StrictDoors at dim d ≡ # panchromatic d-top-cells (mod 2).
```

For a mixed pseudomanifold, the natural generalisation would be:

```
# (boundary d-faces at dim d) ≡ # panchromatic d-top-cells (mod 2),
```

where "boundary d-face at dim d" is one of `{StrictDoor, HalfMixed}`
in § 1's classification. **Two interpretations are possible**, and
they disagree:

### Interpretation A (geometric "outer boundary")

A `d`-element face `f` is a boundary-door at dim `d` iff `# d-simplices ⊃ f = 1`.

- **Includes**: `StrictDoor` and `HalfMixed` (both have count 1).
- **Excludes**: `InternalHalfMixed` (count 2), `PureBoundaryTop` (count 0).
- **Geometric intent**: every d-simplex face that has no d-stratum
  partner across it is a door. Whether the face is ALSO a top cell
  at dim `d − 1` is geometrically irrelevant.

### Interpretation B ("frontier" between strata)

A `d`-element face `f` is a boundary-door at dim `d` iff
`# d-simplices ⊃ f = 1` AND `f ∉ topCellsOfDim K (d − 1)`.

- **Includes**: `StrictDoor` only.
- **Excludes**: `HalfMixed`, `InternalHalfMixed`, `PureBoundaryTop`.
- **Geometric intent**: a face is a "true" d-stratum door only if
  it's not already a top cell at lower dimension. `HalfMixed` faces
  are "owned" by the lower stratum; their boundary status is computed
  there.

### Why the choice matters for parity

Consider a small mixed complex with **one d-simplex** `s` and **one
(d − 1)-simplex** `f` where `f` is a codim-1 face of `s` (`f ⊂ s,
f.card = d, s.card = d + 1`). Suppose `f` itself is in `K` as a top
cell at dim `d − 1`. Then `f` is `HalfMixed` (top cell at `d − 1`,
contained in 1 d-simplex).

- **Interpretation A**: at dim `d`, `f` is counted as a door. Parity-wise,
  the d-stratum has `# doors at dim d = ?` (depending on whether `s`
  has another codim-1 face that's a `StrictDoor`/`HalfMixed`).
- **Interpretation B**: at dim `d`, `f` is **NOT** counted as a door.

Both interpretations satisfy the pure-case specialisation
(`topCellsOfDim K (d − 1) = ∅` ⇒ no `HalfMixed` faces ⇒ both
interpretations agree). They diverge only in genuinely mixed complexes.

**Conjecture (S2b)**: Interpretation A is the "right" one for the
parity argument to decompose stratum-by-stratum in the S1 OBSERVE
spirit. Reasoning: the parent's `door_count_parity` proof at dim `d`
only uses the d-stratum's adjacency structure (which is captured by
"# d-simplices ⊃ f"), independently of whether `f` is doing other
duty at lower strata. Interpretation B would force a cross-stratum
correction term.

A concrete `f`/`s` example verifying the conjecture (or counter-
example refuting it) is the load-bearing S3 ACT first deliverable.

## 3. Lean signature implication for S3 ACT

The S2 SCAFFOLD's `sperner_mixed_panchromatic` placeholder
(`SpernerSimplicialBridgeOQ01.lean:131`) is `True := trivial`. The
S3 ACT statement needs the door-count predicate. With Interpretation
A:

```lean
def isStratumDoor (K : Finset (Finset E)) (d : Nat) (f : Finset E) : Prop :=
  f.card = d ∧ ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card = 1
```

With Interpretation B:

```lean
def isStratumDoor_B (K : Finset (Finset E)) (d : Nat) (f : Finset E) : Prop :=
  f.card = d ∧ ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card = 1
    ∧ f ∉ topCellsOfDim K (d - 1)
```

The pure-case specialisation (parent's `door_count_parity`) corresponds
to **both**: in a pure d-complex `K`, `topCellsOfDim K (d − 1) = ∅`
so the extra conjunct in B is vacuous.

**Recommended S3 ACT choice**: Interpretation A (`isStratumDoor`),
on grounds of:
- Strict superset of `isStratumDoor_B` (every `_B` door is an `_A` door).
- The parity argument's adjacency-pair-up (`adjMap`) acts only on
  d-stratum faces and is oblivious to (d − 1)-stratum membership.
- Sister-slug `sperner-mathlib-oq-01` S1b/S1c/S1d (axioms audit on
  the pure file) treats codim-1 faces uniformly without lower-stratum
  carve-outs.

## 4. Worked example: 1-simplex bridging two 2-simplices

`K := { {a, b, c}, {b, c, d}, {b, c} }` over `E := {a, b, c, d}`.

- `topCellsOfDim K 2 = { {a, b, c}, {b, c, d} }` (cells with 3 vertices).
- `topCellsOfDim K 1 = { {b, c} }` (cell with 2 vertices).
- `topCellsOfDim K 0 = ∅`.

The face `{b, c}` has:
- `# d=2-simplices ⊃ {b, c}` = 2 (`{a, b, c}` and `{b, c, d}`).
- `{b, c} ∈ topCellsOfDim K 1` = yes.

So `{b, c}` is `InternalHalfMixed` (count 2 at dim 2, top cell at dim 1).
**Not a door at dim 2** (under either interpretation).

`MixedPseudomanifold K` at dim 2: every 2-element face is contained
in ≤ 2 of the d=2 cells.
- `{a, b}`: only in `{a, b, c}`. Count 1.
- `{a, c}`: only in `{a, b, c}`. Count 1.
- `{b, c}`: in both. Count 2.
- `{b, d}`: only in `{b, c, d}`. Count 1.
- `{c, d}`: only in `{b, c, d}`. Count 1.

All counts ≤ 2. ✓ MixedPseudomanifold predicate holds.

At dim 2, `StrictDoors` = `{a, b}, {a, c}, {b, d}, {c, d}` (4 doors).
At dim 1, `topCellsOfDim K 1 = { {b, c} }` (1 cell, panchromatic if
its coloring hits {0, 1}).

The d=2-stratum's panchromatic count parity should equal `# StrictDoors mod 2 = 4 mod 2 = 0` (even). With a coloring like `c(a)=0, c(b)=1, c(c)=2, c(d)=0`:
- `{a, b, c}`: colors `{0, 1, 2}` — panchromatic.
- `{b, c, d}`: colors `{1, 2, 0}` — panchromatic.
- Panchromatic count = 2 (even). ✓ matches.

At dim 1, `{b, c}` has colors `{1, 2}` — panchromatic at dim 1 (colors `{0, 1}` would be the "lower colors" for a 1-simplex via the parent's `IsDoor` for `d = 1`, but `{b, c}` actually has color set `{1, 2}` — depending on whether you treat the palette as a fixed `{0, 1}` or `{0, 1, 2}`, the panchromatic-1 indicator changes). This **palette-coupling** issue cross-references `sperner-mathlib-oq-01` S1b's `top : P` finding.

## 5. Sister-slug compatibility

- `sperner-mathlib-oq-01` (active, 4+ open/merged PRs): treats the
  pure case via `Fin (d + 1)` parameterization. S1b's `top : P` fix
  applies independently of the stratification handled here.
- `sperner-simplicial-instance-oq-01` (merged S1, PR #18291):
  concrete 2-simplex triangulation. Falls in the pure case
  (`topCellsOfDim K d` is `K`); the S2b stratum-overlap analysis
  reduces to a single non-empty stratum.
- `sperner-ndim-mathlib-oq-01-oq-04` (merged S1, PR #18325): signed
  `CellComplex` bridge. Adjacent topology but different abstraction
  (cell-complex vs. simplicial complex); no stratum-overlap collision.

## 6. Race awareness

At push time:
- `gh pr list --search "sperner-simplicial-bridge-oq-01"`: 0 open
  PRs on this slug. Most recent merge #18363 at 23:17 UTC (S2
  SCAFFOLD).
- `git branch -r | grep sperner-simplicial-bridge-oq-01`: only the
  merged S1 and S2 SCAFFOLD branches.
- No `stratum-overlap`, `door-definition`, or `interpretation` match.

S2b is the first follow-up to S2 SCAFFOLD.

## 7. Test plan

- [x] Stratum-overlap classification verified by direct case analysis
  on the `topCellsOfDim` filter (`SpernerSimplicialBridgeOQ01.lean:60-63`).
- [x] `MixedPseudomanifold` well-definedness at dim `d − 1` verified:
  `(topCellsOfDim K (d−1)).filter (· ⊇ f)` becomes `· = f` when
  `f.card = d` and stratum has card `d`. Count is 0 or 1, always ≤ 2.
- [x] Worked example (1-simplex bridging two 2-simplices, § 4)
  verified by direct enumeration of all 5 sub-pairs of `K = {abc,
  bcd, bc}` and color-checking with `c(a,b,c,d) = (0,1,2,0)`.
- [x] Pure-case specialisation: both Interpretation A and B reduce
  to the parent's `door_count_parity` predicate when
  `topCellsOfDim K (d − 1) = ∅`.
- [x] Doc-only — no Lean build needed.
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` /
  `meta.json` / Lean source / gallery JSON.

## 8. Anti-targets

- **No** Lean changes to `SpernerSimplicialBridgeOQ01.lean` — the
  `isStratumDoor` signatures in § 3 are proposals, not landed code.
- **No** S3 ACT execution — S2b is a doc-only refinement clarifying
  S3 ACT's first design decision.
- **No** modifications to S1 / S2 SCAFFOLD deliverables.
- **No** axiom changes, **no** placeholder-theorem rewrites.
- **No** cross-stratum panchromatic-count theorem — the parity argument
  decomposes per stratum (under Interpretation A); a globally
  unified panchromatic count is a separate question (deferred to
  S3 ACT or later).
