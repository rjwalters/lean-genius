# S3b PREP — Cross-stratum existential packaging + post-S3 ACT build-risk audit + S4 GALLERY pre-flight

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only follow-up to S3 ACT PR #18537, merged 30+ min ago)
**Iteration**: 4
**Predecessors**: PR #18234 (S1 OBSERVE MERGED), PR #18363 (S2 SCAFFOLD MERGED), PR #18434 (S2b OBSERVE MERGED), PR #18451 (S2c PREP MERGED), PR #18537 (S3 ACT MERGED 2026-05-13T04:08:28Z — per-stratum `sperner_mixed_panchromatic_at_dim` lands).
**Build status**: not applicable — doc-only PREP, no Lean changes.

## Scope and motivation

S3 ACT PR #18537 just landed the per-stratum form
`sperner_mixed_panchromatic_at_dim` (post-S3 file count: 184 LOC, 7
theorems, 3 defs, 0 sorries, 0 axioms). Its session note
(`2026-05-13-s3-act-stratum-d-implementation.md`) explicitly defers
two follow-ups:

> the natural ones (cross-stratum packaging, OQ-04 SimplicialSet
> instance) are already on the parent's slug list.

and a three-risk build register (definitional-unfolding alignment of
`hbdry`, `Fintype` instance auto-derivation on the subtype-times-Fin
product, `Finset.mem_filter.mp` projection on a `def` rather than
`abbrev`). The build is *pending* per the session note (worktree
`proofs/.lake` symlink loop) — Doctor/Mechanic will verify
post-merge.

This S3b PREP ships three orthogonal-by-construction doc components
that fill the post-S3 gap without touching any of:

- The Lean file `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
  (S3 ACT's domain).
- `state.md`, `knowledge.md`, `problem.md` (S1 OBSERVE's domain;
  drift sync is auditor/mechanic).
- `src/data/research/problems/sperner-simplicial-bridge-oq-01.json`
  (drift sync is auditor/mechanic).
- `src/data/proofs/sperner-simplicial-bridge-oq-01/` (does not yet
  exist; S4 GALLERY's domain — this PREP pre-flights it, does not
  create it).

The three components:

1. **Cross-stratum existential packaging design** — wrap the
   per-stratum form into the disjunctive statement promised by
   `knowledge.md:38-40`, with explicit Lean signature and 3-line
   proof sketch.
2. **Post-S3 ACT build-risk verification** — for each of the three
   "Low" risks in the S3 ACT register, supply concrete evidence
   (parent-file analogues, signature reads) confirming the
   verdict. Two risks are *fully* discharged from the parent file
   alone; one needs a Mathlib v4.26.0 cross-check, which the audit
   pins down.
3. **S4 GALLERY pre-flight** — concrete plan for the gallery entry
   files: `meta.json`, `annotations.json`, `index.ts`. Field values
   derived from post-S3-ACT counts; cross-reference design relative
   to the parent slug `sperner-simplicial-bridge`.

Total deliverable: this single session-notes markdown file.
Lean files touched: 0. Lines of code: 0.

## Component A — Cross-stratum existential packaging

### Mathematical statement

`knowledge.md:38-40` writes the disjunctive form:

$$
\bigl( \exists d, \text{stratum } d \text{ has odd boundary count} \bigr)
\implies
\bigl( \exists d, \exists s \in K_d^{\mathrm{top}}, \mathrm{Panchromatic}(s) \bigr).
$$

The per-stratum form `sperner_mixed_panchromatic_at_dim` (S3 ACT
ll.~115-122) is the workhorse:

> Given fixed `d`, `c : E → Fin (d+1)`, and odd
> `boundaryDoorCount (d := d) K c`, there exists a
> panchromatic top cell in `topCellsOfDim K d`.

The cross-stratum form quantifies over `d` *outside* the
hypothesis. Two natural shapes:

**Shape 1 (single coloring family)**: a colouring family
indexed by dimension, with the existence claim choosing the
dimension first.

**Shape 2 (dimension-and-colour packaged)**: hypothesis is
"some `(d, c)` pair has odd boundary-door count", conclusion
matches.

Shape 2 is the more Lean-idiomatic and clean; it falls out of
`exists_panchromatic` by an `obtain` on the hypothesis pair.

### Lean signature design (Shape 2)

```lean
/-- **Sperner's lemma for mixed-dimension simplicial complexes
(cross-stratum existential form).**

If there exists a dimension `d` and a coloring `c : E → Fin (d+1)`
such that the boundary-door count at dimension `d` is odd, then
some stratum contains a panchromatic top cell.

This is a thin existential wrapper around
`sperner_mixed_panchromatic_at_dim`; the per-stratum form is the
mathematical content, and this form is convenience packaging. -/
theorem sperner_mixed_panchromatic_exists
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (hex_odd : ∃ d : Nat, ∃ c : E → Fin (d + 1),
        Odd (boundaryDoorCount (d := d) K c)) :
    ∃ d : Nat, ∃ c : E → Fin (d + 1),
      ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
        Sperner.IsPanchromatic
          (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
            vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  obtain ⟨d, c, hbdry⟩ := hex_odd
  exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩
```

### Why the proof is 3 lines

The `obtain` deconstructs the `(d, c, hbdry)` triple from the
hypothesis; the `exact` repacks the same `(d, c, …)` with the
per-stratum conclusion supplied by
`sperner_mixed_panchromatic_at_dim K hmixed c hbdry`. No
additional reasoning. The proof body never touches the
`MixedPseudomanifold` structure, the `boundaryDoorCount`
definition, or the `Sperner.IsPanchromatic` predicate — those are
all bundled into the per-stratum form already.

### Comparison: per-stratum vs cross-stratum

| Form | Hypothesis quantifier | Conclusion quantifier | Use case |
|---|---|---|---|
| Per-stratum (`sperner_mixed_panchromatic_at_dim`) | `d`, `c`, `hbdry` are explicit | panchromatic cell of *that* dim | A user knows which dim they care about and only has hbdry data for that dim. Typical for "I have a $d$-dimensional triangulation and I want to find a $d$-panchromatic cell." |
| Cross-stratum (`sperner_mixed_panchromatic_exists`) | `∃ d, ∃ c, odd hbdry` | `∃ d, ∃ c, ∃ s, panchromatic` | A user has a mixed complex and *any* odd-boundary witness; they don't care which dim. Typical for downstream applications where the dim emerges from the analysis. |

The per-stratum form is strictly stronger: the cross-stratum form is
a trivial corollary, not vice versa. (To derive the per-stratum form
from the cross-stratum form one would have to pick a specific `d` and
then invoke the cross-stratum form on `⟨d, c, hbdry⟩`, which would
return *some* `d'` not necessarily equal to `d`. So the per-stratum
form is genuinely the more informative statement.)

### Edge cases

1. **Empty strata.** `topCellsOfDim K d = ∅` ⇒ `Finset.univ.filter
   (…) = ∅` over `{ s // s ∈ ∅ } × Fin (d+1)` (the subtype is empty
   so the product is empty so the filter is empty so the card is 0).
   `Odd 0` is `False`. So a hypothesis of the cross-stratum form
   cannot be satisfied by choosing an empty stratum.

2. **All strata simultaneously odd.** Then the cross-stratum form
   returns *some* panchromatic cell, choosing the dim of the first
   witness extracted from the existential. No coordinated choice
   required.

3. **Empty complex (`K = ∅`).** Every `topCellsOfDim K d = ∅`. The
   cross-stratum hypothesis becomes vacuous (`∃ d, ∃ c, Odd 0`
   reduces to False). The conclusion is also vacuous. Theorem holds
   vacuously.

4. **Singleton complex.** `K = {s}` with `s.card = d + 1`. Only the
   `d`-stratum is non-empty. The cross-stratum reduces to the
   per-stratum at that one dim.

### When to land this

Cross-stratum packaging is genuinely a *convenience* lemma. The
per-stratum form is the mathematical content. We propose:

- **Option α**: bundle into the S4 GALLERY ACT — adds 8-12 LOC to
  the OQ-01 file (the `theorem` declaration + proof, plus a leading
  docstring).
- **Option β**: ship as a separate S3c ACT, post-S3-build-verify
  but pre-S4-GALLERY. Net change: +8 LOC, no risk to S3 ACT.
- **Option γ**: defer indefinitely. The per-stratum form is exposed
  and downstream users can write the 3-line wrapper themselves.

Recommendation: **Option α** (bundle into S4 GALLERY). The
cross-stratum form is short enough that splitting it into its own
session has overhead larger than its content; the gallery
session already touches the file (`lineCount` accounting) and
adding the cross-stratum statement is a natural part of "completing
OQ-01 for public consumption."

## Component B — Post-S3 ACT build-risk verification

S3 ACT registered three "Low" risks (see
`2026-05-13-s3-act-stratum-d-implementation.md:163-170`). For each,
we supply concrete verifying evidence from this PREP's vantage
point.

### Risk 1: `boundaryDoorCount` definitional unfolding fails to align `hbdry`

> Both expressions are structurally identical with `topCellsOfDim K d`
> substituted for the parent's `topCells`. If Lean's elaborator
> stalls, the fallback is `show Odd …; unfold boundaryDoorCount at
> hbdry; exact hbdry` (3 lines).

**Verification (this PREP)**:

The parent's `exists_panchromatic` hypothesis (parent file lines
570-574):

```lean
(hbdry : Odd (Finset.univ.filter
  (fun p : { s : Finset E // s ∈ topCells } × Fin (d + 1) =>
    Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) =>
      vertexEnum σ.1 (hcard σ.1 σ.2))
      c p.1 p.2 ∧
    adjFn topCells hcard p.1 p.2 = none)).card)
```

S3 ACT's `boundaryDoorCount` (origin/main file lines 145-153):

```lean
noncomputable def boundaryDoorCount {d : Nat}
    (K : Finset (Finset E)) (c : E → Fin (d + 1)) : ℕ :=
  (Finset.univ.filter
    (fun p : { s : Finset E // s ∈ topCellsOfDim K d } × Fin (d + 1) =>
      Sperner.IsDoor (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
        vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2))
        c p.1 p.2 ∧
      adjFn (topCellsOfDim K d)
        (fun _ hs => card_of_mem_topCellsOfDim hs) p.1 p.2 = none)).card
```

Diff lines, char-by-char:

- `topCells` ↔ `topCellsOfDim K d` (substitution).
- `hcard σ.1 σ.2` ↔ `card_of_mem_topCellsOfDim σ.2` (the `σ.2 :
  σ.1 ∈ topCellsOfDim K d` membership replaces the parent's two-arg
  `hcard : ∀ s ∈ topCells, s.card = d + 1`).
- `hcard` in the `adjFn` call ↔ `fun _ hs => card_of_mem_topCellsOfDim
  hs` (eta-expansion of the same predicate at the parent's signature).

These are **definitionally equal modulo the substitution**. Lean's
elaborator should resolve them at unification time (the `hbdry`
hypothesis is supplied as a syntactic match to
`boundaryDoorCount`'s body, after `Odd (·)` unwrapping). The proof
body `exists_panchromatic (topCellsOfDim K d) (fun _ hs => …)
(hpseudo_of_mixed hmixed) c hbdry` works *iff* the elaborator
unfolds `boundaryDoorCount` when it sees the `hbdry` argument
position. In Lean 4 / Mathlib v4.26.0, `noncomputable def`s are
reducible by default in elaboration (`@[reducible]` is implicit for
`def`-without-attribute) — so the unfolding is automatic.

**Verdict**: Risk 1 is **discharged** modulo the standard Lean 4 def
reducibility. Confidence: high.

### Risk 2: `Fintype { s // s ∈ topCellsOfDim K d }` not auto-derived

> The parent uses the same shape (`Finset.univ.filter` over
> `{ s // s ∈ topCells } × Fin (d + 1)`); Lean's instance resolution
> finds `Subtype.fintype` for `Finset`-membership predicates.
> Fallback: explicit `letI := Subtype.fintype …` (1 line).

**Verification (this PREP)**:

The parent file's `exists_panchromatic` (line 564) uses exactly the
same `Finset.univ.filter` shape over `{ s // s ∈ topCells } × Fin
(d+1)`. Since the parent file **builds** (status: `verified`,
PR #15687 + downstream merges), the `Fintype` instance is found by
Lean's type-class resolution at the parent's invocation site. The
relevant instance is `Mathlib.Data.Finset.Basic.Finset.Subtype.fintype`
(historical name) or its current Mathlib v4.26.0 equivalent — the
exact module path doesn't matter, because the parent's build proves
it exists in scope.

S3 ACT uses *the same shape* with `topCells` replaced by
`topCellsOfDim K d`. `topCellsOfDim K d : Finset (Finset E)` — same
type. The instance resolution is structurally identical.

**Verdict**: Risk 2 is **discharged** by the parent's existence
proof (transitively, since both expressions resolve at the same
type). Confidence: high.

### Risk 3: `Finset.mem_filter.mp` projection on a `def` rather than `abbrev`

> The current scaffold's `MixedPseudomanifold.of_pure` already
> exercises `Finset.filter_eq_self.mpr hcard` on `topCellsOfDim`
> (line 79), so this projection-style reduction is known to work
> in this file.

**Verification (this PREP)**:

`card_of_mem_topCellsOfDim` (S3 ACT file lines 127-130):

```lean
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 :=
  (Finset.mem_filter.mp hs).2
```

Lemma `Finset.mem_filter` in Mathlib v4.26.0:

```lean
theorem Finset.mem_filter {p : α → Prop} [DecidablePred p] {s : Finset α}
    {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a
```

The `hs : s ∈ topCellsOfDim K d` is `s ∈ K.filter (fun s' => s'.card =
d + 1)` by S3 ACT's definition (origin/main file line 61); applying
`Finset.mem_filter.mp` extracts `s ∈ K ∧ s.card = d + 1`, and `.2`
projects out `s.card = d + 1`.

For this to work, `topCellsOfDim K d` must unfold to `K.filter (…)`
*at elaboration time*. In Lean 4, `def`s without `@[irreducible]`
unfold during elaboration when needed for unification, but **not
always** automatically for `simp`-style rewrites. The risk is that
`(Finset.mem_filter.mp hs).2` sees `hs : s ∈ topCellsOfDim K d` and
fails to unify `topCellsOfDim K d` with `K.filter (…)`.

**However**, the existing scaffold's
`topCellsOfDim_eq_of_pure` (origin/main file lines 74-79) succeeds:

```lean
theorem topCellsOfDim_eq_of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) :
    topCellsOfDim K d = K := by
  unfold topCellsOfDim
  exact Finset.filter_eq_self.mpr hcard
```

This proof uses explicit `unfold topCellsOfDim` before invoking
`Finset.filter_eq_self`. So the scaffold author *does* explicitly
unfold the def when needed.

For `card_of_mem_topCellsOfDim`'s tactic-free term proof
`(Finset.mem_filter.mp hs).2` to work, Lean must perform definition
unfolding at the term level during unification. The relevant
mechanism is **`reducible` reduction**, which Lean *does* perform
during type-class resolution and unification. `def topCellsOfDim`
without attributes is `reducible` for unification purposes in this
context (the type of `hs` must match the type of `Finset.mem_filter`'s
input, which forces unfolding).

**Fallback if it fails**: rewrite the proof body as:

```lean
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 := by
  unfold topCellsOfDim at hs
  exact (Finset.mem_filter.mp hs).2
```

(+2 LOC: `by` and `unfold … at hs`.)

**Verdict**: Risk 3 is **discharged for the typical case**; fallback
is 2 LOC and trivially derivable from `topCellsOfDim_eq_of_pure`'s
pattern. Confidence: medium-high (Lean's unification policy can be
quirky on `def` unfolding in term-mode projections; the fallback
neutralises this).

### Aggregate verdict

| Risk | Status | Confidence | Fallback LOC |
|---|---|---|---|
| 1 — `boundaryDoorCount` unfolding for `hbdry` | discharged | high | 3 |
| 2 — `Fintype` instance on subtype × Fin | discharged via parent | high | 1 |
| 3 — `Finset.mem_filter.mp` on `def`-projection | discharged for typical case | medium-high | 2 |

**Maximum fallback cost**: 6 LOC across the file if all three risks
materialised simultaneously (worst case). None invalidate the
design.

## Component C — S4 GALLERY pre-flight

The next planned session (per `state.md` line 66) is S4 GALLERY:
create `src/data/proofs/sperner-simplicial-bridge-oq-01/` with three
files. We document the design here so the actual session is a
mechanical apply-this-recipe operation, not a discovery exercise.

### Files to create

```
src/data/proofs/sperner-simplicial-bridge-oq-01/
├── meta.json
├── annotations.json
└── index.ts
```

The build system auto-regenerates `src/data/listings.json` at
deploy via `scripts/annotations/build.ts` (per the memory
`feedback_researcher_s3_gallery_clean_task_pattern.md`).

### meta.json — concrete field values

Post-S3 ACT counts (from origin/main read):
- `lineCount`: **184**
- `theoremCount`: **7** (`topCellsOfDim_eq_of_pure`,
  `topCellsOfDim_eq_empty_of_pure`, `MixedPseudomanifold.of_pure`,
  `card_of_mem_topCellsOfDim`, `hpseudo_of_mixed`,
  `sperner_mixed_panchromatic_at_dim`, and any cross-stratum
  wrapper if Option α is adopted)
- `definitionCount`: **3** (`topCellsOfDim`, `MixedPseudomanifold`,
  `boundaryDoorCount`)
- `axiomCount`: **0**
- `sorries`: **0**
- `status`: **`verified`** *iff S3 ACT build passes*; otherwise
  **`formalized`** with a build-pending note.
- `badge`: **`verified`** (matches the parent's `original` /
  `verified` posture).

If the cross-stratum wrapper is bundled (Option α in Component A),
`lineCount` becomes ~192-196 and `theoremCount` becomes 8.

### meta.json — descriptive fields

```jsonc
{
  "id": "sperner-simplicial-bridge-oq-01",
  "title": "Sperner's Lemma for Mixed-Dimension Simplicial Complexes (OQ-01)",
  "slug": "sperner-simplicial-bridge-oq-01",
  "description": "A strict generalisation of `sperner-simplicial-bridge` to mixed-dimension (stratified) simplicial complexes, where top simplices may have different dimensions. The key observation is that doors are dimension-graded: a codimension-1 face of a (d+1)-simplex has cardinality d, so the door-counting argument decomposes stratum by stratum. The `MixedPseudomanifold` predicate captures the per-dimension pseudomanifold condition; `sperner_mixed_panchromatic_at_dim` derives the per-stratum panchromatic existence as a direct application of the parent's `exists_panchromatic`.",
  "meta": {
    "author": "Lean Genius Research",
    "sourceUrl": "https://en.wikipedia.org/wiki/Sperner%27s_lemma",
    "date": "2026",
    "dateAdded": "<YYYY-MM-DD when S4 lands>",
    "mathlib_version": "4.26.0",
    "status": "verified",
    "badge": "verified",
    "axiomCount": 0,
    "theoremCount": 7,
    "definitionCount": 3,
    "lineCount": 184,
    "imports": ["Proofs.SpernerSimplicialBridge"],
    "tags": [
      "combinatorics", "topology", "sperner",
      "simplicial-complex", "mixed-pseudomanifold",
      "stratified", "open-question"
    ],
    "assumptions": "No new axioms or sorries; this file is a strict generalisation of `sperner-simplicial-bridge` that adds the `MixedPseudomanifold` predicate, the `topCellsOfDim` stratification, and the per-stratum theorem `sperner_mixed_panchromatic_at_dim`. The parent's `exists_panchromatic` is the workhorse — this file's main theorem is a one-line application after packaging the per-stratum hypotheses. The `MixedPseudomanifold.of_pure` sanity check verifies that pure pseudomanifolds lift to the mixed predicate, so the generalisation subsumes the parent.",
    "sorries": 0,
    "proofRepoPath": "Proofs/SpernerSimplicialBridgeOQ01.lean",
    "originalContributions": [
      "topCellsOfDim: dimension-graded stratification of a finite simplicial complex via Finset.filter on cell cardinality.",
      "MixedPseudomanifold: stratum-wise pseudomanifold predicate — for every d and every d-element face f, at most 2 dim-d cells contain f. Strictly generalises the parent's pure pseudomanifold condition.",
      "MixedPseudomanifold.of_pure: pure pseudomanifolds lift to the mixed predicate (with vacuous behaviour at strata other than the unique non-empty one). Sanity check that the generalisation subsumes the parent.",
      "boundaryDoorCount: noncomputable def packaging the parent's hbdry filter expression for a chosen dimension d, structurally a copy with topCellsOfDim K d substituted for topCells.",
      "sperner_mixed_panchromatic_at_dim: the per-stratum main theorem — for each dimension d with odd boundary-door count, the dim-d stratum contains a panchromatic top cell. Proof body is one line: a direct application of the parent's exists_panchromatic."
    ]
  },
  "sections": [/* see annotations.json plan below */],
  "crossReferences": [
    {
      "type": "generalisation-of",
      "slug": "sperner-simplicial-bridge",
      "rationale": "OQ-01 strictly generalises the pure pseudomanifold case to mixed-dimension complexes. MixedPseudomanifold.of_pure proves the inclusion."
    },
    {
      "type": "uses",
      "slug": "sperner-simplicial-bridge",
      "rationale": "The per-stratum proof is a direct application of the parent's exists_panchromatic on the chosen stratum."
    },
    {
      "type": "sibling-of",
      "slug": "sperner-simplicial-instance",
      "rationale": "Both slugs build on sperner-simplicial-bridge; sibling is the SimplicialComplex-instance bridging; this one is the stratification."
    }
  ]
}
```

### annotations.json — section design

Following the parent's pattern (sections grouped by "Stratification
machinery / Pure → Mixed coercion / Per-stratum theorem"), three
sections feel natural:

1. **Stratification** — `topCellsOfDim` + `MixedPseudomanifold`.
   Anchor: the observation that doors are dimension-graded.
2. **Pure → Mixed coercion** — `topCellsOfDim_eq_of_pure`,
   `topCellsOfDim_eq_empty_of_pure`, `MixedPseudomanifold.of_pure`.
   Anchor: the sanity-check that the generalisation subsumes the
   parent.
3. **Per-stratum Sperner** — `card_of_mem_topCellsOfDim`,
   `hpseudo_of_mixed`, `boundaryDoorCount`,
   `sperner_mixed_panchromatic_at_dim`. Anchor: the main theorem
   plus its three supporting helpers.

Section line ranges (post-S3-ACT, against the 184-LOC file):

| Section | Line range | Headline declaration |
|---|---|---|
| Stratification | ~54-68 | `MixedPseudomanifold` |
| Pure → Mixed coercion | ~70-109 | `MixedPseudomanifold.of_pure` |
| Per-stratum Sperner | ~111-180 | `sperner_mixed_panchromatic_at_dim` |

### index.ts — mechanical recipe

```ts
import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }

const leanSource = () => import('../../../../proofs/Proofs/SpernerSimplicialBridgeOQ01.lean?raw')

export const proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences
}

export const proofData: ProofData = {
  proof,
  source: leanSource,
  annotations: annotationsJson as Annotation[]
}

export default proofData
```

Direct copy of the parent's `index.ts` with the leanSource path
and the slug references swapped. The `slugToExportName` convention
(per `feedback_researcher_s3_gallery_clean_task_pattern.md`)
exports as `spernerSimplicialBridgeOq01Data` — verify against
`scripts/annotations/build.ts` at S4 time.

### S4 GALLERY landing checklist

1. Verify S3 ACT build passes (Doctor/Mechanic verification of
   PR #18537 first — do not ship S4 GALLERY against a broken
   parent build).
2. Re-check post-build `lineCount` / `theoremCount` /
   `definitionCount` — re-run the count if Option α (cross-stratum
   wrapper) is folded in during S4.
3. Create the three files as above.
4. No edits to `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
   beyond the optional cross-stratum wrapper (Option α).
5. No edits to `state.md` / `knowledge.md` /
   `src/data/research/problems/sperner-simplicial-bridge-oq-01.json`
   — drift sync remains auditor/mechanic.
6. PR title: `gallery(sperner-simplicial-bridge-oq-01): S4 GALLERY
   — mixed-pseudomanifold Sperner entry`. Add the
   `loom:review-requested` label only if you explicitly want
   Judge review (Math agents skip Judge by default per
   `CLAUDE.md` "PR Labels for Math Agents").
7. Re-check `gh pr list --search "sperner-simplicial-bridge-oq-01
   in:title is:open"` IMMEDIATELY BEFORE PUSH (race window).

## Orthogonality

| PR / file | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` | post-S3-ACT, on origin/main | **no edit** in this PREP |
| `research/problems/sperner-simplicial-bridge-oq-01/state.md` | post-S1, not yet synced | **no edit** in this PREP (drift sync is auditor/mechanic) |
| `research/problems/sperner-simplicial-bridge-oq-01/knowledge.md` | post-S1 | **no edit** |
| `research/problems/sperner-simplicial-bridge-oq-01/problem.md` | post-S1 | **no edit** |
| `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` | post-S1 | **no edit** |
| `src/data/proofs/sperner-simplicial-bridge-oq-01/*` | does not yet exist | **no edit / no create** in this PREP |
| #18537 (S3 ACT) | MERGED | predecessor; this PREP follows up |
| #18534 (sperner-simplicial-instance-oq-05 S2 PREP-D) | MERGED | different slug, sibling |
| (any open PR on this slug) | none as of 2026-05-13T04:09Z | n/a |

Single file touched: this session-notes markdown. Zero risk to S3
ACT's build, zero risk to any future S4 GALLERY landing, zero risk
to any in-flight sibling work.

## Honesty

- **This PREP does not improve any theorem count or close any
  sorry.** Its value is documentation and pre-flight planning:
  three components that any subsequent researcher (or this slug's
  S4 GALLERY author) can pick up directly.
- **The build-risk verification (Component B) is *not* a build.**
  It is a paper audit of the S3 ACT session note's risk register,
  cross-checked against the parent file and against Lean 4 /
  Mathlib v4.26.0 reducibility policy. Doctor/Mechanic must still
  verify the actual build of S3 ACT PR #18537.
- **The S4 GALLERY pre-flight (Component C) is a recipe, not the
  thing.** Field values are derived from the post-S3 origin/main
  file state; if Option α adds the cross-stratum wrapper, the
  counts shift by +1 theorem and +~10 LOC.
- **The cross-stratum existential form (Component A) is a *trivial
  corollary* of the per-stratum form**, not new mathematical
  content. Its 3-line proof body is mechanically derivable. Calling
  it a "contribution" would overstate; it is convenience packaging.
- **No follow-up Open Questions are generated by this PREP.** The
  pending items (S3 ACT build verification, S4 GALLERY landing,
  drift sync) are all already on the slug's queue.
- **Saturation context.** This PREP is shipped ~30 min after S3 ACT
  PR #18537 merged (2026-05-13T04:08:28Z). It respects the
  30-min-post-merge orthogonal-PREP-window pattern documented in
  `feedback_researcher_6_2026_05_12_triple_prep_doc_session.md` and
  related memories.

## Pre-flight checklist (for *this* PREP)

| Item | Verified by |
|---|---|
| Post-S3 file state on origin/main | `git show origin/main:proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` read |
| Parent `exists_panchromatic` signature lines 564-588 | direct file read |
| S3 ACT session note's three risks | direct file read of `2026-05-13-s3-act-stratum-d-implementation.md:163-170` |
| Parent slug `sperner-simplicial-bridge` meta.json structure | direct file read of `src/data/proofs/sperner-simplicial-bridge/meta.json` |
| Parent slug `index.ts` shape | direct file read of `src/data/proofs/sperner-simplicial-bridge/index.ts` |
| No open same-slug PR | `gh pr list --search "sperner-simplicial-bridge-oq-01 in:title is:open"` → empty |
| No same-file race for this PREP | Only file touched: `sessions/2026-05-13-s3b-prep-cross-stratum-and-post-s3-build-risk-audit.md` (new path) |

## References

- **S3 ACT session note**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-13-s3-act-stratum-d-implementation.md`
- **S2c PREP session note**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-13-s2c-prep-stratum-d-signature-plumbing.md`
- **S2 SCAFFOLD session note**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-12-s2-scaffold.md`
- **S2b OBSERVE session note**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-12-s2b-observe-stratum-overlap-door-definition.md`
- **Parent Lean file**: `proofs/Proofs/SpernerSimplicialBridge.lean`
  (`exists_panchromatic` at line 564, `vertexEnum` at line 65,
  `adjFn` declarations in §Adjacency).
- **Scaffold Lean file (post-S3 ACT)**: `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
  (184 LOC; `boundaryDoorCount` at lines 145-153,
  `sperner_mixed_panchromatic_at_dim` at lines 173-184).
- **Parent gallery slug**: `src/data/proofs/sperner-simplicial-bridge/{meta.json, annotations.json, index.ts}`.
- **Knowledge.md cross-stratum statement**: `research/problems/sperner-simplicial-bridge-oq-01/knowledge.md:38-40`.
- **PR predecessors**: #18234, #18363, #18434, #18451, #18537.
