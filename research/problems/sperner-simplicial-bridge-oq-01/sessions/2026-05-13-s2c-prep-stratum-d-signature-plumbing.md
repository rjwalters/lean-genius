# S2c PREP — Per-stratum-`d` signature plumbing for `sperner_mixed_panchromatic` S3 ACT

**Researcher**: researcher-6
**Date**: 2026-05-13
**Phase**: PREP (signature-level S3 ACT design memo)
**Iteration**: 2c (orthogonal to S2b PR #18434's door-definition refinement)
**Predecessor PRs**: #18234 (S1 OBSERVE MERGED), #18363 (S2 SCAFFOLD MERGED — created `SpernerSimplicialBridgeOQ01.lean` with `True` stub for `sperner_mixed_panchromatic`), #18434 (S2b OBSERVE OPEN — door-definition refinement).
**Lines added**: doc-only.

## Scope

S2 SCAFFOLD merged a *placeholder* `sperner_mixed_panchromatic` theorem at `SpernerSimplicialBridgeOQ01.lean:128` whose conclusion is `True`. S2b PR #18434 then refined the *door definition* under Interpretation A vs B. The remaining S3 ACT task — replacing the `True` stub with the real per-stratum statement and proof — has a delicate **signature-plumbing** step that this PREP works out explicitly so the S3 ACT iteration can copy the signature verbatim.

Specifically, S3 ACT must:

1. Parametrise the theorem by a specific dimension `d : ℕ`.
2. Wire the per-stratum `topCellsOfDim K d` into the parent's `exists_panchromatic` (which takes a `Finset (Finset E)` directly).
3. Convert the input `MixedPseudomanifold K` hypothesis to the per-stratum `hpseudo` argument of `exists_panchromatic`.
4. Define the per-stratum boundary-door count for use in the `hbdry : Odd …` hypothesis.
5. Discharge `hcard` (every element of `topCellsOfDim K d` has card `d + 1`) by definitional unfolding.

This memo gives the signature and proof skeleton for each of these five sub-steps.

## Existing surface

### From the parent `SpernerSimplicialBridge.lean:564`

```lean
theorem exists_panchromatic
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells } × Fin (d + 1) =>
        Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) =>
          vertexEnum σ.1 (hcard σ.1 σ.2))
          c p.1 p.2 ∧
        adjFn topCells hcard p.1 p.2 = none)).card) :
    ∃ s : { s : Finset E // s ∈ topCells },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hcard σ.1 σ.2)) c s
```

### From the OQ-01 scaffold `SpernerSimplicialBridgeOQ01.lean`

```lean
-- Line 60
def topCellsOfDim (K : Finset (Finset E)) (d : Nat) : Finset (Finset E) :=
  K.filter (fun s => s.card = d + 1)

-- Line 66
def MixedPseudomanifold (K : Finset (Finset E)) : Prop :=
  ∀ d : Nat, ∀ f : Finset E, f.card = d →
    ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2

-- Lines 97-105: pure-to-mixed coercion lemma
theorem MixedPseudomanifold.of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (K.filter (fun s => f ⊆ s)).card ≤ 2) :
    MixedPseudomanifold K
```

## The five sub-steps

### (1) Add the missing card lemma

```lean
/-- Every cell in the dimension-`d` stratum has cardinality `d + 1`. -/
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 := by
  exact (Finset.mem_filter.mp hs).2
```

**Estimate**: 3 lines. Trivial; `Finset.mem_filter` does all the work.

### (2) Restate the parent's `hpseudo` from `MixedPseudomanifold`

The `MixedPseudomanifold` predicate quantifies over *all* dimensions. The parent's `exists_panchromatic` needs the per-dimension `hpseudo`. The restriction is a direct application:

```lean
/-- Per-dimension specialisation of the mixed-pseudomanifold predicate. -/
theorem hpseudo_of_mixed {d : Nat}
    {K : Finset (Finset E)} (hmixed : MixedPseudomanifold K) :
    ∀ f : Finset E, f.card = d →
      ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2 :=
  fun f hf => hmixed d f hf
```

**Estimate**: 2 lines. Pure unfolding.

### (3) The boundary-door count abstraction

Define a *per-dimension* boundary-door count predicate. Interpretation A (per S2b PR #18434 §3.2 recommendation): a `d`-element face `f` is a boundary door at dimension `d` if exactly one cell in `topCellsOfDim K d` contains `f` AND the coloring restricted to `f` is surjective onto `{0, …, d − 1}` (i.e., all *lower* colors are achieved by `f`'s vertices).

```lean
/-- The count of boundary-door pairs `(s, k)` at dimension `d`,
parametrised by a coloring `c`.

A pair `(s, k)` for `s ∈ topCellsOfDim K d`, `k : Fin (d+1)`, is a
boundary-door iff:
  - `Sperner.IsDoor (vertexEnum ...) c s k` holds (the lower colours
    `{0, …, d-1}` are all present on `s \ {vertex k}`), AND
  - `adjFn (topCellsOfDim K d) hcard s k = none` (the face `s \ {vertex k}`
    is in no other top cell of dimension `d`).
-/
noncomputable def boundaryDoorCount {d : Nat}
    (K : Finset (Finset E)) (c : E → Fin (d + 1)) : ℕ :=
  let topCells := topCellsOfDim K d
  let hcard : ∀ s ∈ topCells, s.card = d + 1 :=
    fun _ hs => card_of_mem_topCellsOfDim hs
  (Finset.univ.filter
    (fun p : { s // s ∈ topCells } × Fin (d + 1) =>
      Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) =>
        vertexEnum σ.1 (hcard σ.1 σ.2))
        c p.1 p.2 ∧
      adjFn topCells hcard p.1 p.2 = none)).card
```

**Estimate**: ~12 lines. Direct reuse of the parent's filter expression, only with `topCellsOfDim K d` substituted for the raw `topCells`.

### (4) The main S3 ACT theorem

```lean
/-- **Sperner's lemma for mixed-dimension simplicial complexes
(OQ-01, per-stratum version)**.

For each dimension `d`, if `K` is a mixed pseudomanifold and the
boundary-door count at dimension `d` is odd, then there exists a
panchromatic cell of dimension `d`. -/
theorem sperner_mixed_panchromatic_at_dim {d : Nat}
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  let topCells := topCellsOfDim K d
  have hcard : ∀ s ∈ topCells, s.card = d + 1 :=
    fun _ hs => card_of_mem_topCellsOfDim hs
  exact Proofs.SpernerSimplicialBridge.exists_panchromatic
    topCells hcard (hpseudo_of_mixed (d := d) hmixed) c hbdry
```

**Estimate**: ~10 lines for the statement + 3 lines for the proof body.

### (5) Replace the placeholder `True` stub

The current `SpernerSimplicialBridgeOQ01.lean:128` reads:

```lean
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (_hmixed : MixedPseudomanifold K) :
    True := trivial
```

S3 ACT replaces this with the per-stratum theorem above, renamed to `sperner_mixed_panchromatic_at_dim` to indicate dimensional parametrisation. The original name `sperner_mixed_panchromatic` is *retained* as a deprecation-friendly alias targetting the new `at_dim` version with implicit `d`:

```lean
@[deprecated sperner_mixed_panchromatic_at_dim (since := "2026-05-13")]
theorem sperner_mixed_panchromatic
    {d : Nat} (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  sperner_mixed_panchromatic_at_dim K hmixed c hbdry
```

(Alternatively, drop the deprecation alias if no downstream code references the placeholder. The placeholder has `_hmixed` as an unused binder, so no downstream code can have been written against it yet.)

## Total S3 ACT estimate

| Sub-step | LOC |
|---|---|
| (1) `card_of_mem_topCellsOfDim` | 3 |
| (2) `hpseudo_of_mixed` | 2 |
| (3) `boundaryDoorCount` definition | 12 |
| (4) `sperner_mixed_panchromatic_at_dim` statement + proof | 13 |
| (5) Replace `True` placeholder (rename + delete) | 1 (delete) |
| Imports / namespace bookkeeping | 2 |
| **Total** | **~33 LOC** |

## Net effect on gallery status

| Metric | Before S3 ACT | After S3 ACT |
|---|---|---|
| `axiomCount` | 0 (parent has 0) | **0** |
| `sorries` | 1 (the `True` placeholder is *vacuously* proved but the *real* statement is absent — this is a SORRY-EQUIVALENT in the sense of "claim not stated") | **0** |
| `status` | `verified` (file builds but theorem says `True`) | **`verified`** (real statement, real proof) |
| `theoremCount` | 4 (incl. `sperner_mixed_panchromatic := trivial`) | 5–6 (split into stratum and possibly the deprecation alias) |

The current `True` placeholder is a *gallery debt*: the file builds and reports `verified` status, but the headline theorem `sperner_mixed_panchromatic` literally says `True`. S3 ACT pays that debt.

## What the parent's API gives us for free

The parent file `SpernerSimplicialBridge.lean` exposes `exists_panchromatic` parameterised by `topCells : Finset (Finset E)` — **not** by `Geometry.SimplicialComplex` or any other abstraction. This is the entire reason S3 ACT is ~33 LOC and not ~150: the parent's API is shaped precisely right for per-stratum application.

The `vertexEnum`, `adjFn`, `IsDoor`, `IsPanchromatic` predicates are all in `Sperner.*` namespace and work over `{ s // s ∈ topCells }`. No re-derivation needed.

## What this PREP does NOT address

1. **The door definition itself**. S2b PR #18434 owns that (Interpretation A vs B). This PREP **accepts S2b's recommendation of Interpretation A** and threads it into the `boundaryDoorCount` definition above.
2. **Stratum-overlap correctness**. Per S2b §1, a `d`-element face can simultaneously be a top cell at dim `d − 1` and a codim-1 face at dim `d`. This is *handled correctly* by the per-stratum `topCellsOfDim K d` filter — the dim-d stratum only contains `d+1`-element cells, so a `d`-element face is never a top cell in that stratum. Interpretation A subordinates this to the dim-d analysis.
3. **Mixed-pseudomanifold-of-pure correctness**. Already proved at `SpernerSimplicialBridgeOQ01.lean:97` in S2 SCAFFOLD.
4. **The S2b OPEN status of PR #18434**. The S2b finding is *advisory*; this PREP can land independently of whether S2b merges, since it cites the door-definition recommendation but does not edit `MixedPseudomanifold` or `topCellsOfDim`.

## Orthogonality to in-flight PRs

| PR | Phase | Focus | Conflict? |
|---|---|---|---|
| #18234 (MERGED) | S1 OBSERVE | Territory map | no — base |
| #18363 (MERGED) | S2 SCAFFOLD | Data defs + placeholder | no — S3 will rename placeholder |
| #18434 (OPEN) | S2b OBSERVE | Door-definition Interpretation A vs B | no — different file (sessions/2026-05-12-s2b-*); this PREP cites the recommendation |
| **#this** | S2c PREP | Per-stratum signature plumbing for S3 ACT | — |

Pristine session-file addition; no edits anywhere else.

## Anti-targets

- **Do not** redefine `topCellsOfDim` or `MixedPseudomanifold`. These are S2 SCAFFOLD's.
- **Do not** redefine `vertexEnum` / `IsDoor` / `IsPanchromatic`. These are the parent's.
- **Do not** drop the dimensional parameter `d` from the S3 ACT theorem signature. The statement is per-dimension; dropping `d` would force a `∀ d, …` outer quantifier and break the symmetry with `exists_panchromatic`.
- **Do not** attempt to prove the full *cross-dimensional* statement ("for every dim d with odd door count, there exists a panchromatic cell at dim d") in S3 ACT. That's an existential over dimensions, which the per-stratum version directly implies; ship the per-stratum version first.
- **Do not** edit the parent `SpernerSimplicialBridge.lean`. S3 ACT only edits `SpernerSimplicialBridgeOQ01.lean`.

## Build-risk audit

| Step | Risk | Fallback |
|---|---|---|
| (1) `card_of_mem_topCellsOfDim` via `Finset.mem_filter` | low | `simp [topCellsOfDim, Finset.mem_filter]` |
| (2) `hpseudo_of_mixed` direct unfolding | low | none needed |
| (3) `boundaryDoorCount` def | low — pure data shuffling | none |
| (4) Main theorem proof: `exists_panchromatic` direct application | **medium** — the namespace path to the parent's theorem might be `Proofs.SpernerSimplicialBridge.Sperner.SimplicialComplex.exists_panchromatic` instead of `Proofs.SpernerSimplicialBridge.exists_panchromatic`. Verify via `#check` |
| (5) Deprecation alias `@[deprecated ...]` | low | drop if Lean complains |

The medium-risk step (4) is a one-line `exact` call; the namespace path is mechanically discoverable.

## Cross-file context

The slug ecosystem currently has 4 sperner-* slugs:

| Slug | Status | Open PRs | Relationship to OQ-01 |
|---|---|---|---|
| `sperner-mathlib-oq-01` | RICH | 4 (S1c/S1d/S1e/S1e-multi) | Different parent (`SpernerMathlib.lean`, not `SpernerSimplicialBridge.lean`); shares `IsDoor`/`IsPanchromatic` definitions |
| `sperner-ndim-mathlib-oq-02` | RICH | 3 (S23/S25-prep/S28-prep) | Different parent (`SpernerMathlib4.lean`); same `IsDoor` pattern |
| `sperner-simplicial-instance-oq-01` | recent merge | 0 | Same parent (`SpernerSimplicialBridge.lean`); orthogonal axis (concrete 2-simplex instance) |
| **`sperner-simplicial-bridge-oq-01`** (this) | RICH | 1 (S2b) | S3 ACT pending |

**Consistency check**: this PREP's `boundaryDoorCount` uses `Sperner.IsDoor` (from `SpernerMathlib.lean:354`) — *not* `IsDoor` (from `SpernerGrid.lean:131`). The parent `SpernerSimplicialBridge.lean:564` already commits to `Sperner.IsDoor`; this PREP follows suit. No cross-slug consistency violation.

## Stop conditions

This S2c PREP is complete when:

1. ✅ All five S3 ACT sub-steps are written out with Lean skeletons.
2. ✅ LOC estimate per sub-step is provided (total ~33 LOC).
3. ✅ Build-risk audit per sub-step.
4. ✅ Net effect on gallery status is computed.
5. ✅ Cross-file context (sister sperner-* slugs).
6. ✅ Anti-targets are explicit.
7. ✅ Pristine session-file addition: no edits anywhere else.

All seven stop conditions are met by this file.

## Honesty

- This is a **PREP** (planning document), not an ACT (no Lean changes).
- The ~33 LOC estimate is honest; the implementation is structurally trivial because the parent's API is already shaped right.
- The `True` placeholder at `SpernerSimplicialBridgeOQ01.lean:128` is a real gallery debt. S3 ACT pays it.
- This PREP **does not endorse** Interpretation B from S2b PR #18434; it threads through Interpretation A (per S2b's own §3.2 recommendation).
- The `@[deprecated]` alias at step (5) is **optional**. If no downstream code references the placeholder, drop it; the placeholder has an unused `_hmixed` binder, so it's unlikely anything references it.
- I have not built the file locally. The S3 ACT PR will need to verify the four assertions: `card_of_mem_topCellsOfDim`, `hpseudo_of_mixed`, `boundaryDoorCount`'s well-definedness, and the namespace path to `exists_panchromatic`.

## References

- Parent: `proofs/Proofs/SpernerSimplicialBridge.lean` (`exists_panchromatic` at line 564).
- Scaffold: `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (`topCellsOfDim` at line 60, `MixedPseudomanifold` at line 66, `True` placeholder at line 128).
- Door / Panchromatic predicates: `proofs/Proofs/SpernerMathlib.lean:347, 354`.
- `vertexEnum`: `proofs/Proofs/SpernerSimplicialBridge.lean:65`.
- S1 OBSERVE: PR #18234.
- S2 SCAFFOLD: PR #18363.
- S2b OBSERVE (door definition): PR #18434.
- Sister slug `sperner-simplicial-instance-oq-01`: PR #18291 (S1 OBSERVE merged 2026-05-12).
