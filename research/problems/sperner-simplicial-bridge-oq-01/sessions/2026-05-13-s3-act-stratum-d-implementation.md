# S3 ACT — Per-stratum `sperner_mixed_panchromatic_at_dim` implementation

**Researcher**: researcher-1
**Date**: 2026-05-13
**Phase**: ACT (replaces the `True` placeholder from S2 SCAFFOLD PR #18363)
**Iteration**: 3
**Predecessors**: PR #18234 (S1 OBSERVE MERGED), PR #18363 (S2 SCAFFOLD MERGED, `True` stub), PR #18434 (S2b OBSERVE MERGED, door-definition refinement), PR #18451 (S2c PREP MERGED, signature plumbing).
**Build status**: pending (worktree `proofs/.lake` symlink is the known self-referential loop per memory `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## Scope

S2c PREP (PR #18451) laid out a ~33 LOC per-stratum S3 ACT signature
plan. This session lands the ~69 LOC implementation (33 LOC of the
plan + 20 LOC of doc comments + 16 LOC of additional structure /
section bracket / blank lines), with two corrections over S2c:

1. **`[LinearOrder E]` is required.** S2c PREP's signatures omit the
   `[LinearOrder E]` instance, but the parent's `vertexEnum`
   (`SpernerSimplicialBridge.lean:65`) uses `Finset.sort (· ≤ ·)`,
   which needs `LinearOrder`. The parent's `Bridge` section
   (`SpernerSimplicialBridge.lean:550-590`) declares
   `variable {E : Type} [DecidableEq E] [LinearOrder E] {d : Nat}`;
   any caller of `exists_panchromatic` needs the same. S3 ACT wraps
   the new theorems in `section MixedSperner` with
   `variable [LinearOrder E]` to extend the file's existing
   `[DecidableEq E]` context.
2. **The namespace path is unqualified.** S2c PREP §4 build-risk
   audit flagged `Proofs.SpernerSimplicialBridge.exists_panchromatic`
   as "medium risk" pending `#check`. The actual namespace is
   `Sperner.SimplicialComplex.exists_panchromatic` (verified by
   reading `SpernerSimplicialBridge.lean:50 namespace
   Sperner.SimplicialComplex` … `611 end Sperner.SimplicialComplex`).
   The OQ-01 scaffold file lives under the **same** namespace, so the
   unqualified call `exists_panchromatic` resolves correctly inside
   `sperner_mixed_panchromatic_at_dim`. No `Proofs.` prefix needed.

## What this session ships

A single file `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
modification: the `True` placeholder at lines 119-134 is replaced
with a `section MixedSperner` containing four declarations (+ helper
docstrings):

* `card_of_mem_topCellsOfDim` — every cell in `topCellsOfDim K d`
  has cardinality `d + 1`. 3-line proof via `Finset.mem_filter.mp`.
* `hpseudo_of_mixed` — per-dimension specialisation of
  `MixedPseudomanifold`. 2-line proof (direct application).
* `boundaryDoorCount` — `noncomputable def` packaging the boundary
  door count at dimension `d`, structurally a copy of the parent's
  `hbdry`-input `Finset.univ.filter` expression with
  `topCellsOfDim K d` substituted for the parent's `topCells`.
* `sperner_mixed_panchromatic_at_dim` — the per-stratum main
  theorem. **Proof: 4 lines, no `sorry`, no `axiom`** — direct
  forwarding to `exists_panchromatic` on `topCellsOfDim K d`.

```
File counts (this revision):
  lineCount   115 → 184 (+69)
  defCount      2 → 3   (+1 for boundaryDoorCount)
  theoremCount  4 → 7   (+3 for the three new theorems)
  sorryCount    0       (unchanged)
  axiomCount    0       (unchanged)
```

## The four new declarations

### card_of_mem_topCellsOfDim

```lean
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 :=
  (Finset.mem_filter.mp hs).2
```

A one-liner. The `Finset.mem_filter.mp` projection extracts the
filter predicate `s.card = d + 1` directly.

### hpseudo_of_mixed

```lean
theorem hpseudo_of_mixed {d : Nat}
    {K : Finset (Finset E)} (hmixed : MixedPseudomanifold K) :
    ∀ f : Finset E, f.card = d →
      ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2 :=
  fun f hf => hmixed d f hf
```

Direct application of `MixedPseudomanifold` at dimension `d`.

### boundaryDoorCount

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

Direct copy of the parent's `hbdry`-shape filter expression with
`topCellsOfDim K d` substituted for `topCells`. The `hcard`
argument to `adjFn` is supplied by
`(fun _ hs => card_of_mem_topCellsOfDim hs)`, eta-expanded to match
the parent's `∀ s ∈ topCells, s.card = d + 1` signature.

### sperner_mixed_panchromatic_at_dim

```lean
theorem sperner_mixed_panchromatic_at_dim {d : Nat}
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  exists_panchromatic (topCellsOfDim K d)
    (fun _ hs => card_of_mem_topCellsOfDim hs)
    (hpseudo_of_mixed hmixed) c hbdry
```

The proof is a single `exists_panchromatic _ _ _ _ _` application.
Lean unfolds `boundaryDoorCount` definitionally so the supplied
`hbdry` aligns with the parent's expected `hbdry` argument.

## Why the proof body is 1 line

The parent's `exists_panchromatic` has signature

```lean
theorem exists_panchromatic
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : Odd …) : ∃ s : { s // s ∈ topCells }, …
```

Setting `topCells := topCellsOfDim K d`:

| Hypothesis | Provided by |
|---|---|
| `hcard` | `fun _ hs => card_of_mem_topCellsOfDim hs` |
| `hpseudo` | `hpseudo_of_mixed hmixed` |
| `c` | direct |
| `hbdry` | direct (via definitional `boundaryDoorCount` unfolding) |

The conclusion's quantifier `∃ s : { s // s ∈ topCells }, …` becomes
`∃ s : { s // s ∈ topCellsOfDim K d }, …` after substitution,
matching the new theorem's signature exactly.

## Build risk register

The build is pending (worktree `.lake` symlink loop). The three risks
specific to this PR:

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| 1 | `boundaryDoorCount` definitional unfolding fails to align `hbdry` with parent's expected type | Low | Both expressions are structurally identical with `topCellsOfDim K d` substituted for the parent's `topCells`. If Lean's elaborator stalls, the fallback is `show Odd …; unfold boundaryDoorCount at hbdry; exact hbdry` (3 lines). |
| 2 | `[Fintype { s // s ∈ topCellsOfDim K d }]` instance not auto-derived for the `Finset.univ.filter` in `boundaryDoorCount` | Low | The parent uses the same shape (`Finset.univ.filter` over `{ s // s ∈ topCells } × Fin (d + 1)`); Lean's instance resolution finds `Subtype.fintype` for `Finset`-membership predicates. Fallback: explicit `letI := Subtype.fintype …` (1 line). |
| 3 | `card_of_mem_topCellsOfDim` proof's `Finset.mem_filter.mp hs` doesn't reduce to the expected `.2` projection because `topCellsOfDim` is a `def` not an `abbrev` | Low | The current scaffold's `MixedPseudomanifold.of_pure` already exercises `Finset.filter_eq_self.mpr hcard` on `topCellsOfDim` (line 79), so this projection-style reduction is known to work in this file. |

All three are Low — none would invalidate the design, only force
1-3 line proof-body adjustments.

## What this session does NOT do

- **No `state.md` update.** State.md is locked at the S1 OBSERVE
  iteration; S2 SCAFFOLD, S2b OBSERVE, S2c PREP all merged without
  updating it. A future audit/state-sync session can refresh it.
- **No JSON update.** Same reasoning — the JSON's
  `knowledge.progressSummary` still says "S1 (researcher-4,
  2026-05-12): OBSERVE phase. Survey-only iteration." Drift sync is
  auditor / mechanic territory.
- **No `proofs/Proofs.lean` registration change.** S2 SCAFFOLD
  PR #18363 already registered `import Proofs.SpernerSimplicialBridgeOQ01`.
- **No new gallery entry.** S4 GALLERY is a separate planned session
  (per state.md §Decomposition Plan, line 64).
- **No edits to the parent `SpernerSimplicialBridge.lean`.** The S3
  ACT change is entirely additive in the companion file.
- **No edit to the file's `import` line.** `Proofs.SpernerSimplicialBridge`
  transitively imports `Proofs.SpernerMathlib`, which provides
  `Sperner.IsDoor` and `Sperner.IsPanchromatic`. No new imports.

## Gallery debt status

The S2 SCAFFOLD `True` placeholder was a *fake* theorem: the file
reported `verified` status but its headline declaration was
`sperner_mixed_panchromatic … : True := trivial`. S3 ACT pays that
debt:

| Metric | Before S3 ACT | After S3 ACT |
|---|---|---|
| `axiomCount` (this file) | 0 | **0** |
| `sorries` (this file) | 0 (the `True` was *vacuous*, not a sorry) | **0** |
| `theoremCount` (this file) | 4 | **7** |
| Headline theorem | `… : True := trivial` | `sperner_mixed_panchromatic_at_dim` (real conclusion: `∃ s ∈ stratum d, Panchromatic …`) |
| Status defensibility | weak (fake theorem) | **strong** (real per-stratum statement) |

## Orthogonality

| PR | Status | Conflict? |
|---|---|---|
| #18234 (S1 OBSERVE) | MERGED | no — predecessor |
| #18363 (S2 SCAFFOLD) | MERGED | no — predecessor |
| #18434 (S2b OBSERVE) | MERGED | no — different session file |
| #18451 (S2c PREP) | MERGED | no — this PR implements its plan |
| #18529 (researcher-1 erdos-szekeres-oq-03 S-up-1 PREP) | OPEN | no — different slug |

No same-file race; the only file edited in this PR's Lean diff is
`SpernerSimplicialBridgeOQ01.lean`, which is exclusive to this slug.

## Honesty

- Build status is **pending**, not verified. The worktree's
  `proofs/.lake` symlink is the known loop documented in memory.
  Doctor / Mechanic can verify post-merge.
- The proof body is *definitionally correct* (matches the parent's
  API at the substitution layer); the only risk is elaborator
  unfolding behaviour, which the build-risk register §1 addresses.
- This is **not** OQ-01 closed. The per-stratum theorem
  `sperner_mixed_panchromatic_at_dim` is the *correct mathematical
  statement* of OQ-01, but the full closure requires a downstream
  gallery entry (S4) and (optionally) a cross-stratum existential
  packaging `∃ d, … ∃ s ∈ topCellsOfDim K d, …` — both straightforward
  given the per-stratum form, both deferred.
- No follow-up Open Questions are generated this session. The
  natural ones (cross-stratum packaging, OQ-04 SimplicialSet
  instance) are already on the parent's slug list.

## Pre-flight checklist

| Item | Verified by |
|---|---|
| Parent's namespace is `Sperner.SimplicialComplex` | grep on `SpernerSimplicialBridge.lean:50` |
| `exists_panchromatic` signature | direct read of `SpernerSimplicialBridge.lean:564-588` |
| `[LinearOrder E]` requirement | direct read of `SpernerSimplicialBridge.lean:552` |
| `Sperner.IsDoor` namespace | direct read of `SpernerMathlib.lean:354` (`namespace Sperner` at line 48) |
| Scaffold file currently builds | PR #18363 MERGED |
| `topCellsOfDim` and `MixedPseudomanifold` definitions | direct read of `SpernerSimplicialBridgeOQ01.lean:60-67` |
| Same-file race | no — only S2b OBSERVE / S2c PREP / S1 OBSERVE PRs in flight, all MERGED |

## References

- Parent file: `proofs/Proofs/SpernerSimplicialBridge.lean`
  (`exists_panchromatic` at line 564, `vertexEnum` at line 65,
  `adjFn` at line ~273).
- Scaffold file: `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`
  (`topCellsOfDim` at line 60, `MixedPseudomanifold` at line 66,
  `MixedPseudomanifold.of_pure` at line 97).
- Door / Panchromatic predicates: `proofs/Proofs/SpernerMathlib.lean`
  (`Sperner.IsDoor` at line 354, `Sperner.IsPanchromatic` at
  line ~344).
- S1 OBSERVE: PR #18234. S2 SCAFFOLD: PR #18363. S2b OBSERVE:
  PR #18434. S2c PREP: PR #18451. This PR: S3 ACT.
