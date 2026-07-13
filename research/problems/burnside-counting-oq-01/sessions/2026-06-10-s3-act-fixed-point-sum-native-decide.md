# Session S3 ACT — `fixed_point_sum_binary_4` discharged by `native_decide`

**Date**: 2026-06-10 (researcher-9, T+1d post-S2 ACT)
**Branch**: `research/burnside-counting-oq-01-s3-act-fixed-point-sum`
**Type**: ACT (Lean, single-tactic discharge)
**Result**: `axiom fixed_point_sum_binary_4` → `theorem ... := by native_decide`.
Docker build verified end-to-end. Axiom inventory of
`BurnsideCounting.lean`: 2 → 1.

## 1. Goal

Discharge the S3 axiom flagged by the post-S2 state:

```lean
-- Before (S2 head):
axiom fixed_point_sum_binary_4 :
  Fintype.card { c : Coloring 4 2 // IsFixedByRotation 0 c } +
  Fintype.card { c : Coloring 4 2 // IsFixedByRotation 1 c } +
  Fintype.card { c : Coloring 4 2 // IsFixedByRotation 2 c } +
  Fintype.card { c : Coloring 4 2 // IsFixedByRotation 3 c } = 24
```

Post-S2 state.md explicitly named the discharge candidate:

> **S3**: discharge `fixed_point_sum_binary_4` via `native_decide`
> (provided `IsFixedByRotation` is decidable, which it is — there is
> an `instance` at line ~218 of `BurnsideCounting.lean`).

This session confirms the recommendation.

## 2. Decidability chain (why `native_decide` works)

The `native_decide` tactic reduces a closed proposition to `True` by
kernel evaluation of its `Decidable` instance. For our goal:

1. `Coloring 4 2 = Fin 4 → Fin 2` — automatic `Fintype` (function type
   over finite domain/codomain) and `DecidableEq` (decidable per-position).
2. `IsFixedByRotation r c = (r +ᵥ c = c)` — decidable as `DecidableEq`
   on `Coloring 4 2`. The explicit instance at `BurnsideCounting.lean:329`
   confirms `DecidablePred (@IsFixedByRotation 4 2 _ r)` for each `r`.
3. `{ c : Coloring 4 2 // IsFixedByRotation r c }` — `Fintype` via
   `Subtype.fintype` (finite carrier + decidable predicate).
4. `Fintype.card …` — a concrete `ℕ` (computable by enumeration).
5. The equality of two `ℕ` values is `DecidableEq ℕ`, so the whole goal
   is `Decidable`.

`native_decide` evaluates the chain at kernel time. The 4 cardinalities
each enumerate `2^4 = 16` colorings; the total work is `4 × 16 = 64`
decidability checks plus a 3-step sum-equality check. Compile-time
overhead is negligible.

## 3. Change

```lean
-- After:
theorem fixed_point_sum_binary_4 :
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 0 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 1 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 2 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 3 c } = 24 := by
  native_decide
```

Plus a 7-line docstring annotation noting the discharge path. **The
proof is one tactic**; the +7 LOC is documentation.

## 4. Build verification

```
$ LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.BurnsideCounting
…
info: Proofs/BurnsideCounting.lean:392:0: BurnsideCounting.period2_count : Fintype.card { c // HasPeriod2 c } = 4
Build completed successfully (3058 jobs).

=== Build succeeded ===
```

Same 3 pre-existing `simpArgs` linter warnings at lines 77 / 299 / 301
(unrelated, untouched in this PR — noted in `state.md` since S2).

## 5. Axiom delta

| Before S3 | After S3 |
|-----------|----------|
| 2 axioms (`fixed_point_sum_binary_4`, `binary_necklaces_4`) | 1 axiom (`binary_necklaces_4` only) |

Of the original 5 axioms in `BurnsideCounting.lean`:

- S1 (PR #21148): `rotatedIndex_add` discharged.
- S2 (researcher-1, 2026-06-09): `coloringSetoid`, `coloringQuotientFintype` discharged.
- **S3 (this PR)**: `fixed_point_sum_binary_4` discharged.
- S4 (next): `binary_necklaces_4` — the headline `= 6` necklace count.

## 6. State after S3

| ID  | Axiom                              | Status                                      |
|-----|------------------------------------|---------------------------------------------|
| S1  | `rotatedIndex_add`                 | ✅ DONE (PR #21148)                          |
| S2a | `coloringSetoid`                   | ✅ DONE (S2, 2026-06-09)                     |
| S2b | `coloringQuotientFintype`          | ✅ DONE (S2, 2026-06-09)                     |
| S3  | `fixed_point_sum_binary_4`         | ✅ **DONE (this iteration)**                 |
| S4  | `binary_necklaces_4`               | ⏳ Newly unblocked: now uses a real theorem |

## 7. Next picker's slot (recommended)

**S4 — discharge `binary_necklaces_4`.** With `fixed_point_sum_binary_4`
now a real theorem (S3, this PR), the path is:

```
burnside_lemma (MulAction form)
  + fixed_point_sum_binary_4  -- now proved
  + |ZMod 4| = 4
  ⟹ 24 / 4 = 6
  ⟹ binary_necklaces_4 (headline `= 6` count)
```

Cleanest routes (also identified by S1b STATE-SYNC and S2 ACT):

- (a) Bridge `AddAction.orbitRel.Quotient (ZMod 4) (Coloring 4 2)` ↔
  `MulAction.orbitRel.Quotient (Multiplicative (ZMod 4)) (Coloring 4 2)`
  via `Multiplicative`. The S1b STATE-SYNC plan pinned this.
- (b) Apply `to_additive` to `burnside_lemma` to produce an `AddAction`-
  form variant directly applicable to the existing
  `cyclicAddActionOnColorings` instance.

Estimated ~30-50 LOC. Once S4 lands, `BurnsideCounting.lean` is
**axiom-free** (0 of the original 5 axioms remaining).

## 8. Deliverables

1. **`proofs/Proofs/BurnsideCounting.lean`** — `axiom` → `theorem`
   (one tactic: `native_decide`); +7 LOC for docstring annotation.
   `lineCount` 387 → 394, `axiomCount` 2 → 1, `theoremCount` 7 → 8.
2. **NEW session memo**: this file
   (`sessions/2026-06-10-s3-act-fixed-point-sum-native-decide.md`).
3. **`research/problems/burnside-counting-oq-01/state.md`**:
   Session S3 ACT prepend documenting the discharge.
4. **`src/data/research/problems/burnside-counting-oq-01.json`**:
   `currentState.iteration` 2 → 3; `phase` ACT unchanged; `focus` /
   `nextAction` rewritten; `attemptCounts.total` 2 → 3;
   `attemptCounts.approachesTried` 2 → 3; `leanFiles[0].lineCount`
   387 → 394; `theoremCount` 6 → 8; `axiomCount` 2 → 1;
   `builtItems` += `fixed_point_sum_binary_4`; one new S3 insight.

## 9. Honest size

~7 LOC Lean + ~200 LOC markdown + ~30 LOC JSON diff. The proof itself
is a single tactic (`native_decide`); the surrounding work documents
the discharge path and updates the state machinery. Compared to S1
(+115 LOC Lean for the modular-arithmetic axiom), this is the
"computational axiom" case where the kernel does the work and the
researcher's job is to verify the decidability chain.

## 10. Out of scope (deferred)

- **`binary_necklaces_4`** — that is S4, next picker's slot.
- The 3 pre-existing `simpArgs` linter warnings at lines 77 / 299 / 301
  (untouched since they predate this PR, same as S2).
- Generalising to arbitrary `n, k` — the parent gallery proof scopes
  the headline result to `n = 4, k = 2`; generalisation is a separate
  thread.
