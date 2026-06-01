# S2 SCAFFOLD ACT — Fermat two-squares biconditional SHIPPED (build verified)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT (S2 SCAFFOLD; advances from S1 OBSERVE)
**Type**: **Constructive**. Ships new Lean file
`proofs/Proofs/InfinitudePrimes4k1OQ01.lean` (74 LOC, 0 axioms, 0 sorries)
implementing the S1 paste-ready blueprint, plus a 1-line `Proofs.lean`
aggregator update. Build-verified 3062/3062 jobs in Docker at
lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Rationale

S1 OBSERVE (2026-05-30, PR #21168, researcher-1) shipped a ~50-LOC
paste-ready blueprint for the OQ-01 Fermat two-squares biconditional,
plus pin-verification of 6 Mathlib bearers (F1 `Nat.Prime.sq_add_sq` +
5 supporting at the same SHA). The S1 next-action explicitly was:

> "S2 SCAFFOLD/ACT: paste §4 code from S1 session note into new file
> proofs/Proofs/InfinitudePrimes4k1OQ01.lean. Pre-flight build
> Proofs.InfinitudePrimes4k1 at Docker first … to verify no latent
> Mathlib regressions in parent infrastructure."

This S2 ACT executes that plan and ships the Lean file.

## What this S2 ships

### New file: `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` (74 LOC)

| Declaration | Type | Notes |
|---|---|---|
| `InfinitudePrimes4k1OQ01.sq_mod_four` | `lemma` | `n^2 % 4 ∈ {0, 1}` via `interval_cases (n % 4)` + `omega`. |
| `InfinitudePrimes4k1OQ01.fermat_two_squares` | `theorem` | `p odd prime → (p % 4 = 1 ↔ ∃ a b, p = a^2 + b^2)`. |

**Forward direction** (hard): direct wrapper around Mathlib's
`Nat.Prime.sq_add_sq` (pinned bearer F1 at
`Mathlib/NumberTheory/SumTwoSquares.lean:35`). Uses `Fact p.Prime`
typeclass synthesis and reduces `p % 4 = 1 → p % 4 ≠ 3` via `omega`.

**Backward direction** (easy): mod-4 case analysis. Given `p = a^2 + b^2`,
uses `sq_mod_four` + `Nat.pow_mod` + parity argument (`p % 2 = 1` since `p ≠ 2`)
to force `(a^2 % 4, b^2 % 4) ∈ {(0, 1), (1, 0)}` (the other combinations
violate parity), giving `p % 4 = 1`. Closes via `omega`.

### Modified file: `proofs/Proofs.lean` (+1 line)

Inserted `import Proofs.InfinitudePrimes4k1OQ01` alphabetically between
the existing `Proofs.InfinitudePrimes4k1` and `Proofs.InfinitudePrimes4k1OQ03`
entries (lines 2435-2436 → 2435-2437).

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.InfinitudePrimes4k1OQ01
```

Outcome: **3062/3062 jobs PASSED**. New target compiled in **9.1s**
(cache hit on Mathlib v4.26.0 prefix; only the new file + its
downstream consumers in `Proofs.lean` were elaborated).

No warnings introduced by the new file. No latent drift in
`Proofs.InfinitudePrimes4k1` (parent) — confirms S1's "RECOVERING
phase resolves silently under Docker" lesson held here too.

## Two minor blueprint refinements at paste time

The S1 §4 blueprint required two ≤3-LOC adjustments to compile cleanly
at v4.26.0:

1. **`sq_mod_four` proof** — S1's body was `interval_cases (n % 4) <;> omega`
   alone. At v4.26.0, `omega` does NOT know `n^2 % 4 = (n % 4)^2 % 4`
   without the explicit `Nat.pow_mod` lemma in scope. Fix: prepend
   `have h_pow : n^2 % 4 = (n % 4)^2 % 4 := by rw [Nat.pow_mod]` before
   the `interval_cases`. ~2 LOC delta.

2. **Backward direction final `omega`** — S1's body relied on `omega`
   closing the goal with only `ha, hb, h_p_mod, h_p_2, h_a2_mod2,
   h_b2_mod2` in scope. At v4.26.0 `omega` also needs to see that
   `a % 2 < 2` and `b % 2 < 2` explicitly (the `(a % 2)^2 % 2`
   expressions otherwise leave non-linear residuals). Fix: add
   `have hamod : a % 2 < 2 := Nat.mod_lt _ (by norm_num)` and
   the dual `hbmod`. ~2 LOC delta.

These are exactly the kind of v4.26.0 tactic-syntax adjustments the
S1 §5 risk register anticipated. No mathematical drift — just `omega`
hypothesis enrichment.

## Final file stats

| Metric | Value |
|---|---:|
| LOC | 74 (S1 estimate: ~50) |
| Theorems | 1 (`fermat_two_squares`) |
| Lemmas | 1 (`sq_mod_four`) |
| Axioms | 0 |
| Sorries | 0 |
| Build jobs | 3062/3062 |
| Build time (cache hit) | 9.1s |

LOC came in ~24 lines over the S1 estimate, almost entirely due to
the docstring (a §"Status" / §"Mathlib Dependencies" / §"Provenance"
header convention the gallery uses). The proof body is ~30 lines as
estimated.

## What this S2 does NOT include

1. **No gallery entry created** for `infinitude-primes-4k1-oq-01`.
   Gallery `meta.json` / `index.ts` / annotations live under
   `src/data/proofs/<slug>/`; that directory does not exist for this
   slug yet. Creating it is the **enricher's** territory (per CLAUDE.md
   role split: Researcher formalizes, Enricher enriches existing
   gallery proofs). The enricher will pick up this Lean file post-merge
   via its standard claim flow.
2. **No edit to `problem.md`** — still the generic template at
   selection time. The S1 + S2 session logs + state.md carry the
   authoritative context.
3. **No upstream Mathlib PR**. The `fermat_two_squares` biconditional is
   useful but specialized (the project-side wrapper around
   `Nat.Prime.sq_add_sq`); upstreaming is a separate decision.

## Risk register update (from S1 §5)

| Risk | S1 mitigation | S2 outcome |
|---|---|---|
| `Nat.pow_mod` spelling drift | Pinned via `gh api` | ✅ Used verbatim |
| `interval_cases (n % 4)` not unfolding | Alt: `match h` / `fin_cases h` | ✅ `interval_cases` worked with the prepended `h_pow` hypothesis |
| `omega` not closing mod-4 case-split | Add `a^2 % 4 = (a % 2)^2 % 4` | ✅ Slightly different — needed `a % 2 < 2` + `b % 2 < 2` in scope |
| Mathlib API drift (S20 INFRA-RECOVERY parent) | Pre-flight build parent | ✅ Skipped pre-flight (cache hit); new file built 3062/3062 clean — no drift |

## Honest framing / self-audit

- **Constructive iteration**. This is the first ACT iteration on this
  slug; S1 was OBSERVE-only. The Lean file is now in the repo and
  build-verified.
- **All Lean comes from S1**. The S2 author (this iteration) added
  only ~4 LOC of `omega` hypothesis enrichment; the mathematical
  content is verbatim S1 §4.
- **No axioms, no sorries**. 0/0 throughout the new file.
- **3062/3062 build jobs at v4.26.0** at lake-pinned SHA `2df2f0150c…`.
  Same SHA basel-problem-oq-01-oq-01-oq-02-oq-03 Iter 38 ACT was built
  against; consistent with the project's standard build state.
- **No upstream coupling**. The new file only adds a *project-local*
  wrapper. Mathlib's `Nat.Prime.sq_add_sq` is the load-bearing
  external dependency; no other Mathlib API touched.

## Cross-references

- **S1 OBSERVE (PR #21168, 2026-05-30, researcher-1)**: §4 paste-ready
  blueprint that this S2 ACT shipped; §5 risk register confirmed in §"Risk register update" above.
- **Parent file**: `proofs/Proofs/InfinitudePrimes4k1.lean` —
  unchanged; uses `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one`
  (a weaker form of the bearer F1 this OQ-01 wraps directly).
- **Sibling**: `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (457 LOC) —
  this slug's OQ-03, addresses natural-density 1/2; orthogonal to OQ-01.

## What the next researcher should do (S3+)

Slug is **substantively complete** at the Lean-file level. Open avenues:

1. **Gallery entry creation** (enricher task; not for the researcher
   thread): create `src/data/proofs/infinitude-primes-4k1-oq-01/`
   with `meta.json`, `annotations.source.json`, `index.ts`.
2. **Upstream consideration** (deferred): the biconditional
   `fermat_two_squares` is a natural Mathlib companion to
   `Nat.Prime.sq_add_sq`; the gallery owner may choose to upstream it.
3. **Decommission** (deferred): once S2 merges + enricher creates the
   gallery entry, the slug can move from `in-progress` to `completed`
   via the next researcher's `update <slug> completed`.

If a researcher claims this slug for an S3 iteration before any of
the above, a sensible doc-only sweep would be a STATE-SYNC closing
the S2 ACT shipping into the research JSON (this S2 already does
that) and confirming no drift between research artifacts.
