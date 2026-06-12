# S4 ACT — `binary_necklaces_4` discharged; file is axiom-free

**Date**: 2026-06-11
**Researcher**: researcher-2
**Mode**: ACT (Lean implementation)
**Branch**: `research/burnside-oq-01-s4-necklaces-act`
**Build**: `./proofs/scripts/docker-build.sh Proofs.BurnsideCounting`
→ **3058 / 3058 jobs clean**.

## TL;DR

Discharged `binary_necklaces_4`, the **last of the 5 original axioms** in
`Proofs/BurnsideCounting.lean`. The file is now **axiom-free** (0 axioms,
0 sorries, 9 theorems, 404 LOC). The proof is a single `native_decide`.

## The key realisation

The S3 state.md recommended a ~30-50 LOC route: `burnside_lemma`
(MulAction form) + `fixed_point_sum_binary_4 = 24` + `|ZMod 4| = 4`, with
a bridge `AddAction.orbitRel.Quotient (ZMod 4) (Coloring 4 2) ↔
MulAction.orbitRel.Quotient (Multiplicative (ZMod 4)) (Coloring 4 2)` (or
`to_additive` on `burnside_lemma`).

That is the correct *mathematical* derivation, but it is unnecessary for
the *formal* goal. The goal is a single finite cardinality equality:

```lean
@Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2) = 6
```

S2 (researcher-1) had already shipped `coloringQuotientFintype` as a
**computable** `Fintype (Quotient (coloringSetoid n k))`, built from
`Quotient.fintype` over the finite carrier `Coloring 4 2 = Fin 4 → Fin 2`
and the decidable orbit relation `coloringSetoid_decidableRel`
(`decidable_of_iff (∃ x : ZMod n, x +ᵥ b = a) AddAction.mem_orbit_iff.symm`,
itself decidable because `ZMod n` is a `Fintype` and `Coloring` has
`DecidableEq`).

A computable `Fintype` makes `Fintype.card` of the quotient itself
decidable. `native_decide` enumerates the 16 colorings, maps each to its
rotation orbit, dedups via the decidable orbit equality, counts the 6
distinct classes, and decides `6 = 6`. Done.

```lean
theorem binary_necklaces_4 :
    @Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2) = 6 := by
  native_decide
```

`burnside_lemma` (the MulAction Mathlib statement at line 48) stays in the
file as a referenced result; it is not on the proof path for the necklace
count.

## Soundness note

`native_decide` is already the accepted idiom in this file (S3 used it for
`fixed_point_sum_binary_4`). The computed answer `6` is the classic count
of binary necklaces of length 4 — the verification is genuine (the
decision procedure returned `6` and `6 = 6` decided `true`), not vacuous.
All instances on the path (`Quotient.fintype`, `coloringSetoid_decidableRel`,
`rotateColoring`, `DecidableEq (Fin 4 → Fin 2)`) are computable; no
`Classical.choice` / noncomputable defs are reachable.

## Axiom history of `BurnsideCounting.lean`

| Iter | Axiom discharged | Method |
|---|---|---|
| S1 (#21148) | `rotatedIndex_add` | full Nat-modular proof (8-leaf case split) |
| S2 (2026-06-09) | `coloringSetoid`, `coloringQuotientFintype` | `AddAction.orbitRel` + `Quotient.fintype` + decidable rel |
| S3 (2026-06-10) | `fixed_point_sum_binary_4` | `native_decide` |
| **S4 (this PR)** | **`binary_necklaces_4`** | **`native_decide` on the computable quotient card** |

All 5 original axioms gone. File axiom-free.

## Race awareness

- Open PRs for this slug at push time: checked via `gh pr list`.
- Conflict surface: strictly additive single-file change (axiom → theorem)
  + state.md + JSON + this memo. No other Lean file touched.
- Branched off `origin/main`.

## Status

`verified` — `BurnsideCounting.lean` is axiom-free, 0 sorries,
Docker 3058 jobs clean. The slug's OQ target (`rotatedIndex_add`) was
already closed in S1; this iteration completes the broader file-level
axiom elimination. No remaining axioms or sorries; only the 3 cosmetic
pre-existing simpArgs linter warnings remain (untouched).
