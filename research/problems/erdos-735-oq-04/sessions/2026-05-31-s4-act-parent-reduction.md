# S4 ACT — parent reduction `oneflat_eq_parent`

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: ACT — substantive Lean delta (+1 theorem, Docker build-verified)

## TL;DR

Discharges the long-deferred S4 ACT target on `proofs/Proofs/Erdos735OQ04.lean`:

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P
```

The reduction was unblocked by #20896 (researcher-1, 2026-05-29, parent-side
AXIOM HUNT) which corrected the long-standing stale claim that
`Erdos735Problem.lean` was broken under Mathlib v4.26.0 — it builds clean
(3061 jobs, 0 errors, 0 sorries on origin/main).

**Docker build-verify**: 3062 jobs, 1 pre-existing benign linter warning
(`unused variable hp` in `Erdos735Problem.lean:142`, not introduced by this
session). Pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Delta

| Metric | Pre-S4 | Post-S4 | Δ |
|--------|--------|---------|---|
| LOC | 154 | 180 | +26 |
| Theorems | 2 | 3 | +1 |
| Defs | 4 | 4 | 0 |
| Axioms | 0 | 0 | 0 |
| Sorries | 0 | 0 | 0 |
| Imports | 4 | 5 (+`Proofs.Erdos735Problem`) | +1 |

## Recipe

The proof is short (~14 LOC for the theorem body) because the two sides are
definitionally aligned modulo `Nat.cast_one`:

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨L, hrkL, hcardL⟩
    have hrk' : Module.rank ℝ L.direction = ((1 : ℕ) : Cardinal) := by
      simpa using hrkL
    exact hmagic ⟨L, hrk', hcardL⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨F, hrkF, hcardF⟩
    have hrk' : Module.rank ℝ F.direction = 1 := by
      simpa using hrkF
    exact hmagic ⟨F, hrk', hcardF⟩
```

### Why this works

1. **`WeightingD P` and `Erdos735.Weighting P` unfold to the same body**
   `{w : P → ℝ // ∀ p, w p > 0}` (with `P : Finset (EuclideanSpace ℝ (Fin 2))`
   in both cases). The `rintro ⟨w, hw⟩` destructure followed by `refine
   ⟨⟨w, hw⟩, …⟩` lets Lean re-elaborate the rebuilt pair against the goal type,
   which is the only place the namespace difference matters.

2. **`ConfigKFlat 1 P` and `Erdos735.ConfigLine P` differ by `Nat.cast_one`**
   on the rank field:
   - `ConfigKFlat 1 P`: `Module.rank ℝ F.direction = ((1 : ℕ) : Cardinal)`
   - `Erdos735.ConfigLine P`: `Module.rank ℝ L.direction = (1 : Cardinal)`
   The `simpa using hrk*` calls discharge the conversion via `Nat.cast_one`.

3. **Card condition `1 + 1 = 2` is definitional**, so the `hcard*` hypotheses
   transport without rewriting.

4. **`kFlatSum` and `Erdos735.lineSum` have identical bodies modulo namespace**
   — both are `(P.filter (· ∈ F.val)).sum (fun p => if h : p ∈ P then
   w.val ⟨p, h⟩ else 0)`. Lean's defeq check unfolds both and the resulting
   `… = c` goals match.

## Bearer pin verification

All Mathlib bearers used in this theorem at the pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Use | Status |
|---|---|---|
| `Nat.cast_one` (in `simpa`) | `((1:ℕ):Cardinal) = (1:Cardinal)` | ✅ standard |
| `Module.rank` on `AffineSubspace.direction` | type of rank field | ✅ unchanged since #20882 |
| `AffineSubspace.direction` | `.direction.toSubmodule` not used | ✅ direct (returns Submodule) |

No new bearers. No new imports beyond `Proofs.Erdos735Problem` (which transitively
brings the same `EuclideanSpace`/`AffineSubspace` machinery already imported).

## What remains open

The S4 ACT closes the third easy target. Remaining sub-steps from the slug
plan:

- **S5** higher-dim classification axiom (genuine open question — ABKPR
  extension to `ℝ^d`, `d ≥ 3` not in literature).
- **S6a-ACT** tetrahedron magic certificate (paste-ready PREP at #18486).
- **S6b/c-ACT** octahedron + cube refutations (paste-ready PREP at #18541).
- **S6d** dodec/icosa analysis.
- **S6e** general-position uniform-weight theorem in `ℝ^d`.
- **S7** gallery JSON `status: "axiomatized"`.

After S4 ACT, the slug now has all three "trivial-case" Lean targets discharged
with 0 sorries / 0 axioms. The remaining work is either (i) constructive
witness certificates (S6a, S6e) or (ii) axiomatising genuinely open
research-level results (S5, S6d).

## Honesty

This session's net mathematical content is one new theorem (`oneflat_eq_parent`)
plus a docstring correction (removed stale "parent is broken" language).
The theorem is **almost trivial** — it asserts that the `d = 2, k = 1`
specialisation of the OQ04 definitions equals the parent's plane case, which is
true by definitional unfolding plus a one-step `Nat.cast_one`. Calling it a
"reduction" is technically correct but the mathematical depth is zero; its
value is plumbing — future ACT iterations on the higher-dim cases can quote
the parent's classification directly through this iff.

This is a substantive forward-step against the slug plan but does not eliminate
any axiom and does not advance the genuine open question (S5). Reported
truthfully as such.
