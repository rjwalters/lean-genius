# pascals-hexagon-oq-03 — Research State

## Current phase

**S1 OBSERVE / ACT** — initial scaffold of the 60-Pascal-line configuration.

## Latest iteration

**Iteration 1** (2026-05-12, researcher-4)

**Outcome**: S1 SCAFFOLD shipped.

**Deliverable**: `proofs/Proofs/PascalsHexagonOQ03.lean` (~250 lines) — combinatorial backbone, Pascal-line map signature, Steiner/Kirkman structures, main theorem statements; 5 sorries spread over 4 sub-OQs.

**Resolution claim**: **YES** — the 60-Pascal-line configuration can be formalized. The scaffold provides the combinatorial framework, the four sub-OQs decompose the remaining concurrence work, and existing Cayley-Bacharach axiom infrastructure suffices to discharge each triple.

## Sub-OQ roadmap

| Sub-OQ | Lines | Purpose | Status |
|--------|-------|---------|--------|
| OQ-03-OQ-01 | ~150 | `hexagonalGroup` order = 12, `card_hexagon_labelings = 60` | sorry-1 |
| OQ-03-OQ-02 | ~100 | `pascalLine` well-defined on the quotient | sorry-2 |
| OQ-03-OQ-03 | ~400 | Steiner points: enumerate 20 triples + concurrence | sorry-3 |
| OQ-03-OQ-04 | ~400 | Kirkman points: enumerate 60 triples + concurrence | sorry-4 |
| OQ-03-OQ-05 (opt) | ~200 | Cayley + Plücker + Salmon configurations | deferred |

## Session log

### S1 (2026-05-12, researcher-4)

- ORIENT: tier-B available pool filtered for 0 open PRs + oldest last-merge. `pascals-hexagon-oq-03` last merged 2026-05-05 (a routine meta-fix PR, not an OQ-03 PR); no open PRs; no remote branches; not in research registry.
- OBSERVE: parent docstring (lines 286-294) already documents the 60-20-60-15 incidence structure narratively; no Lean formalization of it. Companion file `PascalsHexagon.lean` provides `Conic`, `InscribedHexagon`, `pointOnLine`, `lineThrough`, `lineIntersection`, and the `conic_implies_pascal_constraint` axiom — sufficient infrastructure for Pascal-line definitions in the scaffold.
- ACT: wrote `PascalsHexagonOQ03.lean` (~250 lines) with `hexRot`, `hexRev`, `hexagonalGroup`, `HexagonLabeling`, `card_sym6` (no sorry, by `Fintype.card_perm` + `decide`), and 4 sorry-guarded sub-OQ targets.
- Gallery entry: meta.json + annotations.json + index.ts wired through to `Proofs/Proofs.lean`.

**Next action (S2)**: discharge `card_hexagonalGroup = 12` (OQ-03-OQ-01). Strategy: enumerate the 12 elements of the subgroup as a `Finset` (e₁ = id, ρ, ρ², ρ³, ρ⁴, ρ⁵, σ, ρσ, ρ²σ, ρ³σ, ρ⁴σ, ρ⁵σ) and verify each lies in `Subgroup.closure {ρ, σ}` by `Subgroup.mul_mem` + `Subgroup.subset_closure`, then use `Subgroup.card_closure_eq_card_set_image` or directly `decide` on a `Fintype` instance.

## Notes

- The parent `pascals-hexagon` has an axiom `conic_implies_pascal_constraint` — OQ-01 — which is independent of OQ-03. Resolving OQ-03 does not depend on resolving OQ-01.
- The S1 scaffold uses `finRotate 6` for cyclic rotation (Mathlib's `Equiv.Perm` definition) to keep `hexRot` provably nonsorry-y in S1; the reversal `hexRev` is also explicit.
- `Fintype.card_perm` + `Fintype.card_fin` + `decide` gives `card_sym6 = 720` cleanly.
- The full S2+ proof of `card_hexagon_labelings = 60` is one application of `Subgroup.card_eq_card_quotient_mul_card_subgroup` away once `card_hexagonalGroup = 12` is established.
