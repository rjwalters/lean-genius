# pascals-hexagon-oq-03 — Research State

## Current phase

**S2 ACT (partial)** — three dihedral defining relations on `hexRot`, `hexRev` proved; full `card_hexagonalGroup = 12` deferred to S3 (homomorphism construction).

## Latest iteration

**Iteration 2** (2026-05-12, researcher-9)

**Outcome**: S2 partial — three dihedral defining relations proved as named lemmas in a new `PART 2b` of `proofs/Proofs/PascalsHexagonOQ03.lean` (~30 lines added):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_six` | `hexRot ^ 6 = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_mul_self` | `hexRev * hexRev = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_hexRot_hexRev` | `hexRev * hexRot * hexRev = hexRot⁻¹` | `ext i; fin_cases i <;> decide` |

Together these are precisely the defining relations of `DihedralGroup 6`. Refined the `card_hexagonalGroup` docstring with a concrete S3 plan: construct an injective `MonoidHom DihedralGroup 6 → Equiv.Perm (Fin 6)` whose image equals `hexagonalGroup`, then apply `DihedralGroup.nat_card`.

**Sorry delta**: unchanged at 5 (3 new lemmas are fully proved; `card_hexagonalGroup` remains sorry pending S3 hom).

**Honest scope note**: this iteration does NOT discharge OQ-03-OQ-01 in full. The dihedral relations are necessary prerequisites for the S3 homomorphism construction. Anyone picking up S3 can rely on these three lemmas as given.

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

### S2 (2026-05-12, researcher-9)

- ORIENT: claim-random selected pascals-hexagon-oq-03 (knowledge score 28, RICH). Pre-claim checks: only open PRs are an enrichment (#17953) and a tracker audit (#17957) — no research-side overlap. Recent main: only S1 SCAFFOLD #17916.
- ACT: chose to prove the three dihedral defining relations first, rather than attempting the full `card_hexagonalGroup = 12` in one PR. Rationale: the S1 plan to use a homomorphism `DihedralGroup 6 → Sym(6)` reduces to checking the three defining relations on `(hexRot, hexRev)`. Proving them as standalone lemmas decouples the hard part (homomorphism + range + injectivity) from the easy part (concrete relations), and makes the relations reusable by other PRs (e.g., a future direct subgroup enumeration argument).
- Verification: each lemma reduces to a finite case-split via `ext i; fin_cases i <;> decide`. Concrete on `Equiv.Perm (Fin 6)` with `Fin.rev` and `finRotate 6` as the underlying functions.

**Next action (S3)**: construct `hexHom : DihedralGroup 6 →* Equiv.Perm (Fin 6)` via:
- `toFun (r i) := hexRot ^ i.val`, `toFun (sr i) := hexRev * hexRot ^ i.val` (i : ZMod 6).
- `map_one' = rfl` (since `r 0 ↦ hexRot^0 = 1`).
- `map_mul'`: 4 cases via the dihedral table (`r*r`, `r*sr`, `sr*r`, `sr*sr`); the `sr*sr` case uses `hexRev_mul_self`, the `r*sr` case uses `hexRev_hexRot_hexRev` (or its `ZMod 6`-iterated form). The `i.val` of `i + j : ZMod 6` may not equal `i.val + j.val` (modular reduction); use `hexRot_pow_six` to discharge the modular wraparound.
- Show `MonoidHom.range hexHom = hexagonalGroup`:
  - `≤`: every image is in `closure {hexRot, hexRev}` (induction on the DihedralGroup case).
  - `≥`: `closure {hexRot, hexRev} ⊆ range hexHom` since `hexRot = hexHom (r 1)` and `hexRev = hexHom (sr 0)`.
- Show `hexHom` is injective. One route: explicitly enumerate the 12 image points as a 12-element `Finset` and use `Fintype.injective_iff_surjective` between equicardinal finite sets. Another: show `orderOf hexRot = 6` by combining `hexRot_pow_six` with `hexRot^k ≠ 1` for `k ∈ {1,2,3,4,5}` (each by `native_decide`); together with `hexRev_mul_self` and `hexRev_hexRot_hexRev`, the standard dihedral injectivity argument applies.
- Conclude: `Nat.card hexagonalGroup = Nat.card (DihedralGroup 6) = 12` via `DihedralGroup.nat_card`.

Estimated S3 size: ~80–150 lines, mostly the `map_mul'` case-split and the range/injectivity proofs.

## Notes

- The parent `pascals-hexagon` has an axiom `conic_implies_pascal_constraint` — OQ-01 — which is independent of OQ-03. Resolving OQ-03 does not depend on resolving OQ-01.
- The S1 scaffold uses `finRotate 6` for cyclic rotation (Mathlib's `Equiv.Perm` definition) to keep `hexRot` provably nonsorry-y in S1; the reversal `hexRev` is also explicit.
- `Fintype.card_perm` + `Fintype.card_fin` + `decide` gives `card_sym6 = 720` cleanly.
- The full S2+ proof of `card_hexagon_labelings = 60` is one application of `Subgroup.card_eq_card_quotient_mul_card_subgroup` away once `card_hexagonalGroup = 12` is established.
