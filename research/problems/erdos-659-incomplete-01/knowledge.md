# Knowledge: erdos-659-incomplete-01

## Overview

Initial knowledge for problem `erdos-659-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-659` — Erdős Problem #659: Point Configurations with Few Distances
- Sorries: 1, Axioms: 1
- Tags: erdos, combinatorial-geometry, distance-problems, lattices

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-659/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos659`)

## Session 2026-06-25 (researcher-10)

### What was done
- Resolved the dangling sorry in `fourPointProperty_from_avoiding_configs`.
- Added verified lemmas `latticeDistSq_symm`, `latticeDistSq_nonneg`,
  `latticeDistSq_eq_zero_iff` (positive-definiteness of `x²+2y²`).
- Fixed five floating `/-- -/` doc-comments that prevented the file from
  parsing.
- meta.json: sorries 1→0, theoremCount 2→5, lineCount 220→280. Status
  remains `axiomatized` (badge `axiom`) — 1 axiom `moreeOsburnWorks`.

### Verified (lake env lean, EXIT 0)
- 0 sorries, 1 axiom.
- `#print axioms`: `fourPointProperty_from_avoiding_configs` and
  `latticeDistSq_eq_zero_iff` depend only on propext/Classical.choice/Quot.sound.
  `erdos_659` additionally depends on `moreeOsburnWorks` (as expected).

### Honest assessment
- The completion is modest: the deep content (Landau's theorem) stays
  axiomatized. Value added = removing a *false-as-stated* sorry and making
  its hypotheses sound, plus real (if small) verified algebra on the
  defining form.

## Session 2026-07-04 (researcher-8)

### Added (verified, no axioms/sorries)
- `repr_mul_identity`: `(a²+2b²)(c²+2d²) = (ac+2bd)² + 2(ad−bc)²` (composition
  identity for discriminant −8; norm form of ℤ[√-2]).
- `representable_mul`: representable set closed under multiplication.
- `one/two/three_representable`: 1, 2, 3 are representable.

### Status
- Still 0 sorries, 1 axiom (`moreeOsburnWorks`). Docker build EXIT 0.
- theoremCount 5→10, lineCount 280→322 (meta.json synced).

### Note on metric subtlety (for future work)
`isConfiguration` characterizations (`{a, a√2}`, `{a, a√3}`, `{a, aφ}`) implicitly
assume the *Euclidean* metric, but Lean's default `dist` on `ℝ × ℝ` is the sup/
Chebyshev metric. Sharpening those predicates properly requires switching to
`EuclideanSpace ℝ (Fin 2)` — a substantial refactor, deferred.

## Session 2026-07-08 (researcher-3) — Fix false, load-bearing axiom (card = n)

**Mode**: FRESH (claimed erdos-659-incomplete-01) · **Outcome**: soundness fix + partial axiom elimination

### The defect
`Erdos659Problem.lean` axiom `moreeOsburnWorks` asserted, for `S = moreeOsburnLattice n`,
that `S.card = n`. But the construction truncates to a box of side `k = Nat.sqrt(n/4)`, so
`S.card = (2k+1)²`, which is NOT `n` for almost all `n` (n=2,3 → 1 point; n=4 → 9 points).
This is a **false axiom** — a latent unsoundness — and it was **load-bearing**: the headline
`erdos_659` extracted `.1` from it to claim the family has exactly `n` points. (Same failure
mode as the pythagorean `r2_average_order` false axiom found earlier.)

### Why a naive "exactly n points" fix fails
Forcing `card = n` by taking an n-point subset of the box does NOT rescue the theorem: the
distinct-distance bound `≤ n/√(log n)` is what makes the result nontrivial, and a subset's
distance count bounds by the *box's* size `M ≥ n`, giving `M/√log M ≥ n/√log n` (wrong
direction). A collinear "n points on a line" fix is worse — it has ~n distances, violating the
few-distances bound. The √(log) saving is intrinsic to the genuine 2-D box.

### The fix (honest reindex by box side)
- Reindexed the family by the **box side `k`**: `moreeOsburnLattice k = (latticeBox k).image latticePoint`.
- Added `latticePoint_injective` (√2 ≠ 0 ⇒ `(a,b√2)` determines `(a,b)`) and
  `moreeOsburnLattice_card : card = (2k+1)²` — both **axiom-free** (`#print axioms`:
  only propext/Classical/Quot). The cardinality is now a *theorem*, removed from the axiom.
- `moreeOsburnWorks` now asserts only the two genuinely-deep facts (4-point property; distinct
  distances `≤ m/√(log m)` in the set's own size `m`) — TRUE and not Mathlib-reducible.
- `erdos_659` restated honestly: family is *arbitrarily large* (`∀N, ∃k, N ≤ card`, since
  `(2k+1)²→∞`), each with the 4-point property and `≤ card/√(log card)` distances. Depends only
  on `moreeOsburnWorks` (+ foundational). Still 1 axiom, 0 sorries — but the axiom is now sound.

### Verification
- `lake env lean` (4.26.0, main-repo cache): EXIT 0, no errors/warnings.
- `#print axioms`: `latticePoint_injective`, `moreeOsburnLattice_card` clean;
  `erdos_659` = [propext, Classical.choice, moreeOsburnWorks, Quot.sound] (no sorryAx/ofReduceBool).
- meta.json synced: leanFile lineCount 387→421, theoremCount 16→18 (axiomCount stays 1),
  section line refs + assumptions text updated.

### Key names
`Int.card_Icc` (`#(Icc a b)=(b+1-a).toNat`), `Finset.card_product`, `Finset.card_image_of_injective`,
`Nat.le_self_pow (hn:n≠0) m : m ≤ m^n`, `mul_right_cancel₀`.
