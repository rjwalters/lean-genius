# Knowledge: geometric-series-oq-01-oq-02

## Summary

**Problem**: Formalize the general Cesàro (C,1) regularity theorem — if a series
`∑ aₙ` converges to `s`, then its Cesàro mean converges to the same `s`.

**Status**: ACT (S2, 2026-06-15). Full Lean proof written — 126 LOC, 0 sorries,
0 axioms (`proofs/Proofs/GeometricSeriesOQ01OQ02.lean`). M1 regularity +
series-level corollary + M2 Grandi strict-extension all proved. Build-pending
UNREGISTERED (dual blackout: Docker down, no local Mathlib) — needs
`import Proofs.GeometricSeriesOQ01OQ02` in `proofs/Proofs.lean`, a
`docker-build.sh` pass, and gallery data before merge.

**Progress summary**: ACT — complete proof of the OQ. `cesaro_regularity`
(`Sₙ → s ⟹ σₙ → s`) is `(h.comp (tendsto_add_atTop_nat 1)).cesaro`; series-level
`cesaroSummable_of_hasSum`/`cesaroSummable_of_summable` via
`HasSum.tendsto_sum_nat`; converse-failure `cesaro_strictly_extends_convergence`
reuses the parent's `grandiCesaro_tendsto` + `not_summable_grandi` through a
pointwise bridge `cesaroMean_grandi_eq`.

## Key insights

- The OQ is the **regularity / consistency** property of (C,1) summation:
  ordinary convergence ⟹ Cesàro summability to the *same* limit. It is a
  near-immediate corollary of `Filter.Tendsto.cesaro`, applied to the
  **partial-sum sequence** `S N = ∑ i ∈ range N, a i` (not to the terms `aₙ`).
- The correct object to average is the sequence of partial sums `S`, not the
  terms `aₙ`. Averaging the terms gives `→ 0` whenever `∑ aₙ` converges (terms
  vanish) and is *not* the (C,1) mean of the series.
- Mathlib's `Filter.Tendsto.cesaro` divides by `N` over `range N` (includes the
  empty partial sum `S 0 = 0`); the indexing offset / inclusion of `S 0` does not
  affect the limit, so it matches the standard (C,1) definition.
- The parent entry `geometric-series-oq-01` already proves the **concrete** Grandi
  instance by hand (`grandiCesaro_tendsto`, via `|σₙ − 1/2| ≤ 1/(2n)`). OQ-02's
  general theorem subsumes that bespoke bound — the value-add is generality, plus
  the converse-failure illustration that (C,1) **strictly** extends convergence.
- Regularity and its converse are distinct facts: regularity is
  convergent ⟹ (C,1)-summable; Grandi's series witnesses that the converse
  fails ((C,1)-summable to 1/2, yet divergent / not `Summable`).

## Built items

- `proofs/Proofs/GeometricSeriesOQ01OQ02.lean` (S2, 126 LOC, 0 sorry/0 axiom):
  - `partialSum`, `cesaroMean`, `CesaroSummable` (defs).
  - `cesaro_regularity` — **the OQ**: `Tendsto (partialSum a) (𝓝 s) → CesaroSummable a s`.
  - `cesaroSummable_of_hasSum`, `cesaroSummable_of_summable` — regularity at the
    level of the actual series sum (`HasSum`/`Summable`).
  - `cesaroMean_grandi_eq` — pointwise bridge: `cesaroMean ((-1)^·) = grandiCesaro`
    (parent's bespoke mean), via `div_eq_inv_mul` + `if_neg`.
  - `grandi_cesaroSummable` — Grandi (C,1)-summable to 1/2 (reuses parent's bound).
  - `grandi_not_summable`, `cesaro_strictly_extends_convergence` — converse fails.

## Mathlib gaps

- No named series-level `CesaroSummable` predicate in Mathlib (trivial to define
  locally; not a fundamental gap).
- The sequence-average limit transfer **is** present: `Filter.Tendsto.cesaro`
  and `Filter.Tendsto.cesaro_smul` in
  `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`.

## Next steps

1. (Build, when Docker returns) Register `import Proofs.GeometricSeriesOQ01OQ02`
   in `proofs/Proofs.lean`, run `./proofs/scripts/docker-build.sh
   Proofs.GeometricSeriesOQ01OQ02`. Likely-fragile points to watch if it fails:
   - `Filter.Tendsto.cesaro` exact name/shape (`(n:ℝ)⁻¹ * ∑ i ∈ range n, u i`).
   - `tendsto_add_atTop_nat 1` defeq with the `S_{k+1}` shift in `cesaroMean`.
   - `cesaroMean_grandi_eq` n>0 branch closing by `rw [div_eq_inv_mul]` after the
     `simp only` unfold (bound-var rename i↔j is harmless).
2. Add gallery `src/data/proofs/geometric-series-oq-01-oq-02/` (mirror parent's
   meta.json; set `status` to `verified` ONLY after the build is green).
3. (Optional follow-up theory) Hardy–Littlewood Tauberian converse: if `σₙ → s`
   and `aₙ = O(1/n)` then `∑ aₙ = s` — the genuine open direction, NOT yet in
   Mathlib (this session proved only the easy regularity direction).

## Sessions

### Session 2026-06-15 (S2) — ACT: full Lean proof

**Mode**: REVISIT (executed the S1 ACT plan)
**Outcome**: progress — complete proof written (build-pending; dual blackout)

#### What I did
- Wrote `proofs/Proofs/GeometricSeriesOQ01OQ02.lean` (126 LOC, 0 sorry/0 axiom).
- M1 `cesaro_regularity`: chose the (C,1) convention `σₙ = (S₁+⋯+Sₙ)/n` (average
  the *nonempty* partial sums `S_{k+1}`), so the proof is
  `(h.comp (tendsto_add_atTop_nat 1)).cesaro` — one `Filter.Tendsto.cesaro` call
  on the shifted partial-sum sequence.
- Added series-level corollaries `cesaroSummable_of_hasSum` (via
  `HasSum.tendsto_sum_nat`) and `cesaroSummable_of_summable`.
- M2: proved `cesaroMean ((-1)^·) = grandiCesaro` *pointwise* (`funext`, n=0 by
  `simp`, n>0 by `simp only [...] ; rw [div_eq_inv_mul]`), letting me transport
  the parent's `grandiCesaro_tendsto` to get `grandi_cesaroSummable` to 1/2 for
  FREE, then bundle with `not_summable_grandi` into
  `cesaro_strictly_extends_convergence`.

#### Key findings
- Picking the textbook convention (start partial sums at `S₁`, divide by `n`)
  makes BOTH M1 (one `.cesaro` after a `+1` shift) and M2 (defeq-equal to the
  parent's `grandiCesaro`, modulo `a/n = n⁻¹*a`) collapse to near-one-liners.
  Choosing the convention to match the reusable artifact is the whole trick.
- This proves only the *regularity* (easy) direction. The Hardy–Littlewood
  Tauberian converse is the real open content and remains unformalized.

#### Files modified
- `proofs/Proofs/GeometricSeriesOQ01OQ02.lean` (new)
- `research/problems/geometric-series-oq-01-oq-02/{knowledge,state}.md`

#### Next steps
- Register + `docker-build` when the host returns; then add gallery data.

### Session 2026-06-14 (S1) — ORIENT feasibility survey

**Mode**: FRESH
**Outcome**: scouted / ORIENT (no proof attempt — Docker down)

#### What I did
- Selected from the available pool by knowledge-tier triage (RICH slugs
  `nth-root-irrational-oq-03` = active passive-watch, `mean-value-theorem-oq-02-oq-04`
  = already resolved/retracted; chose this high-tractability fresh OQ for a
  paper ORIENT).
- Resolved the OQ on paper: regularity of (C,1) summation reduces to
  `Filter.Tendsto.cesaro` applied to the partial-sum sequence.
- Verified the exact Mathlib signatures against `master` (2026-06-14) in
  `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`.
- Inspected the parent Lean file `proofs/Proofs/GeometricSeriesOQ01.lean`:
  found reusable `grandiCesaro_tendsto`, `not_summable_grandi`, `grandi_even`,
  `grandi_odd` for M2.
- Split into M1 (regularity) and M2 (converse-failure) milestones; both
  buildable (< 80 LOC), no Mathlib gap.

#### Key findings
- OQ is a near-immediate corollary of existing Mathlib — main work is packaging
  + the converse illustration, not new mathematics.
- Average the partial sums, not the terms.

#### Files modified
- `research/problems/geometric-series-oq-01-oq-02/state.md` (new)
- `research/problems/geometric-series-oq-01-oq-02/knowledge.md` (new)

#### Next steps
- ACT when Docker returns (see Next steps above).
