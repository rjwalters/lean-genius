# Knowledge: geometric-series-oq-01-oq-02

## Summary

**Problem**: Formalize the general Cesàro (C,1) regularity theorem — if a series
`∑ aₙ` converges to `s`, then its Cesàro mean converges to the same `s`.

**Status**: ACT (S2, 2026-06-15, researcher-6). Lean file written, build-pending
(Docker host still down, Aristotle only fills sorries so cannot typecheck a
sorry-free file). The S1 plan (M1 regularity via `Filter.Tendsto.cesaro`, M2
Grandi converse-failure) is fully realized in
`proofs/Proofs/GeometricSeriesOQ01OQ02.lean` — 0 sorries, 0 axioms.

**Status (S1)**: ORIENT (2026-06-14). OQ resolved on paper; reduces to Mathlib's
`Filter.Tendsto.cesaro`. Buildable (< 80 LOC), no Mathlib gap.

**Progress summary**: ORIENT — formalizable core pinned to existing Mathlib API;
two-milestone plan (M1 regularity, M2 converse-failure via Grandi). No Lean
written yet.

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

- `GeometricSeriesOQ01OQ02.cesaroMean` / `CesaroSummable`
  (`proofs/Proofs/GeometricSeriesOQ01OQ02.lean`).
- M1 `cesaroSummable_of_tendsto`, `cesaroSummable_of_hasSum` (regularity).
- M2 `sum_grandiPartial`, `grandi_partial_abs_le_one`, `grandiCesaroMean_eq`,
  `grandiCesaroMean_tendsto`, `grandi_partial_not_tendsto`,
  `cesaro_strictly_extends_convergence`.
- All 0 sorries / 0 axioms; **build-pending** (Docker host down at S2).

## Mathlib gaps

- No named series-level `CesaroSummable` predicate in Mathlib (trivial to define
  locally; not a fundamental gap).
- The sequence-average limit transfer **is** present: `Filter.Tendsto.cesaro`
  and `Filter.Tendsto.cesaro_smul` in
  `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`.

## Next steps

1. (ACT, Docker) Create `proofs/Proofs/GeometricSeriesOQ01OQ02.lean`.
2. Define `cesaroMean S N := (N⁻¹:ℝ) * ∑ k ∈ range N, S k` and a
   `CesaroSummable` predicate.
3. M1: regularity via `exact h.cesaro` on the partial-sum sequence.
4. M2: Grandi converse-failure using parent `grandiCesaro_tendsto` +
   `not_summable_grandi`.
5. Add gallery `src/data/proofs/geometric-series-oq-01-oq-02/` and build-verify.

## Sessions

### Session 2026-06-15 (S2) — ACT: wrote the Lean file (build-pending)

**Mode**: REVISIT (claimed available, RICH knowledge from S1)
**Outcome**: progress — Lean file written, 0 sorries / 0 axioms, build-pending

#### What I did
- Confirmed `Filter.Tendsto.cesaro` signature via web (Mathlib4 docs):
  `(h : Tendsto u atTop (𝓝 l)) : Tendsto (fun n => (↑n)⁻¹ * ∑ i ∈ range n, u i) atTop (𝓝 l)`.
  Defined `cesaroMean S n := (↑n)⁻¹ * ∑ k ∈ range n, S k` to match this convention
  exactly, so M1 is a definitional application.
- Wrote `proofs/Proofs/GeometricSeriesOQ01OQ02.lean`:
  - `cesaroMean`, `CesaroSummable` (predicate on the partial-sum sequence).
  - **M1** `cesaroSummable_of_tendsto := h.cesaro` (term-mode, via defeq) +
    `cesaroSummable_of_hasSum` corollary via `HasSum.tendsto_sum_nat`.
  - **M2** Grandi converse-failure:
    - `sum_grandiPartial`: closed form `∑_{k<n} Sₖ = (n − Sₙ)/2`, induction +
      parent `grandi_double_sum`.
    - `grandi_partial_abs_le_one`: `|Sₙ| ≤ 1` via parity of `(−1)ⁿ`.
    - `grandiCesaroMean_eq`: `σₙ = (1/n)·(n − Sₙ)/2`.
    - `grandiCesaroMean_tendsto`: `σₙ → 1/2` (bound `|σₙ−1/2| = |Sₙ|/(2n) ≤ 1/(2n)`).
    - `grandi_partial_not_tendsto`: partial sums diverge (even subseq → 0, odd → 1).
    - `cesaro_strictly_extends_convergence`: the headline ∧.
- Could NOT verify the build: Docker host down; Aristotle MCP only proves
  `sorry`s so it cannot typecheck a sorry-free file. File shipped build-pending
  and **UNREGISTERED** in `Proofs.lean` (protects the aggregate build /
  auto-merge until a Docker session verifies it).

#### Key findings
- The clean real identity `∑_{k<n} Sₖ = (n − Sₙ)/2` (proved from `2Sₙ = 1−(−1)ⁿ`)
  gives `σₙ − 1/2 = −Sₙ/(2n)` exactly — sidesteps the parent's `⌈n/2⌉/n` ceiling
  arithmetic and the index-shift between the two Cesàro conventions.
- M1 is genuinely one line: matching `cesaroMean`'s shape to `Filter.Tendsto.cesaro`
  makes the regularity theorem a definitional rewrite of the Mathlib lemma.

#### Files modified
- `proofs/Proofs/GeometricSeriesOQ01OQ02.lean` (new, ~200 lines incl. docstring)
- `research/problems/geometric-series-oq-01-oq-02/knowledge.md` (this update)

#### Next steps (when Docker returns)
1. `./proofs/scripts/docker-build.sh Proofs.GeometricSeriesOQ01OQ02`; fix any
   API drift (candidate risk points: `gcongr` leaf on `|S| ≤ 1`, `field_simp`
   in `hkey`, `div_lt_iff₀` name).
2. Register `import Proofs.GeometricSeriesOQ01OQ02` in `Proofs.lean`.
3. Add gallery `src/data/proofs/geometric-series-oq-01-oq-02/` (meta.json +
   proof.md); status `verified`, badge `original`, 0 axioms / 0 sorries —
   only after the build is green.

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
