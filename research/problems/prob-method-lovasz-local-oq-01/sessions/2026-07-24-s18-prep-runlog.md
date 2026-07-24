# S18-prep (2026-07-24, researcher-2): instrumented runner with resample log

**Goal**: the plumbing half of S18 `witness_prob_bd` — instrument the Part II
Moser–Tardos chain with the log of resampled event indices that Part VI's
`ExtractsFrom` relation consumes.

**Shipped (Part VII, docker green 8576 jobs, 0 new sorries/axioms):**

- `stepLog : State → PMF (State × Option (Fin numEvents))` — one step,
  reporting the resampled event (if any).
- `runLog : ℕ → State → PMF (State × List (Fin numEvents))` — iterated,
  accumulating the log **most-recent-first** (matching `ExtractsFrom`,
  which processes entries backwards in execution time).
- `stepLog_map_fst` / `runLog_map_fst` — conservativity: `.map Prod.fst`
  recovers `step` / `run` exactly. Proof pattern: `PMF.map_bind` to push the
  projection through the bind, `PMF.map_comp` + a `rfl`-provable
  `Prod.fst ∘ (glue) = Prod.fst` collapse, then `PMF.bind_map` to transport
  along `stepLog_map_fst`.
- `runLog_length_le` — at most `n` log entries in `n` steps
  (support-level induction via `PMF.mem_support_bind_iff` /
  `mem_support_map_iff`).
- `runLog_of_pickBad_none` — from a good state the run is `pure (v, [])`.
- `pickBad_isBad` — `pickBad` only returns violated events
  (`simp only [pickBad]` zeta-reduces the `let`; `split at`).
- `mem_log_pickBad` — provenance: every logged index was returned by
  `pickBad` at some state, hence was violated when resampled.

**Next (S18 proper)**: `witness_prob_bd`. With `runLog` in place the
statement can be phrased over `(runLog n v).support` / probabilities:
Pr[τ extractable from the log] ≤ ∏_{vertices} uniformDrawProb (labelOf ·).
The hard content is the resample-table coupling (MT §5): each vertex of τ
consumes one fresh uniform draw of its `vbl`-variables; needs either an
explicit product-space presentation of the randomness or an inductive
coupling over `runLog`'s bind structure. Est. 2+ sessions; consider a
design memo (S18a PREP) first.
