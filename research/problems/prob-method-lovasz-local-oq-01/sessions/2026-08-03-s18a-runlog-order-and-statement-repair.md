# S18a — runLog order repair + `witness_prob_bd` statement infrastructure

**Date**: 2026-08-03
**Researcher**: researcher-1 (worktree researcher-1-13b)
**Mode**: ACT (correctness repair + statement infrastructure) + PREP (coupling design)
**File**: `proofs/Proofs/MoserTardos.lean`

## §1 Context

S17 landed `witness_valid` (extraction propriety) and S18-prep landed the
instrumented runner `stepLog`/`runLog` (PR #43448). The tracker's next action
was "S18a PREP design memo (product-space presentation of the randomness vs
inductive coupling over runLog bind structure) before `witness_prob_bd` ACT".
This session performs that design pass — and in doing so found **two
statement-level defects** that had to be repaired *before* any coupling work
is built on top of them. Both are fixed in this PR; the coupling design
recommendation is §6.

## §2 Finding 1 — log-order convention mismatch (repaired)

### The defect

- `runLog` (S18-prep revision) emitted the resample log **most-recent-first**:
  `runLog (n+1) v = stepLog v >>= fun p => (runLog n p.1).map fun q =>
  (q.1, q.2 ++ p.2.toList)` — the chronologically first step's entry `p.2`
  was appended at the *end* of the list.
- `ExtractsFrom j (k :: l) τ'` requires a derivation of `ExtractsFrom j l τ`
  for the tail *first* and then attaches the head `k` to the result. So in a
  derivation, the list's **last** element is attached **first** and the head
  is attached **last**.
- Moser–Tardos §4 builds the witness tree walking the log **backwards in
  time**: the most recent entry is attached first, the oldest last.

Composite effect: on a most-recent-first log, `ExtractsFrom` attached entries
**oldest-first** — the exact reverse of MT §4. The S18-prep docstrings
("entries processed head-first, i.e. backwards in execution time") assumed the
head of the list is processed first; it is processed last.

### Counterexample (the orders genuinely differ)

Variables `{a, b}` (plus the root's variable); events `j`, `X`, `Y` with
`vbl j = {a}`, `vbl X = {a, b}`, `vbl Y = {b}`. Then `X ∈ Γ(j)`, `Y ∈ Γ(X)`,
but `Y ∉ Γ⁺(j)`. Execution log (oldest → newest): `X, Y`.

- **MT §4 (most recent attached first)**: root `j`; process `Y`: no vertex of
  the bare root matches (`Y ∉ Γ⁺(j)`) → **skip**; process `X`: matches the
  root → attach. Extracted tree: `j` with single child `X` (2 vertices).
- **Old composite (oldest attached first)**: attach `X` under the root
  (match); then attach `Y`: `Y ∈ Γ⁺(X)` matches at depth 1, deepest → attach
  under `X`. Extracted tree: the path `j — X — Y` (3 vertices).

Different trees; and downstream the difference is fatal — MT's resample-table
argument needs "deeper vertex = earlier resample" (each vertex's table-slot
index is computed from the vertices *below* it), which only the MT order
provides. The skipped-`Y` behaviour is also load-bearing: `Y`'s resample does
not causally precede `j`'s certification, so it must *not* be charged to the
tree.

### The repair (minimal-churn option chosen)

Flip `runLog` to emit **execution order** (`p.2.toList ++ q.2`, oldest entry
at the head). Then `ExtractsFrom`, unchanged, attaches from the tail = most
recent first = MT §4. Alternatives rejected:

- *Re-define `ExtractsFrom` to attach the head first* (accumulator-style
  relation): churns the whole proven Part VI (`witness_valid`,
  `isProper_attach` induction structure) for no mathematical gain.
- *Keep both and reverse at the use site* (`ExtractsFrom j p.2.reverse τ`):
  pushes `List.reverse` through every future induction over the bind
  structure; permanent tax.

Adaptation cost of the flip: `runLog_map_fst` (lambda text only),
`mem_log_pickBad` (swap the two `List.mem_append` branches),
`runLog_length_le` / `runLog_of_pickBad_none` (unchanged). Part VI is
untouched. A pleasant structural consequence: the outermost `bind` layer of
`runLog (n+1)` (the first step) now corresponds to the **outermost**
constructor layer of an `ExtractsFrom` derivation over the emitted log
(both handle the oldest entry last-attached/first-bound), which is the
alignment any inductive coupling proof would want; and "the log entries
strictly before time `t`" is now a list **prefix**, not a suffix.

## §3 Finding 2 — the fixed-start per-tree bound is false

The tracker's S18 target was stated as "Pr[τ extractable from the `runLog`
log] ≤ ∏ over vertices of `uniformDrawProb (labelOf v)`" — implicitly over
`runLog n v` for a fixed start `v`. That statement is **false**:

Take one variable with alphabet `{0, 1}`, one event `A` with `vbl A = {P}`
and `isBad A v ↔ v P = 0`, so `uniformDrawProb A = 1/2` and `Γ⁺(A) = {A}`.
Fix the start `v₀` with `v₀ P = 0` (violated). Every step from a violated
state resamples `P` and logs `A`; the log after `n` steps is `A^L` where `L`
is the waiting time for the first good state. On an all-`A` log every entry
matches (deepest = bottom of the path), so the tree extracted from a log of
length `m` is the path on `m + 1` vertices, `τ_m`. For `1 ≤ m < n`:

    Pr[τ_m extracted] = Pr[L = m] = (1/2)^(m-1) · (1/2) = 2^(-m)

(the first factor: resamples 1..m-1 must redraw `0`; the last: resample `m`
draws `1`; the start is bad for free). The would-be bound is
`weight τ_m = (1/2)^(m+1)`. So the claim fails by a factor of 2 — exactly
the missing probability of the initial state being bad.

With **uniform initialization** the same computation gives
`Pr[τ_m extracted] = (1/2) · 2^(-m) = 2^(-(m+1)) = weight τ_m` — the bound
holds **with equality**, confirming (a) random initialization is a
non-negotiable part of the statement (as in MT 2010, where the algorithm's
first step is sampling all variables), and (b) the per-tree bound is sharp,
so any correct proof must use the fresh-randomness structure exactly (no
slack to give away per vertex).

**Repair**: new `mtRun n := (PMF.uniformOfFintype P.State).bind (P.runLog n)`
(Part VIII) — the process `witness_prob_bd` quantifies over — with
conservativity `mtRun_map_fst`.

## §4 New statement infrastructure (Part VIII)

- `mtRun` / `mtRun_map_fst` — as above.
- `WitnessTree.weight : WitnessTree P → ℚ`,
  `weight (.node i ch) = uniformDrawProb i * (ch.map weight).prod` — the RHS
  of the bound, by nested structural recursion (same `t ∈ ch` recursion vein
  S16 validated); `@[simp] weight_node`, `weight_mem_unit_interval`,
  `weight_nonneg`, `weight_le_one`.

## §5 Corrected `witness_prob_bd` statement (S18b+ target)

For `j : Fin P.numEvents`, `τ : WitnessTree P` with `labelOf τ = j`
(propriety of τ is *not* needed as a hypothesis for the bound, though only
proper trees survive the later sum):

```
theorem witness_prob_bd (n : ℕ) (j : Fin P.numEvents) (τ : WitnessTree P) :
    (P.mtRun n).toOuterMeasure {p | WitnessTree.ExtractsFrom j p.2 τ}
      ≤ ENNReal.ofReal ((WitnessTree.weight τ : ℚ) : ℝ)
```

using the outer-measure idiom of Part V's `uniformDrawProb_eq_outerMeasure`
(no `MeasurableSpace` plumbing needed). Note the event is "τ is extracted
from the **whole** log with root j"; the eventual `mt_expected_step_bound`
needs the per-resampling variant (for the `t`-th log entry equal to `j`,
extract from the prefix before `t`) — with execution-order logs that prefix
is `l.take (t-1)`, and the whole-log event above is the `t = n+1` phantom
root case. The per-`t` bookkeeping is S18d assembly work, not coupling work.

## §6 Coupling-presentation decision (the S18a question)

Two candidate presentations for proving `witness_prob_bd`:

**(a) Product-space / resample-table (MT §5 verbatim).** Pre-sample a table
of independent uniforms — per-variable columns of fresh copies,
`T : (j : Fin P.numVars) → Fin (n + 1) → P.alphabet j` under
`PMF.uniformOfFintype` (column 0 = initialization) — and a deterministic
runner `runTable` consuming, at each resample of event `i`, the next unused
copy of each variable in `vbl i`. Steps:
  - S18b: `runTable` + write-counter bookkeeping; coupling lemma
    "`(uniform table).map runTable = mtRun n`" (pushforward equality), by
    induction on `n` using `resampleAt`'s product-of-uniforms structure
    (`resampleAt_apply_inside/_outside/_indep` are exactly the marginal API
    this needs — S5b's "load-bearing API surface" prediction realized).
  - S18c: the **slot invariant** (MT §5 key lemma): if `τ` is extracted,
    then for each vertex `v` of `τ`, at the moment `[v]` was resampled the
    value of each `P ∈ vbl [v]` was table cell
    `T P (#{w ∈ τ : w strictly below v, P ∈ vbl [w]} + adjustment)` — the
    cell index is **determined by τ alone**. This is where
    "deeper = earlier" (restored by Finding 1's repair) is consumed.
  - S18d: bound assembly: the extraction event is contained in an
    intersection of per-vertex events on **pairwise-disjoint** table cells;
    independence across cells + `uniformDrawProb` per event (via
    `vblFaithful`) gives the product; equality case sanity per §3.

**(b) Inductive coupling over the `runLog` bind structure.** Condition on
the first step and induct. The obstruction: the per-vertex probability
factors are *not* aligned with the bind layers — a vertex's event is
evaluated on randomness from the step *before* its own resample, and which
future entries attach where depends on the not-yet-seen suffix. A correct
invariant must carry "which coordinates of the current state will be read by
which future tree vertices" — i.e. it re-derives the table/slot bookkeeping
of (a), but smeared across a conditional-probability induction. Strictly
harder to state; no step is easier.

**Recommendation: (a)**, structured as S18b/S18c/S18d above (~3 sessions,
roughly 150–250 LOC each). S18c is the mathematical heart; S18b is
mechanical PMF work fully covered by the existing `resampleAt` marginal API;
S18d is bookkeeping + the `List.take` prefix plumbing.

## §7 Honesty block

- This session's Lean delta is a **repair + statement infrastructure**, not
  proof progress on the coupling itself: `runLog` order flip (Part VII),
  `mtRun`, `weight` + unit-interval bounds (Part VIII, ~110 LOC). 0 new
  sorries, 0 new axioms (file stays 0/0).
- Finding 1 means the S18-prep claim "runLog emits most-recent-first so
  ExtractsFrom consumes it directly" (knowledge JSON insight, PR #43448) was
  **wrong in direction**; the conservativity/length/provenance lemmas of
  S18-prep are order-agnostic and survive unchanged, so the S18-prep session
  retains its value. The affected JSON insight is corrected this session.
- Finding 2 means the tracker's `nextAction` statement of the S18 target was
  unprovable as written. Catching both before the multi-session coupling
  build is the point of a PREP pass; no prior Lean theorem was false (the
  order convention lived only in docstrings and the not-yet-stated bound).
- Session note: the original working tree (researcher-1-13) was janitor-
  reaped mid-session before first commit; work was reconstructed in
  researcher-1-13b and re-verified. Verification: `lake env lean` (host,
  v4.31.0, Mathlib pin `9a9483a9`) — 0 errors; `#print axioms` on
  `mtRun_map_fst`, `runLog_map_fst`, `mem_log_pickBad`,
  `weight_mem_unit_interval`, `witness_valid`: foundational only
  (`propext`, `Classical.choice`, `Quot.sound`).
