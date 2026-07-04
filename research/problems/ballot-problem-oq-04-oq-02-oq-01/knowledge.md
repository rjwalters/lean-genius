# ballot-problem-oq-04-oq-02-oq-01 — Non-Crossing Partitions are Counted by Catalan

**Goal:** `nonCrossingCount n = catalan n`, where `nonCrossingCount n` (from
`ballot-problem-oq-04-oq-02`) is `Fintype.card {P : Finpartition (univ : Finset (Fin n)) // IsNonCrossingFp P}`.

This is **openQuestion[2]** of the sibling entry `ballot-problem-oq-04-oq-02`:
> "Establish the Catalan recurrence directly on the Finpartition model — decompose by the
> block containing the last index (or by first return) to obtain
> `nonCrossingCount (n+1) = ∑ nonCrossingCount i · nonCrossingCount (n−i)`, matching Mathlib's
> catalan recurrence without constructing the full bijection."

## Summary of state

The open counting statement has been **reduced to one combinatorial recurrence**. Everything
except that recurrence is proved with 0 sorry.

## Session 2026-06-30 (researcher-2) — unconditional `n ≤ 3` anchor (the sorry stays BLOCKED)

**Mode:** ACT (STUCK → add an independent, non-circular verified result rather than touch the
blocked bijection). **Outcome:** PROGRESS (new 0-axiom theorem; the sole `sorry`
`nonempty_firstReturnEquiv` is unchanged — it remains the hard, multi-session BLOCKED core).

- Added **`nonCrossingCount_eq_catalan_of_le_three {n} (hn : n ≤ 3) : nonCrossingCount n =
  catalan n`** — discharges the conjecture **unconditionally for n ≤ 3**, i.e. *without*
  assuming the open `nonempty_firstReturnEquiv` (the full `nonCrossingCount_eq_catalan` is only
  conditional on it). For n ≤ 3 every partition of `Fin n` is non-crossing
  (`nonCrossingCount_eq_card_of_n_le_three`), so the count = the Bell number
  `Fintype.card (Finpartition (Fin n))` (= 1,1,2,5), evaluated by **kernel `decide`**; Bell =
  Catalan up to n=3. Complements `nonCrossingCount_four_lt` (the n=4 Bell>Catalan drop) — the
  two now pin the conjecture on both sides of its first nontrivial test.
- **Verified 0-axiom** host `lake env lean` (`#print axioms = [propext, Classical.choice,
  Quot.sound]`; `decide` is KERNEL reduction, NOT `native_decide`, so no `Lean.ofReduceBool`).
  Full file EXIT 0, only the pre-existing line-105 sorry warning.

### Reusable gotchas
- `Fintype.card (Finpartition (Fin n))` is **not** `decide`-able at default depth — needs
  `set_option maxRecDepth 8000`; even then it's only feasible for tiny n (Bell numbers).
- `catalan n` does **not** reduce by `decide`/`rfl` (well-founded recursion). Evaluate via
  `simp [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
  catalan_zero]` (catalan 1 needs only `simp [catalan_succ']`).

### Status of the BLOCKED core (3rd session touching it; UNCHANGED)
`nonempty_firstReturnEquiv` (the first-return bijection) is the entire combinatorial difficulty
and is **not** in Mathlib in any form (no non-crossing-partition theory, no Finpartition
interval-restriction). Aristotle has been down (404) every session. This is genuinely BLOCKED;
do not add scaffolding around it — build the restriction theory or wait for Aristotle.

## Session 2026-06-26 (Session 1) — Structural reduction

**Mode:** FRESH
**Outcome:** progress (reduction + base case proved; recurrence isolated as 1 sorry)

### What I did
- Triaged the available pool. Found three Seeker "gallery-gap" candidates were already
  proved in the gallery/Mathlib (composite Wilson converse → `WilsonsTheoremOQ01`/`OQ05OQ01`;
  Basel π²/8 → `BaselProblemOQ09.lean:116`; X³−2 irreducibility →
  `AngleTrisectionOQ02OQ01OQ02.lean:128`) and that Jordan–Hölder for modules is already in
  Mathlib (`JordanHolderModule.instJordanHolderLattice`). Selected this candidate as the
  genuine, substantive gap building on the deepest existing infrastructure.
- Created `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean`:
  - `nonCrossingCount_zero : nonCrossingCount 0 = 1` (0 sorry).
  - `nonCrossingCount_recurrence` — STATED to match Mathlib's `catalan_succ'`
    (`∑ ij ∈ antidiagonal n, …`); body is the single outstanding `sorry`.
  - `nonCrossingCount_eq_catalan : nonCrossingCount n = catalan n` — proved by
    `Nat.strong_induction_on`, rewriting each antidiagonal factor by the IH (0 sorry beyond
    its dependence on the recurrence).
- Created the gallery entry data and research problem JSON.

### Key findings
- Mathlib's `catalan` is *defined* by the antidiagonal convolution, and `catalan_succ'`
  exposes it; so `nonCrossingCount = catalan` is a 4-line strong induction once the same
  recurrence is known for `nonCrossingCount`. The whole problem collapses to the recurrence.
- The recurrence must be proved combinatorially and independently (assuming the goal would be
  circular).
- Mathlib has **no** non-crossing partition theory and **no** Finpartition block-gap
  decomposition lemma — both would need to be built for the recurrence.

### Files modified
- `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean` (new, 1 sorry)
- `src/data/research/problems/ballot-problem-oq-04-oq-02-oq-01.json` (new)
- `src/data/proofs/ballot-problem-oq-04-oq-02-oq-01/` (new gallery entry)

### Next steps
- Prove `nonCrossingCount_recurrence` via the first-return block decomposition: in a
  non-crossing Finpartition of `Fin (n+1)`, the block of `0` splits the remaining indices into
  intervals each carrying an independent non-crossing partition; assemble the `Equiv` to
  `Σ ij ∈ antidiagonal n, (nc of Fin i) × (nc of Fin j)` and take `Fintype.card`.
- Or build the explicit Dyck↔partition bijection (sibling `ballot-problem-oq-04-oq-01`) and
  transport `DyckWord.card_dyckWord_semilength_eq_catalan`.
- Retry Aristotle on the recurrence sorry — the MCP endpoint returned "Resource not found"
  this session (service unavailable), so the async submission did not register.

## Session 2026-06-26 (Session 2) — Aristotle outage confirmed; crux still blocked

**Mode:** REVISIT
**Outcome:** no Lean progress (honest). The single `nonCrossingCount_recurrence` sorry is
unchanged; no fabricated scaffold was added.

### What I did / found
- **Aristotle is DOWN, not merely flaky.** Both `prove_file` (async) and the host smoke
  test (`scripts/aristotle/mcp-smoke-test.sh`) fail with HTTP **404 Not Found** on
  `https://aristotle.harmonic.fun/api/v1/project?project_type=2`. This is a server-side
  endpoint outage (the API path appears to have moved/retired), identical to Session 1's
  "Resource not found". **Do not spend time on Aristotle submissions until the smoke test
  passes again.**
- Re-confirmed the reduction is sound and the crux is correctly isolated: `nonCrossingCount_zero`
  and `nonCrossingCount_eq_catalan` are 0-sorry; only the recurrence remains.
- **Buildability verdict: BLOCKED on infrastructure (>1000 lines).** Proving the recurrence
  in the Finpartition model requires constructing the first-return decomposition `Equiv`
  `{P : Finpartition (Fin (n+1)) // IsNonCrossingFp P} ≃ Σ ij ∈ antidiagonal n, (nc Fin i) × (nc Fin j)`
  from scratch — Mathlib has no non-crossing-partition theory and no block-gap / interval
  re-indexing lemmas for `Finpartition`. This is genuinely multi-session foundational work,
  not a tactical-search target.

### Sharper decomposition plan for a future session (pick ONE track)
1. **Finpartition first-return track.** Let `k = max (P.part 0)` (the largest index sharing
   0's block — the "arch closing point"). Non-crossing forces every block to lie entirely in
   `[1, k-1]` (interior of 0's arch) or entirely in `[k+1, n]` (exterior); 0's own block can
   touch only the arch endpoints. Map `P ↦ (P restricted to interior, P restricted to
   exterior)` with sizes `(k-1, n-k)` summing over `antidiagonal n`. The hard lemmas are
   (a) "no block straddles k" (this IS the non-crossing condition) and (b) the two
   restrictions are themselves non-crossing and the assignment is an `Equiv`. Needs
   `Finpartition` interval-restriction and re-indexing infra built first.
2. **Dyck-word transport track.** Build the explicit bijection to `DyckWord` (sibling
   `ballot-problem-oq-04-oq-01`, which researcher-8 found was a near-duplicate / subsumed)
   and transport Mathlib's `DyckWord.card_dyckWord_semilength_eq_catalan`. Heavier setup but
   reuses Mathlib's proven Catalan-Dyck side; avoids re-deriving the recurrence.

Track 1 is closer to the file's stated approach; track 2 reuses more Mathlib. Either is a
dedicated multi-session build, not a single proof-search call.

## Session 2026-06-28 (Session 3) — Aristotle still down; flagged BLOCKED

**Mode:** REVISIT (researcher-2)
**Outcome:** no Lean progress (honest). The single `nonCrossingCount_recurrence` sorry is
unchanged. No scaffolding added.

### What I did / found
- **Aristotle remains DOWN.** Submitted the recurrence sorry via the MCP `prove` tool
  (async, with both sibling files as `context_files` and a first-return-decomposition hint);
  it returned `{"status":"error","message":"Resource not found."}` — identical to Sessions 1
  and 2. The host smoke test (`scripts/aristotle/mcp-smoke-test.sh`) still 404s on
  `https://aristotle.harmonic.fun/api/v1/project?project_type=2`. The endpoint outage that
  began before Session 1 has not recovered. (The `running`/`submitted` entries in
  `research/aristotle-jobs.json` are stale pre-outage jobs.)
- Re-confirmed the reduction is sound and the crux is correctly isolated: `nonCrossingCount_zero`
  and `nonCrossingCount_eq_catalan` (conditional on the recurrence) are 0-sorry; only the
  recurrence remains.
- **Verdict unchanged: BLOCKED on >1000-line foundational infrastructure.** Both tractable
  tracks (Finpartition first-return decomposition; Dyck-word transport) require building
  non-crossing-partition / Finpartition-interval-restriction theory that Mathlib lacks — this
  is multi-session foundational work, not a tactical target, and the one tool that could plausibly
  attempt the bijection in one shot (Aristotle) is unavailable.

### Status change
- Marked problem status `blocked` (3rd consecutive stuck session, per the researcher STUCK
  protocol). Re-open for active work when either (a) Aristotle's MCP endpoint recovers — retry
  the recurrence submission first — or (b) a dedicated multi-session build of the Finpartition
  non-crossing infrastructure is undertaken (track 1 above is the closest to the file's stated
  approach).

## Session 2026-07-04 (researcher-11) — n=4 direct computation ruled out (decide AND native_decide overflow)

**Mode:** REVISIT (problem was `blocked`; Aristotle re-checked and still down).
**Outcome:** no Lean progress on the crux (unchanged), but a **definitive negative result** that
closes off the most obvious "next case" idea and saves future sessions two Docker builds.

### What I checked
- **Aristotle still DOWN.** `scripts/aristotle/mcp-smoke-test.sh` still 404s on
  `https://aristotle.harmonic.fun/api/v1/project?project_type=2` (4th consecutive session). The
  MCP server *connects* now but the underlying endpoint is unchanged. Do not submit until the
  smoke test passes.

### The idea I tried (and why it's dead)
The prior anchor `nonCrossingCount_eq_catalan_of_le_three` covers `n ≤ 3` (all partitions
non-crossing → Bell number, kernel `decide`). The natural *strengthening* is the exact value at
the **first divergence** `n = 4`: prove `nonCrossingCount 4 = 14 = catalan 4` unconditionally
(the sibling only has the *inequality* `nonCrossingCount_four_lt : nonCrossingCount 4 < 15`,
proved abstractly via `Fintype.card_subtype_lt` — never the exact value). This would verify the
conjecture on all of `0 ≤ n ≤ 4`, through the first Bell/Catalan split.

**Both computational routes overflow — confirmed by Docker build, not speculation:**
- **Kernel `decide`** (even `set_option maxRecDepth 100000`): `Stack overflow detected. Aborting.`
  (Lean exit 134) after 43s. Kernel cannot reduce the `Fintype (Finpartition (Fin 4))`
  enumeration.
- **`native_decide`**: ALSO overflows — `interpreter stacktrace` through
  `Fintype.card ... nonCrossingCount.spec_0` → `Finset.image._redArg` → `List.dedup` →
  `List.pwFilter` (exit 134). The `Fintype (Finpartition α)` instance builds the partition set by
  `image`/`dedup`/`pwFilter` over a huge candidate set and blows the interpreter stack even
  compiled. So `nonCrossingCount 4` (and even the plain Bell count `Fintype.card (Finpartition
  (Fin 4)) = 15`) is **not** obtainable by `decide` OR `native_decide`. n≤3 worked only because
  `Finpartition (Fin 3)` is tiny (Bell 3 = 5).

### Consequence for future sessions
- **Do NOT retry `decide`/`native_decide` on `nonCrossingCount 4`** (or any `n ≥ 4`) — proven
  infeasible here. The `n ≤ 3` anchor is the computational ceiling for this Fintype instance.
- A non-computational `nonCrossingCount 4 = 14` would need either (a) Mathlib Bell-number theory
  (`Fintype.card (Finpartition (Fin 4)) = 15`, which Mathlib does not provide as a closed value
  reachable without the same overflow) plus a *uniqueness-of-the-crosser* lemma (crossing4Fp is
  the only crossing partition of Fin 4), or (b) the general first-return bijection itself. Both
  are foundational builds, not tactical targets.
- **Verdict UNCHANGED: BLOCKED.** The crux `nonempty_firstReturnEquiv` still needs the
  non-crossing-partition / Finpartition interval-restriction infrastructure Mathlib lacks, and
  the tempting computational shortcut at the divergence point is now ruled out. Re-open when
  Aristotle recovers (retry the recurrence sorry first) or for a dedicated multi-session infra
  build (track 1: Finpartition first-return decomposition).
