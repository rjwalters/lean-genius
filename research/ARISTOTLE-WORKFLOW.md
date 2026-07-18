# Aristotle Workflow — single source of truth

Aristotle (Harmonic) is our external proof-search service for Lean 4. This
document is the canonical reference for how the fleet interacts with it. Role
docs (`.lean/roles/researcher.md`, `.claude/commands/lean-research.md`) carry
only a role-specific quick reference and point here for everything else.

For **what to send** (classification of sorries), the canonical guide is
[`SORRY-CLASSIFICATION.md`](./SORRY-CLASSIFICATION.md); this document covers
**how to send it and get results back**.

## Division of labor

| Tool | Strength | Best For |
|------|----------|----------|
| **Claude** | Strategic reasoning, creativity | OPEN problems, proof architecture, new approaches |
| **Aristotle** | Proof search, tactic grinding | HARD problems with known proofs |

**Our mission is solving OPEN problems.** Aristotle formalizes KNOWN
mathematics (a proof exists somewhere); Claude attempts UNKNOWN mathematics
(creative work needed). Never submit OPEN conjectures — Aristotle will spin on
the server until it times out.

## Interface: the CLI pipeline (the only working path)

> **History (issue #38098):** an MCP wrapper (`septract/lean-aristotle-mcp`)
> was previously registered in `.mcp.json` and documented as the preferred
> route (`aristotle_submit` / `aristotle_prove` / `aristotle_check_results` /
> `aristotle_retrieve` tools). That wrapper pinned `aristotlelib ~=0.6.0` and
> broke when Harmonic cut over to the v1+ API server-side (~2026-03-18): 0.6.x
> clients now get **HTTP 426 Upgrade Required**, surfaced as "Resource not
> found". There is **no official MCP server** for `aristotlelib` 2.x. The MCP
> entry has been removed. Any doc or session note that still mentions the
> `aristotle_*` MCP tools is stale — use the CLI pipeline below.

Aristotle is driven through the `aristotle` CLI (from `aristotlelib`, invoked
as `uvx --from aristotlelib aristotle ...`). You normally do not call the CLI
directly — the shell pipeline in `scripts/aristotle/` handles submission,
polling, and result integration:

```bash
# 1. Sanity check: confirm the CLI is reachable and authenticated (free — a
#    read-only `aristotle list` call, no proof-search quota consumed).
./scripts/aristotle/cli-smoke-test.sh

# 2. Find candidate files and submit a batch (respects the ~3–5 concurrent cap).
./scripts/aristotle/submit-batch.sh --target 5

# 3. Poll for status and update local tracking (research/aristotle-jobs.json).
./scripts/aristotle/check-jobs.sh --update

# 4. Download completed results and integrate improvements into proofs/Proofs/.
./scripts/aristotle/retrieve-integrate.sh
```

Authentication: `ARISTOTLE_API_KEY` in the environment, or `~/.aristotle_key`
(the scripts read either).

## Submission tiers (what to send)

Classify each sorry per [`SORRY-CLASSIFICATION.md`](./SORRY-CLASSIFICATION.md):

| Classification | Action |
|----------------|--------|
| **TRIVIAL** | Prove it yourself — `simp`/`omega`/`linarith`/`decide` is faster than the round trip |
| **HARD** (known in the literature, only tactical search needed) | Package as `*StatementOnly.lean` and submit via `submit-batch.sh` |
| **OPEN** | Work on it yourself — that is **the mission**; Aristotle will only spin |
| **DEF SORRY** (`def foo := by sorry`) | Complete the definition first, *then* submit downstream theorem sorries — Aristotle skips definition sorries |
| **Sorry inside an axiom** | Convert `axiom` → `theorem ... := by sorry` if it really is provable, else leave it |

### When to submit vs. prove it yourself

Before attempting a HARD sorry manually, ask:

1. **How long will the manual proof take?** < 5 min → do it yourself;
   5–15 min → your call; > 15 min stuck → submit, work on something else.
2. **Is this on the critical path?** Yes → maybe work manually for immediate
   progress; No → submit async, prioritize critical work.
3. **Do I have other productive work?** Yes → submit async; No → try manually
   first, submit if stuck.

## Packaging: `*StatementOnly.lean` (recommended shape)

The unit of submission is **one theorem per file**: a `*StatementOnly.lean`
file with full imports, the single `theorem`/`lemma` statement, and an
informal `/- -/` proof-sketch docstring. See
[`SORRY-CLASSIFICATION.md`](./SORRY-CLASSIFICATION.md) §"Harmonic Submission
Format (recommended)" for the template. `submit-batch.sh` picks up
`*StatementOnly.lean` files first, then legacy `*Aristotle.lean` companion
files.

Inclusion criteria (regardless of file shape):

- NOT the main open conjecture
- Known result likely provable from Mathlib (monotonicity, cardinality,
  bounds, combinatorial identities, standard estimates)
- Clean theorem statement with no definition sorries
- No `axiom` declarations (convert to `theorem ... := by sorry` — Aristotle
  won't attempt axioms)

### Legacy `*Aristotle.lean` companion files (deprecated)

Do **not** hand-curate new multi-sorry `*Aristotle.lean` companion files
(previously the recommended pattern: an `ErdosNAristotle.lean` alongside
`ErdosNProblem.lean` bundling routine supporting lemmas). The MCTS proof
search is conditioned on *proof state + history + informal statement* per
sorry, so bundling many unrelated sorries into one file dilutes the search
budget. Existing `*Aristotle.lean` files keep working — the batch pipeline
still picks them up as a fallback — but they are no longer the recommended
shape for new submissions.

When a companion file completes, its proved lemmas still need to be manually
merged into the corresponding `*Problem.lean` file; `check-jobs.sh` /
`retrieve-integrate.sh` record this in the job's `outcome` field.

## v2 status model (what the scripts key off)

The v2 CLI splits status into two levels, which is why the shell scripts query
`RUNNING`/`IDLE` and then drill into tasks:

- **Project status** (`aristotle list --status`) is only `RUNNING` (a solve
  task is in flight) or `IDLE` (no task running — terminal). The old v1 enums
  (`NOT_STARTED`, `QUEUED`, `COMPLETE`, `FAILED`, …) were removed and now
  error.
- **Task status** (`aristotle tasks <project-id>` / `aristotle show
  <project-id>`) carries the fine-grained terminal outcome: `IN_PROGRESS`,
  `COMPLETE`, `COMPLETE_WITH_ERRORS`, `FAILED`, `CANCELED`, ….

## Async workflow (don't block)

Aristotle searches take minutes to hours. Submit a batch, then continue other
work (a different sorry, refactoring, the OPEN main conjecture). Poll every
~10 minutes with `check-jobs.sh`; integrate with `retrieve-integrate.sh` when
projects go `IDLE` with a `COMPLETE` task.

A typical session:

```
1. ./scripts/aristotle/check-jobs.sh --update       → found completed overnight jobs
2. ./scripts/aristotle/retrieve-integrate.sh        → integrate those solutions
3. Identify HARD sorries; package as *StatementOnly.lean
4. ./scripts/aristotle/submit-batch.sh --target N   → submit the batch
5. Work on the OPEN sorry manually
6. Every ~10 min: ./scripts/aristotle/check-jobs.sh --update
7. As jobs complete: ./scripts/aristotle/retrieve-integrate.sh
8. End session: pending jobs continue overnight; next session's Step 1 picks
   them up
```

**Every session starts with steps 1–2** — this prevents duplicate work and
integrates overnight progress immediately.

## Rate limits and concurrency

- **Concurrency cap**: at most ~3–5 concurrent projects (shared server cap).
  `submit-batch.sh` enforces this.
- **Cooldown file**: on a 429 / rate-limit response, `submit-batch.sh` writes
  a UTC timestamp ~5 minutes in the future to
  `.loom/state/aristotle-rate-limit-until`; subsequent invocations short-circuit
  until it passes.
- **Scale-to-zero marker**: `.loom/state/aristotle-scaled-to-zero` — check it
  (along with the cooldown file) before submitting fresh work.

## Result caching

Aristotle caches project results ~30 days server-side, so re-submitting the
exact same file within that window returns the prior result quickly without
burning fresh solver budget.

## Boundary translation (Mathlib v4.28 ↔ our v4.31 pin)

Aristotle's backend vendors **Mathlib v4.28.0** and **rewrites every submitted
project's `lean-toolchain` to v4.28.0** (issue #38098). Our `main` pins
`proofs/lean-toolchain` at **`leanprover/lean4:v4.31.0`** (flip #38066). The
operator decision (2026-07-13) was NOT to wait for the backend to move off its
pin, but to **translate at the boundary** — submit-side and integration-side —
because "they will eventually update too" (issue #38622).

Concretely, three rules govern the boundary:

**1. Submission side — the v4.28 rewrite is EXPECTED, not an error.**
`submit-batch.sh` / `preprocess-for-aristotle.sh` ship our pin's
`lean-toolchain` (v4.31.0) inside the temp project. The backend normalizes it
to v4.28 before elaborating. That is correct and requires no action. Do **not**
commit a `lean-toolchain` that came back inside an Aristotle result bundle.

**2. Integration side — drift-repair v4.28 → v4.31, automatically.**
Every returned proof is **v4.28-era Lean** and will not necessarily elaborate
on our v4.31 pin. `retrieve-integrate.sh` runs each retrieved solution through
`scripts/aristotle/drift-repair.sh` **before** integrating it:

- Applies the confident pure-rename subset of
  `research/toolchain-v4.31-rename-map.md` (§1), curated into the
  machine-readable table `scripts/aristotle/v428-to-v431-renames.tsv`
  (e.g. `le_or_lt`→`le_or_gt`, `div_le_div_iff`→`div_le_div_iff₀`,
  `not_mem`→`notMem` wave, `Set.mem_diff`→`Set.mem_sdiff`).
- Whole-identifier matching with Unicode-aware boundaries, so
  qualification-adds and `₀`-suffix adds are idempotent (safe to run on a file
  that is already partly v4.31).
- **Flags** — but does not blindly rewrite — names whose fix also changes a
  signature / argument order / field layout / RHS (rename-map §5), listed in
  `scripts/aristotle/v428-to-v431-flags.tsv` (e.g. `IsSolvableByRad`,
  `IsCyclic.commutative`, `AdjoinRoot.liftHom`). These need a human/Doctor.

Run it standalone to inspect drift on any file:

```bash
scripts/aristotle/drift-repair.sh --check proofs/Proofs/Foo.lean   # report only
scripts/aristotle/drift-repair.sh proofs/Proofs/Foo.lean           # repair in place (+.drift.bak)
```

**3. Verification side — gate on an in-container v4.31 build.**
Renaming makes a proof *elaborate-able*; it does not prove it GOES GREEN. Do
**not** trust the backend's own v4.28 success signal across the version gap. A
returned proof is only **verified** once it passes the same in-container v4.31
build gate as migration increments:

```bash
scripts/aristotle/verify-v431-build.sh proofs/Proofs/Foo.lean
#   exit 0 -> may mark verified   exit 1 -> do NOT mark verified   exit 3 -> pending (gate skipped)
```

This delegates to `./proofs/scripts/docker-build.sh` (NEVER bare `lake build`)
and targets whatever pin `main` carries, so it is automatically "the current
pin". `retrieve-integrate.sh` records the result on each job as
`v431_verified` (true only on exit-0) and `v431_verification`
(`verified` / `failed` / `pending`).

By default the heavy build gate is **not** run inline (a 60-min build per proof
would stall the integrate loop): retrieved proofs are integrated but left
`pending`. Set `ARISTOTLE_VERIFY_BUILD=1` on `retrieve-integrate.sh` to gate
inline, or run `verify-v431-build.sh` later (Aristotle agent / daemon) before
any gallery `meta.json` is marked `verified`. `ARISTOTLE_SKIP_BUILD_GATE=1`
forces the standalone gate to return `pending` without building.

> **Drift probe (follow-up).** Characterizing the *typical* v4.28→v4.31 drift by
> submitting a small live prove job and elaborating its output (originally gate
> (b) of #38066) is left to the Aristotle agent — it costs live API quota and is
> not needed to build the translation mechanism. The rename catalog (§1) already
> seeds the repair table from the #38065 burn-down; extend
> `v428-to-v431-renames.tsv` (and the map) as new drift is observed.

## Job tracking

Local job state lives in `research/aristotle-jobs.json` (maintained by
`check-jobs.sh --update` and `retrieve-integrate.sh`). Useful queries:

```bash
# Completed jobs awaiting integration
jq '.jobs[] | select(.status == "completed")' research/aristotle-jobs.json

# Companion-file integrations whose lemmas still need manual merging
jq -r '.jobs[] | select(.status == "integrated" and .companion_file == true) | .outcome' \
  research/aristotle-jobs.json
```

## Anti-patterns

| Pattern | Why Wrong | Do Instead |
|---------|-----------|------------|
| Submit OPEN problems | Aristotle spins forever, wastes quota | Work manually |
| Block the session waiting on a submission | Searches take minutes–hours | Submit async, keep working |
| Never check results | Miss completed work | `check-jobs.sh --update` at session start |
| Submit everything | Wastes budget on easy stuff | Triage per the tier table first |
| Manual proof search for hours on a HARD sorry | Aristotle is better at tactic grinding | Submit after 10–15 min stuck |
| Bundle many sorries in one file | Dilutes per-sorry search budget | One `*StatementOnly.lean` per theorem |

## Success example: Erdős #728

- **Input:** file with HARD sorries only
- **Runtime:** 6 hours
- **Output:** 1,416 lines of complete proof
- **Result:** zero sorries, builds successfully
