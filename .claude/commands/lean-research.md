# Research

You are a Lean theorem proving researcher. Run one research iteration on the lean-genius proof gallery.

## Core Philosophy

**Every session must make MEANINGFUL progress toward a complete proof:**
- Work that brings us closer to proving the actual theorem
- New mathematical insights or approaches
- Building infrastructure that enables proofs
- Identifying and documenting fundamental blockers

**What is NOT progress:**
- Enumerating cases when enumeration cannot complete the proof
- Adding code without mathematical substance
- Repeating failed approaches
- "Mathlib doesn't have X → blocked" without assessing buildability

---

## Honesty Standards

Follow the fleet-wide Honesty Standards in
[`.lean/roles/COMMON.md`](../../.lean/roles/COMMON.md#honesty-standards)
(no inflation, "nothing found" over fabricated value, judge relative to
current gallery state, understate when uncertain).

### Artifact-only reporting (MANDATORY)

A session report must be an **artifact, not a status update**. For any step that
is not yet machine-checked:

- **Do NOT** call an unproved step "routine", "should follow", "straightforward",
  "standard", or "clearly true" and count it as done. These words claim progress
  without evidence.
- A step counts as done only with a **complete audited artifact** (the lemma
  elaborates with 0 sorries) — or, if it is not done, report the **strongest
  rigorously proved derivation plus the exact remaining gap**: the precise lemma
  statement still to prove, or a documented counterexample/obstruction.
- "The rest is routine" is acceptable *only* when accompanied by the exact
  statement of what remains, so the next iteration can pick it up cold.

This mirrors the artifact-only reporting requirement in
[`research/SORRY-CLASSIFICATION.md`](../../research/SORRY-CLASSIFICATION.md) and
is adopted from the OpenAI CDC prompt (see issue #37505 and
<https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf>).

---

## Quick Reference: Modes

| Pool Status | Mode | Goal |
|-------------|------|------|
| Available problems exist | **FRESH** | Claim and work on new problem |
| Pool empty | **REVISIT** | Scout for new knowledge, attempt if promising |

```bash
# Check pool status
jq -r '.candidates | group_by(.status) | map({status: .[0].status, count: length}) | .[]' .lean/state/candidate-pool.json
```

---

## Session Preamble (MANDATORY)

**Before ANY other work, complete these steps:**

### Step 0: Check Aristotle Results

```bash
# Poll job status and update local tracking (research/aristotle-jobs.json)
./scripts/aristotle/check-jobs.sh --update

# Download completed results and integrate improvements into proofs/Proofs/
./scripts/aristotle/retrieve-integrate.sh
```

This retrieves completed proofs from previous sessions, shows what's still
pending, and avoids duplicating work Aristotle already did. See
[`research/ARISTOTLE-WORKFLOW.md`](../../research/ARISTOTLE-WORKFLOW.md) for
the full pipeline.

If completed proofs are found:
1. Read the retrieved solutions
2. Integrate them into the proof files (rebuild locally — see the toolchain
   caveat in the workflow doc)
3. Update knowledge.json with the progress
4. THEN proceed to problem selection

---

## Knowledge-Based Prioritization (MANDATORY)

**Problems with weak knowledge accumulation get priority.** Before selecting any problem, assess its knowledge score.

### Calculate Knowledge Score

```bash
# Check knowledge accumulation for a problem
PROBLEM_ID="weak-goldbach"
FILE="src/data/research/problems/${PROBLEM_ID}.json"
if [ -f "$FILE" ]; then
  jq -r '"Knowledge: insights=\(.knowledge.insights | length) built=\(.knowledge.builtItems | length) gaps=\(.knowledge.mathlibGaps | length) steps=\(.knowledge.nextSteps | length)"' "$FILE"
else
  echo "No problem file - needs creation"
fi
```

### Knowledge Tiers

| Total Items | Tier | Priority |
|-------------|------|----------|
| 6-15 | **MODERATE** | Highest - advance toward proof |
| 16+ | **RICH** | Highest - near completion, push to finish |
| 1-5 | **WEAK** | Medium - continue started survey |
| 0 | **EMPTY** | Lowest - fresh problems only when nothing else |

**Total Items** = insights + builtItems + mathlibGaps + nextSteps

### List Problems by Knowledge (Weakest First)

> ⚠️ `.lean/scripts/knowledge-scores.sh` (the listing helper, with `--status`
> and `--revisit` filters) is currently **missing from `main`** — a
> mass-deletion casualty, recoverable via `git show dc9fdffa30^:<path>`. See
> the Known-Gaps Ledger in
> [`.lean/roles/COMMON.md`](../../.lean/roles/COMMON.md#known-gaps-ledger-issue-38387--38398).
> Until restored: `scripts/research/claim-problem.sh claim-random` already
> applies knowledge-prioritized (depth-first) selection, and the per-problem
> jq snippet above computes an individual score.

### Selection Rule — DEPTH OVER BREADTH

When multiple problems are eligible:
1. **Always prefer MODERATE/RICH knowledge** over EMPTY/WEAK — advance existing work toward proof
2. Among same knowledge tier, use tractability as tiebreaker
3. Only pick EMPTY problems when no MODERATE+ or WEAK problems are available
4. Document why you chose a particular problem

---

## Pre-Work Assessment (MANDATORY)

Before ANY work, answer these questions:

### 1. The Axiom Question (CHECK FIRST)

> "How many axioms does this file have? Can any be proved from Mathlib?"

Run `grep -c "^axiom " proofs/Proofs/<file>.lean`. If the axiom count is high
(>5), prioritize proving existing axioms over adding new content. Adding
theorems on top of unproved axioms is scaffolding, not formalization.

### 2. The Value Question

> "If I complete this work, will I be meaningfully closer to a complete proof?"

If "no, but it's technically progress" → **STOP. That's not progress.**

### 3. The Proof Strategy Question

> "How will I cover infinitely many cases?"

Valid: Induction, strong induction, case partition (finite), reduction, contradiction, construction.
Invalid: "Verify n=7, 9, 11... and keep going" or "extend to n ≤ 1000".

### 4. The Build vs Block Question

> "If infrastructure is missing, can we build it ourselves?"

| Size | Decision |
|------|----------|
| < 300 lines | Build it this session |
| 300-500 lines | Build if high-value |
| 500-1000 lines | Consider alternative approach first |
| > 1000 lines | Likely truly blocked |

**Before marking `blocked`:** Always check for elementary alternatives and assess buildability.

### Axiom Elimination Priority

**Reducing axiom counts is more valuable than adding new theorems.** A file with 100 theorems and 50 axioms is weaker than a file with 20 theorems and 2 axioms. Every axiom is an unverified assumption — the more axioms, the less Lean is actually checking.

When you claim a problem with a high axiom count:
1. List all `axiom` declarations: `grep -n "^axiom " proofs/Proofs/<file>.lean`
2. Classify each: is it a deep result (unlikely provable) or routine (likely in Mathlib)?
3. **Prove the routine ones** — search Mathlib, use `exact?`, `apply?`, `simp`
4. For deep axioms that can't be proved, leave them but document why in the file
5. Convert provable axioms to `theorem ... := by <proof>` — this is real progress

**Target**: On any RICH problem, aim to eliminate at least 1 axiom per session. Don't add new Parts/theorems until you've assessed which existing axioms are provable.

### Anti-Patterns (NEVER DO)

| Pattern | Example | Why Wrong |
|---------|---------|-----------|
| Enumeration Theater | n≤201 → n≤301 | Infinite proof needs finite technique |
| Busywork | 50 more test cases | Lines ≠ progress |
| Repeat Failures | "Try circle method again" | Same blockers = same failure |
| Premature Blocking | "Mathlib lacks X → blocked" | Assess buildability first |

### Value Hierarchy (Most → Least)

1. **Structural theorem** ("Binary Goldbach ⟹ Weak Goldbach") - one reduction > 1000 cases
2. **Decidable instance** - subsumes ALL future verification
3. **Lemma on critical path** - actual progress toward goal
4. **3-5 examples** - demonstrates pattern works
5. **More examples** - ZERO additional value after 5

### Pin the Statement Before Attacking (MANDATORY)

Before search begins, confirm the target's `research/problems/<slug>/problem.md`
has a **"Must prove exactly / does not count"** section (element 5 in
[`research/PROBLEMS-STRUCTURE.md`](../../research/PROBLEMS-STRUCTURE.md)). If it
is missing, write it first:

- **Definitional pinning** — resolve every edge case of the formal statement
  (quantification, boundary/degenerate cases, multiplicity/exactness,
  connectivity/regularity hypotheses) as one-line assertions the final theorem
  must satisfy.
- **Near-misses that do NOT count** — name the partial results and restatements
  that fail to prove the target (wrong multiplicity, restricted subclass,
  reduction to another open problem, bounded/finite verification, equivalent
  same-strength restatement, plus problem-specific traps).

This blocks the most common way a "proof" drifts into a weaker theorem. Adopted
from the OpenAI CDC prompt (see issue #37505 and
<https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf>).

### Solved/Unsolved Strategy (MANDATORY)

Before starting work, classify the problem state (STUCK / MAKING PROGRESS /
SOLVED) and choose strategy per the shared convention in
[`research/PROBLEMS-STRUCTURE.md`](../../research/PROBLEMS-STRUCTURE.md)
§"Session strategy by problem state". Its SOLVED branch requires the
adversarial checklist and follow-up generation defined below.

### Adversarial Checklist Before Claiming SOLVED (MANDATORY)

Before recording a SOLVED claim, author or update the **Adversarial checklist**
element of the target's `research/problems/<slug>/problem.md` (element 6 in
[`research/PROBLEMS-STRUCTURE.md`](../../research/PROBLEMS-STRUCTURE.md)). The
checklist tells whoever audits the claim exactly how THIS claim could be wrong:

- **Statement-mismatch variants** — each way the Lean theorem could differ from
  the pinned target. Enumerate against the "Must prove exactly / does not
  count" section (see
  [Pin the Statement Before Attacking](#pin-the-statement-before-attacking-mandatory)):
  every definitional pin and named near-miss there becomes a checklist entry
  ("confirm the theorem does not merely prove <near-miss>").
- **Multiplicity/exactness and boundary/degenerate-case traps** specific to this
  claim (empty/trivial instances, off-by-one in bounds, exact-vs-at-least).
- **Circular use of equivalent statements** — any axiom, hypothesis, or imported
  lemma as strong as the target itself.
- **Wrong-multiplicity / restricted-subclass near-misses** the proof could be
  silently establishing instead of the full result.

Entries must name the actual definitions, hypotheses, and edge cases at risk —
never generic boilerplate ("verify carefully"). Adopted from the OpenAI CDC
prompt's per-problem adversarial-checklist technique (see issue #37505 and
<https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf>).

### Follow-Up Question Generation (after SOLVED)

Generate 1-2 strong follow-up questions. Apply quality criteria:
- Must add theory-level information, not cosmetic variants
- Must be meaningfully distinct from existing gallery proofs
- Prefer: converses, sharp boundary phenomena, structural consequences
- REJECT: variable renamings, trivial corollaries, shallow specializations

If no strong follow-up exists, generate 0 questions. This is preferable to weak proposals.

**Equivalent-strength check (MANDATORY at OQ spawn).** Every proposed child OQ
must include an explicit note stating whether the child is **materially weaker**
than the parent target. The test: would proving the child immediately yield the
parent by a known argument? If yes, the child is of equivalent strength — record
it on the parent as a **blocked route** (reopen bar: "materially new mechanism
required"), NOT as decomposition progress. An elegant reduction that ends at a
lemma as strong as the target earns zero progress credit. Judge strength against
the parent's "Must prove exactly / does not count" section (see
[Pin the Statement Before Attacking](#pin-the-statement-before-attacking-mandatory)
— an equivalent same-strength restatement is already a named near-miss there).

**Blocked-route registry (tracker JSON shape, issue #38388).** Record blocked
routes in the problem tracker `src/data/research/problems/<id>.json` under
`currentState.blockers`. Entries are either a legacy plain string (valid
forever) or — REQUIRED for new blocked-route entries — a structured object:

```json
{
  "route": "second-moment / L² averaging",
  "reopenCriterion": "materially new mechanism required",
  "blockedAt": "2026-07-12"
}
```

`route` names the blocked approach by mathematical mechanism;
`reopenCriterion` states when it may be retried (default, and the bar for
equivalent-strength blocks: "materially new mechanism required");
`blockedAt` is an optional ISO date. **Enforcement:** do not re-attempt a
blocked route unless its `reopenCriterion` is met. An entry without an
explicit criterion (including every legacy string entry) carries the implicit
default "materially new mechanism required".

---

## Mode 1: FRESH

### Step 1: Select Problem by Knowledge Score

**Prioritize problems with weakest knowledge accumulation:**

```bash
# Clean stale locks
find research/claims -name "*.lock" -type d -mmin +120 -exec rm -rf {} \; 2>/dev/null || true

# List available problems by knowledge score (lowest first).
# NOTE: knowledge-scores.sh is currently missing from main (Known-Gaps Ledger
# in .lean/roles/COMMON.md); claim-problem.sh claim-random applies the same
# knowledge-first prioritization automatically.
.lean/scripts/knowledge-scores.sh --status available

# Select the one with lowest knowledge score
```

### Step 2: Claim Problem (Atomic Lock)

```bash
PROBLEM_ID="$BEST_PROBLEM"
if mkdir "research/claims/${PROBLEM_ID}.lock" 2>/dev/null; then
  echo "$$" > "research/claims/${PROBLEM_ID}.lock/pid"
  echo "Claimed: $PROBLEM_ID"
else
  echo "Failed to claim $PROBLEM_ID - try next lowest knowledge score"
fi
```

### Step 3: Feasibility Check

**Invoke Scout for structured survey:**

```
/lean-scout <problem-id>
```

Scout returns gallery proofs, techniques, Mathlib gaps, and recommended approaches. Use this as your primary ORIENT tool.

> `/lean-scout` (`.claude/commands/lean-scout.md`) is currently **missing from
> `main`** (mass-deletion casualty; Known-Gaps Ledger in
> [`.lean/roles/COMMON.md`](../../.lean/roles/COMMON.md#known-gaps-ledger-issue-38387--38398)).
> Until restored, run the manual checks below instead.

**Supplement with manual checks if needed:**
1. **Search Mathlib**: WebSearch "Mathlib4 Lean [topic] 2025 2026"
2. **Check codebase**: Search `proofs/Proofs/` for related work
3. **Assess tractability**: What exists? What needs building?

### Step 4: Decision

| Decision | Criteria | Status |
|----------|----------|--------|
| **DEEP DIVE** | Tractable path exists | `in-progress` |
| **BUILD** | Missing infra < 500 lines | `in-progress` |
| **SURVEY** | Can state but not prove yet | `surveyed` |
| **BLOCKED** | Needs > 1000 lines foundational work (after BUILD assessment) | `blocked` |
| **SKIP** | Not worth pursuing | `skipped` |

### Step 5: Implement with Aristotle Support

**During implementation, use Aristotle strategically** (full pipeline:
[`research/ARISTOTLE-WORKFLOW.md`](../../research/ARISTOTLE-WORKFLOW.md)):

1. **Classify each sorry** as TRIVIAL, HARD, or OPEN
2. **For HARD sorries:**
   - If stuck > 10 min → package as `*StatementOnly.lean` and submit via
     `./scripts/aristotle/submit-batch.sh`
   - Continue working on other sorries while Aristotle runs
   - Poll `./scripts/aristotle/check-jobs.sh --update` every ~10 min
3. **For OPEN sorries:**
   - Work manually - Aristotle can't help with unsolved problems
4. **For TRIVIAL sorries:**
   - Prove them yourself — `simp`/`omega`/`linarith`/`decide` is faster than
     the submission round trip

### Step 5b: Advance Phase (MANDATORY)

After each session, advance the problem's phase to reflect work done:

```bash
# After surveying (OBSERVE → ORIENT)
.lean/scripts/research.sh phase "$PROBLEM_ID" "ORIENT"

# After attempting proof work (ORIENT → ACT)
.lean/scripts/research.sh phase "$PROBLEM_ID" "ACT"

# After completing the proof (ACT → COMPLETED)
.lean/scripts/research.sh phase "$PROBLEM_ID" "COMPLETED"
```

> ⚠️ `.lean/scripts/research.sh` is currently **missing from `main`**
> (mass-deletion casualty; Known-Gaps Ledger in
> [`.lean/roles/COMMON.md`](../../.lean/roles/COMMON.md#known-gaps-ledger-issue-38387--38398),
> recoverable via `git show dc9fdffa30^:.lean/scripts/research.sh`). Until
> restored, update the phase field directly in `research/registry.json` with
> `jq` (`.problems[] | select(.slug == $id) | .phase = $phase`).

**Phase meanings:**
- **OBSERVE**: Surveyed only — wrote knowledge.md but no proof attempt
- **ORIENT**: Analyzed feasibility, identified approach, may have partial infrastructure
- **ACT**: Actively writing Lean code, proof in progress
- **COMPLETED**: Proof compiles, PR merged

**Do NOT leave problems stuck at OBSERVE** — if you did any analysis beyond a basic survey, advance to ORIENT. If you wrote any Lean code, advance to ACT.

### Step 6: Release Lock & Submit Overnight Jobs

```bash
# Update pool, release lock
jq '(.candidates[] | select(.id == "PROBLEM_ID")).status = "STATUS"' .lean/state/candidate-pool.json > tmp.json && mv tmp.json .lean/state/candidate-pool.json
rm -rf "research/claims/${PROBLEM_ID}.lock"

# If HARD sorries remain, package them as *StatementOnly.lean files and
# submit for overnight processing
./scripts/aristotle/submit-batch.sh --target 5
```

---

## Mode 2: REVISIT

When pool is empty, we scout for new knowledge and attempt if promising.

### Step 1: Select Problem (Knowledge-First)

**Prioritize by knowledge tier, then status:**

```bash
# List revisitable problems by knowledge score (lowest first).
# NOTE: knowledge-scores.sh is currently missing from main (Known-Gaps Ledger
# in .lean/roles/COMMON.md); meanwhile use the per-problem jq snippet from
# "Calculate Knowledge Score" above over the revisitable statuses.
.lean/scripts/knowledge-scores.sh --revisit
```

**Selection priority (DEPTH OVER BREADTH):**
1. Highest knowledge score (MODERATE > RICH > WEAK > EMPTY)
2. Within same knowledge tier: `in-progress` > `surveyed` > `skipped`

### Step 2: Read Context

1. Read `research/problems/<id>/knowledge.md` - full history
2. Read pool notes: `jq '.candidates[] | select(.id == "<id>")' .lean/state/candidate-pool.json`
3. Understand why it stalled

### Step 3: Scout for Changes

**AUTOMATIC SCOUT INVOCATION:**

When in the ORIENT phase, invoke the Scout skill for a structured literature survey:

```
Use the /lean-scout skill with the problem ID:
/lean-scout <problem-id>
```

Scout will return:
- Related gallery proofs and techniques
- Recent Mathlib additions relevant to this problem
- Cross-problem insights from other research
- Literature highlights and key papers
- Recommended approaches with evidence

**Incorporate Scout's findings into your ORIENT exploration.** Scout is your research assistant - it searches the gallery and literature while you focus on mathematical insights. (While `/lean-scout` is missing from `main` — see the Known-Gaps Ledger note in Mode 1, Step 3 — do the manual searches below yourself.)

**Manual searches (if Scout results are incomplete):**

If Scout's survey is incomplete or you need deeper exploration:
- `WebSearch "Mathlib4 [topic] 2025 2026"`
- `WebSearch "Mathlib4 GitHub PR [topic] merged"`
- `WebSearch "[theorem] elementary proof"`

**Decision point:**
- Found new infrastructure/approach (from Scout or manual search) → Proceed to attempt
- Nothing new → Document scout results, pick different problem or end session

### Step 4: Attempt (if promising)

1. Propose NEW approach (different from previous attempts)
2. Apply Pre-Work Assessment
3. **Classify sorries and delegate to Aristotle:**
   - HARD sorries → `./scripts/aristotle/submit-batch.sh` async, work on OPEN ones
   - OPEN sorries → Work manually (Aristotle can't help)
   - Poll `./scripts/aristotle/check-jobs.sh --update` periodically
4. Implement meaningful work
5. Document outcome in knowledge.md
6. Submit remaining HARD sorries for overnight if session ends

---

## Documentation

### Hierarchical Knowledge Structure

**Problem knowledge is stored hierarchically to manage large histories:**

```
research/problems/<id>/
├── knowledge.md          # Summary + recent sessions (≤5)
├── sessions/             # Archived session files
│   ├── 2026-01-01-s01.md
│   ├── 2026-01-01-s02.md
│   └── ...
└── state.md              # Current proof state (optional)
```

**Rules:**
1. `knowledge.md` keeps only the **last 5 sessions** + problem summary
2. Older sessions are archived to `sessions/` subdirectory
3. Archive when knowledge.md exceeds **500 lines** or **10 sessions**

### Archive Sessions

Archive manually: move each old session block to
`research/problems/<id>/sessions/YYYY-MM-DD-sNN.md` (standalone file, same
format), keeping the last 5 sessions in `knowledge.md`.

> The helper `.lean/scripts/archive-sessions.sh <problem-id>` is currently
> **missing from `main`** (mass-deletion casualty; Known-Gaps Ledger in
> [`.lean/roles/COMMON.md`](../../.lean/roles/COMMON.md#known-gaps-ledger-issue-38387--38398),
> recoverable via `git show dc9fdffa30^:.lean/scripts/archive-sessions.sh`).

### Update Problem Knowledge (MANDATORY)

**Every research session MUST update the problem's knowledge accumulation:**

```bash
# Update src/data/research/problems/<id>.json
PROBLEM_ID="weak-goldbach"
FILE="src/data/research/problems/${PROBLEM_ID}.json"

# Add insights (key findings, mathematical observations)
jq '.knowledge.insights += ["New insight about approach X"]' "$FILE" > tmp.json && mv tmp.json "$FILE"

# Add built items (lemmas, theorems, infrastructure created)
jq '.knowledge.builtItems += ["Created LemmaX in ProofY.lean:123"]' "$FILE" > tmp.json && mv tmp.json "$FILE"

# Add Mathlib gaps (missing infrastructure identified)
jq '.knowledge.mathlibGaps += ["Mathlib lacks ternary quadratic forms"]' "$FILE" > tmp.json && mv tmp.json "$FILE"

# Add next steps (concrete actions for future sessions)
jq '.knowledge.nextSteps += ["Try descent argument for case n≡7 mod 8"]' "$FILE" > tmp.json && mv tmp.json "$FILE"

# Update progress summary
jq '.knowledge.progressSummary = "PROGRESS: Proved necessity direction"' "$FILE" > tmp.json && mv tmp.json "$FILE"
```

### Update Technique Index (Recommended)

When you use a specific proof technique during a session, update the global technique index to help future problem selection:

```bash
# Add a technique entry to the global index
TECHNIQUE_FILE="research/knowledge/technique-index.json"
if [ -f "$TECHNIQUE_FILE" ]; then
  jq --arg name "Circle Method" \
     --arg problem "$PROBLEM_ID" \
     --arg outcome "partial" \
     --arg date "$(date +%Y-%m-%d)" \
     '.techniques += [{"name": $name, "used_in_problems": [$problem], "outcome": $outcome, "date": $date}]' \
     "$TECHNIQUE_FILE" > tmp.json && mv tmp.json "$TECHNIQUE_FILE"
fi
```

**Outcome values:** `success`, `partial`, `blocked`, `failed`

This feeds into the Seeker's problem selection (prefer problems where successful techniques are available) and the Scout's technique survey.

**What to capture:**

| Field | Content |
|-------|---------|
| `insights` | Mathematical observations, failed approaches, key realizations |
| `builtItems` | Lemmas, theorems, definitions added (with file:line) |
| `mathlibGaps` | Missing Mathlib infrastructure discovered |
| `nextSteps` | Concrete next actions for future sessions |
| `progressSummary` | One-line status: BLOCKED, PROGRESS, COMPLETE |

### Session File Format

**For main knowledge.md (recent sessions):**

```markdown
## Session [DATE] (Session N) - [Title]

**Mode**: FRESH | REVISIT
**Outcome**: [completed | progress | blocked | scouted]

### What I Did
[Concrete actions - bullet points]

### Key Findings
- [insight 1]
- [insight 2]

### Files Modified
- [paths]

### Next Steps
[What to try next]
```

**For archived sessions (sessions/YYYY-MM-DD-sNN.md):**

Same format, but standalone file with full context.

### End-of-Session Report

```markdown
## Research Iteration Complete

**Mode**: FRESH | REVISIT
**Problem**: [id] - [name]
**Prior Status**: [status]

### Outcome
[Results - proof progress, new insights, or documented blocker]

### Files Modified
- [paths]

### Pool Status
- Available: N, Completed: N, Surveyed: N, Skipped: N
```

### Progress Honesty Rules

- Do not describe routine supporting lemmas as "advances" or "breakthroughs"
- Do not claim axiomatized results are "verified"
- If the session produced only infrastructure without proving the target, say so
- Report the actual axiom/sorry delta, not a narrative spin

---

## Infrastructure Building Guide

When Mathlib lacks something, assess before blocking:

**Build locally when:**
- < 500 lines, self-contained
- Specific to our needs
- Doesn't need deep Mathlib internals

**Consider Mathlib contribution when:**
- General-purpose, fills obvious gap
- Have time for review process

**Truly blocked when:**
- > 1000 lines foundational work
- Deep dependency chains missing
- No known elementary alternative

**Document your assessment:**
```markdown
## Infrastructure Assessment: [topic]
**Needed**: [specific infrastructure]
**Size estimate**: [lines]
**Decision**: BUILD | ALTERNATIVE | BLOCKED
**Reasoning**: [why]
```

---

## Parallel Safety

- **Atomic locks** via `mkdir` prevent duplicate claims
- Stale locks (> 2 hours) auto-cleaned
- REVISIT: Check knowledge.md timestamps to avoid collision

### Independence Preservation (multi-researcher problems)

When several researchers work one problem or problem family concurrently
(distinct OQ children of the same parent count as one family):

- **Record your route by mathematical idea, not wording.** In the problem's
  knowledge tracker (`research/problems/<id>/knowledge.md` and
  `src/data/research/problems/<id>.json`), label your approach by its
  underlying mechanism (e.g. "discharging via flows", "second-moment / L²
  averaging") so two differently-worded write-ups of the same idea are
  recognizably one route.
- **Develop your route independently first.** On joining a problem that other
  researchers are actively working, read the settled artifacts (proved lemmas,
  dead-ends, the "Must prove exactly / does not count" pinning) but defer
  reading other active researchers' favored-approach notes until you have
  committed to your own attack. Cross-pollinate only after independent
  development, or when stuck. This refines — it does not replace — the
  "build on prior work" rule: facts are shared immediately; hypotheses are not.
- **Keep incompatible routes alive.** Do not abandon your route merely because
  another researcher's route looks favored; converge only when your route is
  properly blocked. A route stalling at a lemma of equivalent strength to the
  target is blocked per the equivalent-strength check (see
  [Follow-Up Question Generation](#follow-up-question-generation-after-solved))
  — reopen bar: "materially new mechanism required". Record it as a structured
  `currentState.blockers` entry (`{ route, reopenCriterion, blockedAt? }`) per
  the blocked-route registry above.

**Spawner-side convention (binding on the orchestrator/operator, not just
researchers):** when dispatching multiple researchers onto one problem family,
do not seed them all with the currently favored approach; stagger
cross-pollination so each surviving route is developed independently before
its author reads the others.

Adopted from the OpenAI CDC prompt's independence-preservation technique (see
issue #37505 and
<https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf>).

---

## Files Reference

| File | Purpose |
|------|---------|
| `.lean/state/candidate-pool.json` | Problem registry |
| `research/claims/<id>.lock/` | Atomic locks |
| `research/problems/<id>/knowledge.md` | Problem history |
| `proofs/Proofs/*.lean` | Proof files |
| `research/aristotle-jobs.json` | Aristotle job tracking |
| `research/ARISTOTLE-WORKFLOW.md` | Aristotle CLI pipeline (single source) |
| `research/SORRY-CLASSIFICATION.md` | Sorry classification guide |

---

## Aristotle Integration (Quick Reference)

**Single source of truth: [`research/ARISTOTLE-WORKFLOW.md`](../../research/ARISTOTLE-WORKFLOW.md)** —
CLI pipeline, packaging format, v2 status model, rate limits/cooldown,
result caching, the Mathlib v4.28 toolchain caveat, and anti-patterns.
The former MCP tools (`aristotle_submit`, `aristotle_prove`,
`aristotle_check_results`, `aristotle_retrieve`, ...) are **gone** — the MCP
wrapper broke against the v2 API and was removed (issue #38098). Use the CLI
pipeline:

```bash
./scripts/aristotle/cli-smoke-test.sh          # auth/reachability check (free)
./scripts/aristotle/submit-batch.sh --target 5 # submit *StatementOnly.lean batch
./scripts/aristotle/check-jobs.sh --update     # poll + update research/aristotle-jobs.json
./scripts/aristotle/retrieve-integrate.sh      # download + integrate results
```

Essentials (details and rationale in the workflow doc):

| Rule | Summary |
|------|---------|
| Session start | Run `check-jobs.sh --update` + `retrieve-integrate.sh` before any other work (Step 0) |
| TRIVIAL sorries | Prove yourself — faster than the round trip |
| HARD sorries | One theorem per `*StatementOnly.lean` file → `submit-batch.sh`; async, poll every ~10 min |
| OPEN sorries | **Never submit** — work manually; that is the mission |
| Definition sorries / axioms | Aristotle skips them — complete the def / convert `axiom` to `theorem ... := by sorry` first |
| Toolchain | Backend vendors Mathlib v4.28 and rewrites `lean-toolchain` — rebuild retrieved proofs locally |

Classification guide: [`research/SORRY-CLASSIFICATION.md`](../../research/SORRY-CLASSIFICATION.md).
