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

## Quick Reference: Modes

| Pool Status | Mode | Goal |
|-------------|------|------|
| Available problems exist | **FRESH** | Claim and work on new problem |
| Pool empty | **REVISIT** | Scout for new knowledge, attempt if promising |

```bash
# Check pool status
jq -r '.candidates | group_by(.status) | map({status: .[0].status, count: length}) | .[]' research/candidate-pool.json
```

---

## Session Preamble (MANDATORY)

**Before ANY other work, complete these steps:**

### Step 0: Check Aristotle Results

```
Use the aristotle_check_results MCP tool to:
- Retrieve any completed proofs from previous sessions
- See what's still pending
- Avoid duplicating work Aristotle already did
```

If completed proofs are found:
1. Read the retrieved solutions
2. Integrate them into the proof files
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
| 0 | **EMPTY** | Highest - explore immediately |
| 1-5 | **WEAK** | High - needs more research |
| 6-15 | **MODERATE** | Medium - continue if promising |
| 16+ | **RICH** | Lower - only if new approach found |

**Total Items** = insights + builtItems + mathlibGaps + nextSteps

### List Problems by Knowledge (Weakest First)

```bash
# Show all problems sorted by knowledge accumulation (ascending)
.lean/scripts/knowledge-scores.sh
```

### Selection Rule

When multiple problems are eligible:
1. **Always prefer EMPTY/WEAK knowledge** over MODERATE/RICH
2. Among same knowledge tier, use tractability as tiebreaker
3. Document why you chose a particular problem

---

## Pre-Work Assessment (MANDATORY)

Before ANY work, answer these questions:

### 1. The Value Question

> "If I complete this work, will I be meaningfully closer to a complete proof?"

If "no, but it's technically progress" → **STOP. That's not progress.**

### 2. The Proof Strategy Question

> "How will I cover infinitely many cases?"

Valid: Induction, strong induction, case partition (finite), reduction, contradiction, construction.
Invalid: "Verify n=7, 9, 11... and keep going" or "extend to n ≤ 1000".

### 3. The Build vs Block Question

> "If infrastructure is missing, can we build it ourselves?"

| Size | Decision |
|------|----------|
| < 300 lines | Build it this session |
| 300-500 lines | Build if high-value |
| 500-1000 lines | Consider alternative approach first |
| > 1000 lines | Likely truly blocked |

**Before marking `blocked`:** Always check for elementary alternatives and assess buildability.

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

---

## Mode 1: FRESH

### Step 1: Select Problem by Knowledge Score

**Prioritize problems with weakest knowledge accumulation:**

```bash
# Clean stale locks
find research/claims -name "*.lock" -type d -mmin +120 -exec rm -rf {} \; 2>/dev/null || true

# List available problems by knowledge score (lowest first)
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

**During implementation, use Aristotle strategically:**

1. **Classify each sorry** as TRIVIAL, HARD, or OPEN
2. **For HARD sorries:**
   - If stuck > 10 min → `aristotle_submit` async
   - Continue working on other sorries while Aristotle runs
   - Check `aristotle_status` every 5-10 min
3. **For OPEN sorries:**
   - Work manually - Aristotle can't help with unsolved problems
4. **For TRIVIAL sorries:**
   - Try manually first (should be quick)
   - Use `aristotle_prove` sync if you want instant answer

### Step 6: Release Lock & Submit Overnight Jobs

```bash
# Update pool, release lock
jq '(.candidates[] | select(.id == "PROBLEM_ID")).status = "STATUS"' research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json
rm -rf "research/claims/${PROBLEM_ID}.lock"

# If HARD sorries remain, submit for overnight processing
./research/scripts/aristotle-submit.sh proofs/Proofs/File.lean problem-id "End of session"
```

---

## Mode 2: REVISIT

When pool is empty, we scout for new knowledge and attempt if promising.

### Step 1: Select Problem (Knowledge-First)

**Prioritize by knowledge tier, then status:**

```bash
# List revisitable problems by knowledge score (lowest first)
.lean/scripts/knowledge-scores.sh --revisit
```

**Selection priority:**
1. Lowest knowledge score (EMPTY > WEAK > MODERATE > RICH)
2. Within same knowledge tier: `in-progress` > `surveyed` > `skipped`

### Step 2: Read Context

1. Read `research/problems/<id>/knowledge.md` - full history
2. Read pool notes: `jq '.candidates[] | select(.id == "<id>")' research/candidate-pool.json`
3. Understand why it stalled

### Step 3: Scout for Changes

Search for new knowledge:
- `WebSearch "Mathlib4 [topic] 2025 2026"`
- `WebSearch "Mathlib4 GitHub PR [topic] merged"`
- `WebSearch "[theorem] elementary proof"`

**Decision point:**
- Found new infrastructure/approach → Proceed to attempt
- Nothing new → Document scout, pick different problem or end session

### Step 4: Attempt (if promising)

1. Propose NEW approach (different from previous attempts)
2. Apply Pre-Work Assessment
3. **Classify sorries and delegate to Aristotle:**
   - HARD sorries → `aristotle_submit` async, work on OPEN ones
   - OPEN sorries → Work manually (Aristotle can't help)
   - Check `aristotle_status` periodically
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
4. Use `.lean/scripts/archive-sessions.sh <problem-id>` to archive

### Archive Sessions

```bash
# Archive old sessions for a problem (keeps last 5)
.lean/scripts/archive-sessions.sh pnp-barriers

# Manual archive: move session block to sessions/YYYY-MM-DD-sNN.md
```

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

---

## Files Reference

| File | Purpose |
|------|---------|
| `research/candidate-pool.json` | Problem registry |
| `research/claims/<id>.lock/` | Atomic locks |
| `research/problems/<id>/knowledge.md` | Problem history |
| `proofs/Proofs/*.lean` | Proof files |
| `research/aristotle-jobs.json` | Aristotle job tracking |
| `research/SORRY-CLASSIFICATION.md` | Sorry classification guide |

---

## Aristotle Integration

Aristotle is a powerful proof search tool. Use it strategically alongside manual proof work.

### Tool Roles

| Tool | Strength | Best For |
|------|----------|----------|
| **Claude** | Strategic reasoning, creativity | OPEN problems, proof architecture, new approaches |
| **Aristotle** | Proof search, tactic grinding | HARD problems with known proofs |

**Our mission is solving OPEN problems!** But use tools appropriately:
- Aristotle formalizes KNOWN mathematics (proof exists somewhere)
- Claude attempts UNKNOWN mathematics (creative work needed)

### Sorry Classification

| Classification | Description | Send to Aristotle? |
|----------------|-------------|-------------------|
| **TRIVIAL** | Direct computation | Yes (fast, 1-5 min) |
| **HARD** | Known result, needs formalization | Yes (may take hours) |
| **OPEN** | Unsolved conjecture | **NEVER** - work on it ourselves! |

---

## Session Start: Check Aristotle Results (MANDATORY)

**Every research session MUST begin by checking for completed Aristotle jobs:**

```
Use aristotle_check_results to:
1. Auto-retrieve any completed proofs from overnight/previous sessions
2. See status of pending jobs
3. Plan around what Aristotle is working on
```

This prevents duplicate work and integrates overnight progress immediately.

---

## Real-Time Aristotle Usage

### When to Submit During Active Work

| Situation | Action |
|-----------|--------|
| Stuck on a proof goal > 10 min | Submit async, continue other work |
| Multiple independent HARD sorries | Submit all in parallel |
| Need a helper lemma | Let Aristotle prove it while you work on main theorem |
| Blocked by tedious case analysis | Perfect for Aristotle |
| Creative/novel approach needed | Work manually - Aristotle can't innovate |

### Async Workflow (Recommended)

```
1. Identify HARD sorry that's blocking progress
2. Use aristotle_submit → get project_id
3. Continue working on other parts of the proof
4. Check aristotle_status periodically (every 5-10 min)
5. When COMPLETE, use aristotle_retrieve
6. Integrate solution and continue
```

This keeps you productive while Aristotle grinds on tactical proofs.

### Sync Workflow (Quick Proofs)

For TRIVIAL sorries or when you need an immediate answer:

```
Use aristotle_prove directly:
- Waits for completion (typically 1-5 minutes)
- Returns the solved proof immediately
- Good for simple lemmas you expect to be fast
```

---

## Available MCP Tools

| Tool | Use Case | Blocking? |
|------|----------|-----------|
| `aristotle_prove` | Quick proofs, need answer now | Yes |
| `aristotle_submit` | Long proofs, want to continue working | No |
| `aristotle_status` | Check progress on async job | No |
| `aristotle_retrieve` | Get completed solution | No |
| `aristotle_check_results` | Session start, batch retrieval | No |
| `aristotle_informal` | Natural language → Lean | Yes |
| `aristotle_list` | See all your projects | No |

---

## Strategic Delegation Checklist

Before attempting a sorry manually, ask:

1. **Is this OPEN or HARD?**
   - OPEN → Work on it manually (Aristotle can't help)
   - HARD → Consider Aristotle

2. **How long will manual proof take?**
   - < 5 min → Do it yourself
   - 5-15 min → Your call
   - > 15 min → Submit to Aristotle, work on something else

3. **Is this on the critical path?**
   - Yes → Maybe work manually for immediate progress
   - No → Submit async, prioritize critical work

4. **Do I have other productive work?**
   - Yes → Submit async, do other work
   - No → Try manually first, submit if stuck

---

## Parallel Workflow Example

```
Session starts:
1. aristotle_check_results → Found 2 completed proofs from last night!
2. Integrate those solutions
3. Identify 3 HARD sorries in current file
4. Submit all 3 with aristotle_submit (get 3 project_ids)
5. Work on the 1 OPEN sorry manually
6. Every 10 min: check aristotle_status on the 3 jobs
7. As jobs complete: retrieve and integrate
8. End session: any still pending will continue overnight
```

---

## Overnight Submissions

For complex proofs expected to take hours:

```bash
# Submit via script for logging
./research/scripts/aristotle-submit.sh proofs/Proofs/File.lean problem-id "Notes"

# Or via MCP tool
Use aristotle_submit with the file path

# Next morning: aristotle_check_results auto-retrieves completed work
```

### Success Example: Erdős #728

- **Input:** File with HARD sorries only
- **Runtime:** 6 hours
- **Output:** 1,416 lines of complete proof
- **Result:** Zero sorries, builds successfully

---

## Anti-Patterns

| Pattern | Why Wrong | Do Instead |
|---------|-----------|------------|
| Submit OPEN problems | Aristotle spins forever, wastes API | Work manually |
| Wait for sync proofs > 5 min | Blocks your session | Use async submit |
| Never check results | Miss completed work | Check at session start |
| Submit everything | Wastes resources on easy stuff | Triage first |
| Manual proof search for hours | Aristotle is better at this | Submit after 10-15 min stuck |
