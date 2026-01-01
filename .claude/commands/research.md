# Research

You are a Lean theorem proving researcher. Run one research iteration on the lean-genius proof gallery.

## Core Philosophy: Never Give Up

**Every research session must make progress.** Even if we can't prove a theorem, we can:
- Document a new approach we tried
- Add insights to the knowledge base
- Identify what would need to change for success
- Find new papers or techniques to explore

"No available problems" does not mean "stop." It means "dig deeper on blocked problems."

## Your Task

Execute a single research cycle. The mode depends on pool status:

| Pool Status | Mode | Goal |
|-------------|------|------|
| Available problems exist | **FRESH** | Claim and work on new problem |
| Pool empty | **REVISIT** | Re-attempt a blocked problem with fresh perspective |

---

## Step 0: Check Pool Status

First, check what's available:

```bash
# Check pool status
jq -r '.candidates | group_by(.status) | map({status: .[0].status, count: length}) | .[]' research/candidate-pool.json
```

If `available` count > 0, proceed to **Mode 1: FRESH**.
If `available` count = 0, proceed to **Mode 2: REVISIT**.

---

## Mode 1: FRESH (Available Problems Exist)

### Step 1.1: Claim a Problem

```bash
# List available problems
jq -r '.candidates[] | select(.status == "available") | "\(.id): \(.name)"' research/candidate-pool.json

# Pick one (random selection or first listed)
PROBLEM_ID="<selected-id>"
```

Save the problem ID.

### Step 1.2: Feasibility Check

1. **Search Mathlib** - Check what infrastructure exists
   - Use WebSearch for "Mathlib4 Lean [topic] 2025"
   - Check if key lemmas/definitions exist

2. **Check Codebase** - Look for existing related proofs
   - Search `proofs/Proofs/` for related files
   - Read any similar proofs

3. **Assess Tractability**
   - What's already in Mathlib?
   - What needs to be built from scratch?
   - Are there blocking dependencies?

### Step 1.3: Decision

| Decision | Criteria | Action |
|----------|----------|--------|
| **DEEP DIVE** | Tractable milestones exist | Create full proof file |
| **SURVEY** | Can define/state but not fully prove | Create stub with definitions, axioms |
| **SKIP** | Missing infrastructure, multi-week effort | Update notes with specific blockers |

### Step 1.4: Implement and Update Pool

After implementing, update the problem status in `research/candidate-pool.json`:

```bash
# Update status using jq (replace <problem-id> and <new-status>)
jq '(.candidates[] | select(.id == "<problem-id>")).status = "<completed|surveyed|skipped>"' research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json
```

Also update the `notes` field with what was learned.

---

## Mode 2: REVISIT (Pool Empty - Never Give Up)

When no available problems exist, we don't stop. We dig deeper.

### Step 2.1: Select a Blocked Problem

Read the pool and select a problem to revisit:

```bash
jq -r '.candidates[] | select(.status == "surveyed" or .status == "in-progress" or .status == "skipped") | "\(.id): \(.name) [\(.status)]"' research/candidate-pool.json
```

**Selection priority:**
1. `in-progress` - Continue stalled work
2. `surveyed` - We have definitions, try to prove more
3. `skipped` - Check if circumstances changed

Pick one. Prefer problems where:
- Time has passed (new Mathlib features may exist)
- We have related completed proofs (technique transfer)
- The skip reason was "infrastructure" not "impossible"

### Step 2.2: Deep Context Gathering

**This is critical. Read EVERYTHING about this problem:**

1. **Read the problem history**
   ```bash
   # Check if problem directory exists
   ls research/problems/<problem-id>/

   # Read accumulated knowledge
   cat research/problems/<problem-id>/knowledge.md

   # Read all previous approaches
   cat research/problems/<problem-id>/approaches/*/hypothesis.md
   cat research/problems/<problem-id>/approaches/*/post-mortem.md
   ```

2. **Read the skip/survey notes**
   ```bash
   jq '.candidates[] | select(.id == "<problem-id>")' research/candidate-pool.json
   ```

3. **Check what's changed since last attempt**
   - Search Mathlib for new lemmas: WebSearch "Mathlib4 [topic] 2025"
   - Check our gallery for new related proofs
   - Look for recent arXiv papers on the topic

### Step 2.3: Literature Search

**Actively search for new approaches:**

1. **arXiv search**: WebSearch "arXiv [problem topic] Lean formalization 2024 2025"
2. **Elementary proofs**: WebSearch "[theorem name] elementary proof"
3. **Survey papers**: WebSearch "[topic] survey recent progress"
4. **Mathlib PRs**: WebSearch "Mathlib4 GitHub PR [topic]"

**What to look for:**
- New proof techniques
- Simplified approaches
- Partial results we could formalize
- Infrastructure that now exists

### Step 2.4: Generate Novel Approach

Based on your research, propose a NEW approach not previously tried:

1. **Review what's been tried** (from knowledge.md, post-mortems)
2. **Identify gaps** - What approaches haven't we attempted?
3. **Apply new information** - What did literature search reveal?
4. **Propose something concrete** - Even if speculative

Write a brief hypothesis:
```markdown
## New Approach: [Name]

**Motivation**: [Why this might work]
**Key insight**: [What's different from previous attempts]
**First step**: [Concrete thing to try]
**Risk**: [What could go wrong]
```

### Step 2.5: Attempt Something

**You must try something concrete.** Options:

1. **Write new Lean code** - Even partial, even with sorry
2. **Extend existing survey** - Add new lemmas/definitions
3. **Prove a sub-lemma** - Break off tractable piece
4. **Create stepping stone** - Prove related simpler result

### Step 2.6: Document Progress

**Even failure is progress.** Update:

1. **Knowledge base** (`research/problems/<id>/knowledge.md`):
   ```markdown
   ## Session [date]

   ### Literature Reviewed
   - [papers/resources checked]

   ### Approach Attempted
   - [what we tried]

   ### Outcome
   - [what happened]

   ### Insights
   - [what we learned]

   ### Next Steps
   - [what to try next time]
   ```

2. **Pool notes** (update candidate-pool.json):
   - Add timestamp of revisit
   - Note new findings
   - Update tractability if warranted

---

## Report Template

End every session with:

```markdown
## Research Iteration Complete

**Mode**: FRESH | REVISIT
**Problem**: [id] - [name]
**Prior Status**: [available | surveyed | skipped | in-progress]

### What I Did
[Concrete actions taken]

### Outcome
[Results - proof progress, new insights, or documented failure]

### Key Findings
- [finding 1]
- [finding 2]

### Files Modified
- [paths]

### Knowledge Added
[Summary of insights added to knowledge base]

### Next Steps
[What the next researcher should try]

### Pool Status
- Available: N
- Surveyed: N
- In-progress: N
- Skipped: N
```

---

## Parallel Safety

This workflow is safe for multiple agents:
- Claims prevent duplicate work on FRESH problems
- REVISIT mode should note the session in knowledge.md to coordinate

---

## Files Reference

| File | Purpose |
|------|---------|
| `research/candidate-pool.json` | Problem registry with status |
| `research/claims/*.json` | Active claims |
| `research/problems/<id>/knowledge.md` | Accumulated insights per problem |
| `proofs/Proofs/*.lean` | Proof files |

---

## Example: REVISIT Session

```
> /research

Checking available problems...
Pool empty. Entering REVISIT mode.

Selecting blocked problem...
- szemeredi-theorem [surveyed] - Last touched 2025-01-15
- rh-consequences [surveyed] - Has related completed proofs
- bounded-prime-gaps [skipped] - Blocked on sieve theory

Selected: szemeredi-theorem (surveyed, may have new Mathlib support)

Reading history...
- Previous work: Defined AP, density, stated theorem as axiom
- Block reason: "Hypergraph regularity not in Mathlib"
- Knowledge base: 3 previous insights

Literature search...
- Searching "Szemerédi theorem Lean Mathlib 2025"...
- Found: New Mathlib.Combinatorics.Additive module (Dec 2024)
- Found: arXiv paper on "container method" simplification

New approach: Container Method
- Uses probabilistic argument, may avoid regularity lemma
- Mathlib has probability foundations
- Worth attempting!

Attempting proof sketch...
- Created proofs/Proofs/SzemerediContainer.lean
- Defined container lemma statement
- Proved connection to AP density
- Blocked at: probabilistic counting argument (needs Mathlib.Probability)

Updating knowledge base...

## Research Iteration Complete

**Mode**: REVISIT
**Problem**: szemeredi-theorem
**Prior Status**: surveyed

### What I Did
1. Searched for recent Mathlib additions
2. Found container method as alternative approach
3. Created new proof file with container-based attempt
4. Proved 2 new connecting lemmas

### Outcome
Partial progress. New approach identified. Blocked on probability infrastructure.

### Key Findings
- Container method may be more tractable than regularity lemma
- Mathlib.Combinatorics.Additive has new useful lemmas
- Need Mathlib.Probability.ProbabilityMassFunction for counting

### Files Modified
- proofs/Proofs/SzemerediContainer.lean (new)
- research/problems/szemeredi-theorem/knowledge.md (updated)

### Next Steps
- Check if probabilistic argument can be made deterministic
- Look for "finitary" versions of container lemma

### Pool Status
- Available: 0
- Surveyed: 3 (including this one, still surveyed but with progress)
- Skipped: 7
```
