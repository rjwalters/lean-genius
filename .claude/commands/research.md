# Research

You are a Lean theorem proving researcher. Run one research iteration on the lean-genius proof gallery.

## Core Philosophy: Meaningful Progress Only

**Every research session must make MEANINGFUL progress toward a complete proof.** This means:
- Work that brings us closer to proving the actual theorem
- New mathematical insights or approaches
- Identifying and documenting fundamental blockers

**What is NOT progress:**
- Enumerating more cases when enumeration cannot complete the proof
- Adding lines of code without mathematical substance
- Repeating approaches that have already failed
- "Busywork" that feels productive but doesn't advance the goal

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

## Step 0.5: CRITICAL VALUE CHECK (MANDATORY)

**STOP. Before doing ANY work, you MUST answer these questions honestly.**

### The Key Question

> "If I complete this work, will I be meaningfully closer to a complete proof?"

If the answer is "no, but it's still technically progress" — **IT IS NOT PROGRESS. STOP.**

### For FRESH Problems

1. **Is there a tractable path to completion?**
   - What proof technique would we use?
   - Does Mathlib have the required infrastructure?
   - If it requires circle method, L-functions, regularity lemmas, or other major machinery not in Mathlib → mark as `blocked`, not `available`

2. **Can we actually prove something, or just state it?**
   - Stating definitions and axioms = `surveyed`
   - Proving the theorem or meaningful lemmas toward it = `in-progress`

### For REVISIT Problems

1. **Why did this problem stall?** Read the actual blocker from knowledge.md.

2. **Has that blocker been removed?**
   - Search for new Mathlib PRs that add the missing infrastructure
   - Check if new proof techniques have emerged
   - If the blocker still exists → **STOP. Pick a different problem.**

3. **Is the proposed work different from what's been tried?**
   - "More of the same" is NOT a valid approach
   - If previous sessions enumerated cases, DO NOT enumerate more cases
   - You must identify what's ACTUALLY DIFFERENT this time

### Anti-Patterns (NEVER DO THESE)

| Anti-Pattern | Example | Why It's Wrong |
|--------------|---------|----------------|
| **Enumeration Theater** | Extending Goldbach from n≤201 to n≤301 | Enumeration cannot complete an infinite proof |
| **Busywork Progress** | Adding 50 more test cases | Lines of code ≠ mathematical progress |
| **Repeating Failed Approaches** | "Let's try circle method" when it's not in Mathlib | Same blockers = same failure |
| **Incremental Futility** | n≤201 → n≤301 → n≤401... | You need n≤∞, this will never complete |
| **Infrastructure Denial** | Working on problem that needs L-functions | Mathlib doesn't have L-functions, this is blocked |

### If You Fail the Value Check

If the problem fails the value check:
1. Update its status to `blocked` with clear documentation of WHY
2. Document what Mathlib infrastructure would be needed
3. Pick a DIFFERENT problem
4. Do NOT proceed with busywork

---

## Step 0.6: PROOF STRATEGY CHECK (For Theorem Proving)

**Before writing ANY code, you must articulate the proof strategy.**

### The Key Distinction

When we say "prove X for all n", we mean:
> Find mathematical structure that covers infinite cases simultaneously

We do NOT mean:
> Check cases one by one until we get tired

### Required: Identify Your Proof Technique

| Technique | How It Covers All Cases | Example |
|-----------|------------------------|---------|
| **Induction** | Base case + step → all n | Prove P(0), prove P(n)→P(n+1) |
| **Strong Induction** | All smaller cases → current case | P(0..n-1) → P(n) |
| **Case Partition** | Finite classes, prove each | Odd vs even, then handle each |
| **Reduction** | Reduce to solved problem | Show X follows from Y |
| **Contradiction** | Assume ¬X, derive false | Assume no solution, find contradiction |
| **Construction** | Build witness with property | Construct object satisfying spec |

### Enumeration Check

If your strategy involves checking individual cases:

1. **Is the set FINITE?** If infinite → enumeration cannot work
2. **Is it SMALL (< 20 cases)?** If large → seek structure instead
3. **Is there truly no pattern?** Usually there is structure to exploit

**If you're about to enumerate an infinite set: STOP. This approach will never complete.**

### Infinite Domain Problems

For theorems like "for all n > 5" or "for all primes p":

**REQUIRED**: Explain how you'll cover infinitely many cases.

Valid answers:
- "Induction on n with base case 7 and step n→n+2"
- "Reduce to finite check via modular arithmetic"
- "Cases partition into 3 classes by residue mod 3"

Invalid answers:
- "Verify n=7, 9, 11, ... and keep going"
- "Extend to n ≤ 1000" (still infinite cases after)
- "Add more examples" (doesn't generalize)

---

## Step 0.7: RABBIT HOLE DETECTION

**Check periodically: Am I in a rabbit hole?**

### Warning Signs

You may be rabbit-holing if:

| Sign | Example | What It Means |
|------|---------|---------------|
| **Mechanical repetition** | Copy-paste with different numbers | You're not thinking, just grinding |
| **No new insights** | Last 5 cases taught you nothing new | Marginal value → 0 |
| **Infinite horizon** | Could continue this forever | Approach doesn't converge |
| **Avoiding the hard part** | Doing easy stuff while real blocker remains | Procrastination via busywork |
| **Volume over insight** | "I added 50 cases!" | Quantity ≠ quality |

### The Marginal Value Test

Before extending work, ask:

1. **What did case N teach us?** [specific insight]
2. **What would case N+1 teach us?** [specific insight]
3. **If the answer is "same as N"** → you have enough examples

After ~5 examples of a pattern, additional examples have near-zero marginal value.

### Recovery Protocol

If you detect a rabbit hole:

1. **STOP immediately** - don't "just finish this bit"
2. **State the actual goal** - what are we really trying to achieve?
3. **Identify the real blocker** - what's actually preventing progress?
4. **Assess tractability** - is this achievable with current tools?
5. **Pivot or mark blocked** - either find new approach or acknowledge impasse

---

## Step 0.8: STRUCTURE OVER VOLUME

**Mathematical progress comes from finding structure, not accumulating volume.**

### Value Hierarchy

From MOST to LEAST valuable:

1. **Structural theorem** - "Binary Goldbach ⟹ Weak Goldbach"
   - One reduction > 1000 verified cases

2. **Decidable instance** - "Decidable (IsSumOfThreePrimes n)"
   - Subsumes ALL future case verification

3. **Lemma on critical path** - proves part of main theorem
   - Actual progress toward goal

4. **A few examples** - demonstrates approach works
   - 3-5 examples sufficient for any pattern

5. **Many examples** - ❌ ZERO additional value
   - If you have 5 examples, 50 more teaches nothing

### Before Adding More Examples

Ask: "Do I already have a decidable instance or structural theorem?"
- If YES → more examples are worthless
- If NO → build the instance/theorem instead of enumerating

---

## Mode 1: FRESH (Available Problems Exist)

### Step 1.1: Claim a Problem (ATOMIC LOCK REQUIRED)

**CRITICAL: You MUST acquire an atomic lock before working on any problem.**

Multiple agents may be running `/research` simultaneously. To prevent duplicate work:

```bash
# Step 1: Clean stale locks (> 2 hours old)
find research/claims -name "*.lock" -type d -mmin +120 -exec rm -rf {} \; 2>/dev/null || true

# Step 2: List available problems
AVAILABLE=$(jq -r '.candidates[] | select(.status == "available") | .id' research/candidate-pool.json)

# Step 3: Attempt to claim each available problem atomically
CLAIMED=""
for PROBLEM_ID in $AVAILABLE; do
  CLAIM_DIR="research/claims/${PROBLEM_ID}.lock"

  # mkdir is POSIX-atomic: either succeeds (you got it) or fails (someone else has it)
  if mkdir "$CLAIM_DIR" 2>/dev/null; then
    # SUCCESS - we own this problem
    echo "$$" > "$CLAIM_DIR/pid"
    date -Iseconds > "$CLAIM_DIR/timestamp"
    echo "Claimed: $PROBLEM_ID"
    CLAIMED="$PROBLEM_ID"
    break
  else
    echo "Already claimed by another agent: $PROBLEM_ID"
  fi
done

if [ -z "$CLAIMED" ]; then
  echo "No available problems could be claimed - entering REVISIT mode"
  # Proceed to Mode 2: REVISIT
fi
```

**Why `mkdir`?** It's POSIX-atomic. There's no race window between "check if exists" and "create" - it's a single operation that either succeeds or fails.

**When done with the problem:** Release the lock:
```bash
rm -rf "research/claims/${PROBLEM_ID}.lock"
```

Save the problem ID in `PROBLEM_ID`.

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

| Decision | Criteria | Status | Action |
|----------|----------|--------|--------|
| **DEEP DIVE** | Tractable path to complete proof exists | `in-progress` | Create full proof file, work toward completion |
| **SURVEY** | Can define/state but proof requires unavailable infrastructure | `surveyed` | Create stub with definitions, axioms, document blockers |
| **BLOCKED** | Requires major Mathlib infrastructure (circle method, L-functions, etc.) | `blocked` | Document specific blockers, do NOT attempt work |
| **SKIP** | Not worth pursuing (too hard, not interesting, wrong approach) | `skipped` | Update notes explaining why |

**Critical**: `blocked` means "we cannot make progress until Mathlib changes." Do NOT confuse with `in-progress`.

### Step 1.4: Implement, Update Pool, and Release Lock

After implementing, update the problem status in `research/candidate-pool.json`:

```bash
# Update status using jq (replace <problem-id> and <new-status>)
jq '(.candidates[] | select(.id == "<problem-id>")).status = "<completed|surveyed|skipped>"' research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json
```

Also update the `notes` field with what was learned.

**IMPORTANT: Release the lock when done:**
```bash
rm -rf "research/claims/${PROBLEM_ID}.lock"
```

This allows other agents to claim the problem if it needs more work (e.g., status changed to `surveyed` or `in-progress`).

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

### Step 2.5: Attempt Something MEANINGFUL

**You must try something that advances the proof.** But first, re-check the value gate:

> "Will this work bring me closer to a complete proof, or is it busywork?"

**Valid options:**
1. **Prove a new lemma** that's on the critical path to the main theorem
2. **Reduce to a simpler problem** that's tractable with current Mathlib
3. **Find an alternative proof approach** that avoids the current blockers
4. **Identify the minimal Mathlib addition** needed to unblock progress
5. **Build infrastructure** (decidable instance, structural theorem) that subsumes many cases

**INVALID options (do NOT do these):**
- Enumerate more cases when enumeration won't complete the proof
- Add more "verified examples" of something already demonstrated
- Repeat the same approach that failed before
- Write code that doesn't advance mathematical understanding
- Extend from n≤k to n≤k+50 when you need n≤∞

**The "More Examples" Trap:**
If previous sessions added examples, and you're about to add more examples:
- **STOP.** This is almost certainly the wrong move.
- Ask: "Do we already have enough examples to demonstrate the pattern?"
- Ask: "Would a decidable instance or structural theorem be more valuable?"
- If you have 5+ examples, more examples have ZERO marginal value.

**If no valid option exists:** The problem is `blocked` or `completed`. Update its status and move on.

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

### FRESH Mode Coordination
- **Atomic directory locks** (`research/claims/<problem-id>.lock/`) prevent duplicate claims
- `mkdir` is POSIX-atomic: no race condition between check and create
- Stale locks (> 2 hours) are automatically cleaned
- Lock is released when work is complete

### REVISIT Mode Coordination
- Note the session start time in `knowledge.md` before beginning work
- Check `knowledge.md` timestamps - if another session started recently, pick a different problem
- Multiple agents can work on different aspects of the same problem if coordinated via knowledge.md

---

## Files Reference

| File | Purpose |
|------|---------|
| `research/candidate-pool.json` | Problem registry with status |
| `research/claims/<id>.lock/` | Atomic locks (directories, not files) |
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
