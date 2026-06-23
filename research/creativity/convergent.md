# Convergent Thinking: Idea Evaluation

**Purpose**: Filter, rank, and select the most promising approaches.

**Mindset**: Be ruthless but fair. Most ideas won't work—that's expected. Your job is to find the diamonds.

---

## The Process

### Step 1: Initial Filter

Quickly eliminate obviously non-viable ideas:

**Immediate Disqualifiers**:
- [ ] Already tried and documented in knowledge base
- [ ] Requires Mathlib components that don't exist
- [ ] Contradicts known mathematical facts
- [ ] Complexity far exceeds available resources

Mark these as "FILTERED: [reason]" and set aside.

---

### Step 2: Feasibility Scoring

For each remaining idea, score on these criteria (0-3 each):

#### Criterion 1: Lean Feasibility

*Can this approach be expressed in Lean 4 + Mathlib?*

| Score | Meaning |
|-------|---------|
| 0 | Cannot be formulated in type theory |
| 1 | Requires major Mathlib extensions |
| 2 | Needs some custom definitions but doable |
| 3 | Directly expressible with existing Mathlib |

**Questions to ask**:
- Do the core types exist? (naturals, primes, etc.)
- Are needed theorems in Mathlib?
- Can the proof strategy be expressed tactically?

#### Criterion 2: Novelty

*Is this genuinely different from what we've tried?*

| Score | Meaning |
|-------|---------|
| 0 | Exactly matches a failed approach |
| 1 | Minor variation on failed approach |
| 2 | Significantly different from prior attempts |
| 3 | Completely new direction |

**Questions to ask**:
- Does the knowledge base mention this?
- Does it share failure modes with past attempts?
- Does it use fundamentally different techniques?

#### Criterion 3: Attack Surface

*How vulnerable is this approach to counterexamples?*

| Score | Meaning |
|-------|---------|
| 0 | Obvious counterexample exists |
| 1 | Likely failure modes identified |
| 2 | No obvious failures, but untested |
| 3 | Already survived preliminary analysis |

**Questions to ask**:
- What would falsify this?
- Are there edge cases that clearly break it?
- Does it rely on unverified assumptions?

#### Criterion 4: Complexity

*How much work to test this approach?*

| Score | Meaning |
|-------|---------|
| 0 | Requires major new theory development |
| 1 | Week+ of formalization work |
| 2 | Days of formalization work |
| 3 | Hours of formalization work |

**Questions to ask**:
- How many lemmas are needed?
- How deep is the proof?
- Can we test the core idea quickly?

---

### Step 3: Evaluation Matrix

Fill out for each idea:

```markdown
## Idea Evaluation: [Problem Name]
Date: [DATE]

| # | Idea (brief) | Lean | Novelty | Attack | Complexity | TOTAL |
|---|--------------|------|---------|--------|------------|-------|
| 1 | [description] | 2 | 3 | 2 | 2 | 9 |
| 2 | [description] | 1 | 2 | 1 | 3 | 7 |
| 3 | [description] | 3 | 1 | 2 | 3 | 9 |
...

### Top Candidates (Total >= 8)
1. Idea X (score 10): [why it's promising]
2. Idea Y (score 9): [why it's promising]
3. Idea Z (score 8): [why it's promising]

### Filtered Out
- Idea A: [reason]
- Idea B: [reason]

### For Future Consideration
- Idea C: score 6, might revisit if [condition]
```

---

### Step 4: Deep Evaluation of Top 3

For each top candidate, do a deeper analysis:

#### Proof Sketch

```markdown
## Deep Dive: [Idea Name]

### Proof Outline
1. [Step 1]
2. [Step 2]
3. [Step 3]
...

### Key Lemmas Needed
- Lemma A: [statement] — exists in Mathlib? [yes/no/partial]
- Lemma B: [statement] — exists in Mathlib? [yes/no/partial]

### Technical Obstacles
- [Obstacle 1]: [how to address]
- [Obstacle 2]: [how to address]

### Dependencies
- [What this approach assumes/requires]

### Falsification Test
"If this approach is wrong, we would see..."
- [Specific failure mode to check for]

### Time Estimate
- Quick test (is core idea viable?): [hours]
- Full formalization (if viable): [hours/days]
```

---

### Step 5: Selection Criteria

Choose ONE approach to try next. Consider:

#### Primary Factor: Expected Value

```
Expected Value = P(success) × Value(success) / Cost(attempt)
```

- Higher feasibility scores → higher P(success)
- Novel approaches → higher Value (we learn more)
- Lower complexity → lower Cost

#### Secondary Factors

1. **Quick falsifiability**: Can we know fast if it won't work?
   - Prefer approaches we can test quickly

2. **Learning potential**: Even if it fails, what do we learn?
   - Prefer approaches that teach us something

3. **Momentum**: Does success enable other approaches?
   - Prefer approaches that unlock new directions

#### Tie-Breakers

If two approaches score similarly:
1. Pick the one with faster falsification test
2. Pick the one with higher learning potential
3. Pick the one you haven't tried anything similar to
4. Pick randomly (seriously—avoid analysis paralysis)

---

### Step 6: Selection Output

```markdown
## Approach Selection: [Problem Name]
Date: [DATE]

### Selected Approach
**Idea**: [Name/Description]
**Score**: [N/12]
**Approach ID**: approach-{N}

### Why This One
1. [Reason 1]
2. [Reason 2]
3. [Reason 3]

### What Would Change Our Mind
- If we see [X], this approach is doomed
- If [Y] happens, pivot to Idea Z instead

### Success Criteria
- Minimum: [what counts as progress]
- Target: [what counts as success]

### Abort Criteria
After [N] attempts or [T] hours:
- If no progress, abandon and try next-ranked idea
- Key signal that it's not working: [specific sign]

### Backup Plan
If this approach fails, next in queue:
1. [Idea B]
2. [Idea C]
```

---

## Evaluation Heuristics

### Signs an Idea is Good

- Explains why previous approaches failed
- Uses techniques proven in similar problems
- Has a clear "if this works, we're done" structure
- Can be tested incrementally
- Matches problem structure naturally

### Signs an Idea is Weak

- "Maybe if we're lucky..."
- Requires many unproven lemmas
- Complexity is open-ended
- Similar to something that already failed
- Relies on techniques never used in this domain

### Signs to Investigate Further

- Unusual but has internal logic
- Connects two disparate areas (often fruitful)
- Would explain patterns we've observed
- Expert intuition says "this feels right"

---

## Remember

- **Most ideas won't work** — that's fine, that's expected
- **Speed matters** — don't over-analyze, just pick and try
- **Learn from all attempts** — failed approaches inform future selection
- **Revisit rankings** — after each attempt, re-evaluate remaining ideas
- **Trust the process** — systematic elimination beats random wandering
