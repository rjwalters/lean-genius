# Research

Run one complete iteration of the autonomous mathematical research loop.

## The Full Loop

This command orchestrates the complete research cycle:

```
┌─────────────────────────────────────────────────────────────┐
│                 AUTONOMOUS RESEARCH LOOP                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│   1. CHECK STATE                                             │
│      └── Any active research problems?                       │
│                                                              │
│   2. IF NO ACTIVE PROBLEM                                    │
│      ├── Refresh problem registry                            │
│      ├── Select tractable problem (Seeker)                   │
│      └── Initialize workspace                                │
│                                                              │
│   3. IF ACTIVE PROBLEM                                       │
│      ├── Read current OODA phase                             │
│      ├── Execute phase (Researcher)                          │
│      └── Update state                                        │
│                                                              │
│   4. REPORT                                                  │
│      └── What was accomplished, next steps                   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## Process

### Step 1: Check State

```bash
# Check for active research
./.loom/scripts/research.sh status

# If active, read the state
cat .loom/research/problems/{slug}/state.md
```

### Step 2: Select Problem (if needed)

If no active problem:
```bash
# Refresh registry
npx tsx .loom/scripts/extract-problems.ts --json

# Select tractable problem
# (Apply selection algorithm from seeker.md)

# Initialize
./.loom/scripts/research.sh init <slug>
```

### Step 3: Execute OODA Phase

Based on current phase in `state.md`:

| Phase | Action |
|-------|--------|
| OBSERVE | Read problem, knowledge, prior attempts |
| ORIENT | Explore gallery, literature, techniques |
| DECIDE | Generate ideas, evaluate, select approach |
| ACT | Write Lean proof attempt |
| VERIFY | Attack the proof |
| LEARN | Document failure, extract insights |
| PIVOT | Change direction, return to ORIENT |
| BREAKTHROUGH | Document, create GitHub issue |

### Step 4: Report

```
✓ Research Iteration Complete

Problem: [slug]
Phase: [old-phase] → [new-phase]
Iteration: [N]

Action Taken:
- [What was done]

Key Findings:
- [Finding 1]
- [Finding 2]

Next: [What the next iteration should do]
```

## Autonomous Mode

For fully autonomous operation, this command can be run repeatedly:

```
/research  ← selects problem, starts OBSERVE
/research  ← continues with ORIENT
/research  ← continues with DECIDE
/research  ← continues with ACT
...
```

Each invocation advances the research by one phase.

## When to Use Each Command

| Command | Purpose |
|---------|---------|
| `/research` | Full loop: select + execute (use this for autonomous operation) |
| `/seeker` | Only problem selection |
| `/researcher` | Only OODA execution (assumes problem exists) |
| `/scout` | Deep exploration during ORIENT |
| `/adversary` | Attack proofs during VERIFY |
| `/chronicler` | Document learnings during LEARN |

## Example Session

```
> /research
Checking for active research... None found.
Refreshing problem registry... 427 problems.
Selecting problem... sqrt2-irrational-oq-01 (tractable extension)
Initializing workspace... Done.
Executing OBSERVE phase...
✓ Research Iteration Complete
Problem: sqrt2-extensions
Phase: NEW → OBSERVE
Next: Read related proofs, understand problem context

> /research
Problem: sqrt2-extensions
Executing ORIENT phase...
Found 3 related proofs: sqrt2-irrational, sqrt3-irrational, transcendence-of-e
Identified techniques: descent, parity, algebraic number theory
✓ Research Iteration Complete
Phase: OBSERVE → ORIENT
Next: Generate approaches using creativity engine

> /research
...
```

## Philosophy

**The goal is sustained autonomous progress.**

Each `/research` invocation should:
1. Make measurable progress (not just "think about it")
2. Produce durable artifacts (code, documentation, insights)
3. Leave clear state for the next iteration
4. Accumulate knowledge even when proofs fail
