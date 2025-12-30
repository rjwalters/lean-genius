# Research State Machine

This document defines the states a research problem moves through and the transitions between them.

## Problem States

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         RESEARCH STATE MACHINE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   ┌──────────┐                                                               │
│   │   NEW    │  Problem identified, not yet initialized                      │
│   └────┬─────┘                                                               │
│        │ init_problem()                                                      │
│        ▼                                                                     │
│   ┌──────────┐                                                               │
│   │ OBSERVE  │  Reading state, understanding problem                         │
│   └────┬─────┘                                                               │
│        │ state_understood()                                                  │
│        ▼                                                                     │
│   ┌──────────┐                                                               │
│   │  ORIENT  │  Exploring literature, finding techniques                     │
│   └────┬─────┘                                                               │
│        │ exploration_complete()                                              │
│        ▼                                                                     │
│   ┌──────────┐                                                               │
│   │  DECIDE  │  Generating hypotheses, ranking approaches                    │
│   └────┬─────┘                                                               │
│        │ approach_selected()                                                 │
│        ▼                                                                     │
│   ┌──────────┐         failure_documented()                                  │
│   │   ACT    │◄────────────────────────────────────────┐                    │
│   └────┬─────┘                                         │                    │
│        │                                               │                    │
│        ├── attempt_succeeded() ──► [VERIFY]            │                    │
│        │                              │                │                    │
│        │                              ├── verified ──► [BREAKTHROUGH]       │
│        │                              │                                      │
│        │                              └── failed ──────┘                    │
│        │                                                                     │
│        └── attempt_failed() ─────────────────────────► [LEARN]              │
│                                                           │                  │
│                                                           │                  │
│   ┌──────────┐◄───────────────────────────────────────────┘                 │
│   │  LEARN   │  Document failure, extract insights                          │
│   └────┬─────┘                                                               │
│        │                                                                     │
│        ├── more_approaches() ──► back to DECIDE                             │
│        │                                                                     │
│        └── exhausted() ──► [PIVOT]                                          │
│                               │                                              │
│                               └──► back to ORIENT (new direction)           │
│                                                                              │
│   ┌──────────────┐                                                          │
│   │ BREAKTHROUGH │  Potential proof found, needs human review               │
│   └──────────────┘                                                          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## State Definitions

### NEW
- Problem has been identified but workspace not created
- No `problem.md` or `state.md` exists yet
- **Entry**: Problem suggested by user, gallery gap, or proof suggestion
- **Exit**: Run `init_problem()` to create workspace

### OBSERVE
- Agent is reading and understanding the current state
- Reviews: problem statement, previous attempts, knowledge base, related proofs
- **Entry**: Fresh start or returning after pause
- **Exit**: Agent has full context, ready to explore
- **Key files**: `problem.md`, `knowledge.md`, `approaches/*/status.md`

### ORIENT
- Agent is exploring the problem space
- Searches: gallery proofs, literature, techniques, analogies
- **Entry**: Problem understood, seeking directions
- **Exit**: Have identified potential approaches to try
- **Key files**: `literature/`, related gallery proofs

### DECIDE
- Agent is generating and evaluating hypotheses
- Activities: divergent ideation, convergent filtering, approach ranking
- **Entry**: Exploration complete, have raw material
- **Exit**: Selected an approach to attempt
- **Key files**: `approaches/*/hypothesis.md`

### ACT
- Agent is attempting to prove/formalize
- Activities: writing Lean, testing, debugging
- **Entry**: Approach selected, ready to implement
- **Exit**: Attempt succeeded or failed
- **Key files**: `approaches/*/attempts/*.lean`

### VERIFY
- Agent has a potentially working proof
- Activities: adversarial testing, edge case checking, formal verification
- **Entry**: Lean compiles successfully
- **Exit**: Verified (breakthrough) or found flaw (back to ACT)
- **Key files**: `approaches/*/attacks/`

### LEARN
- Agent is documenting what happened
- Activities: post-mortem, insight extraction, knowledge base update
- **Entry**: Attempt completed (success or failure)
- **Exit**: Ready for next approach or pivot
- **Key files**: `approaches/*/post-mortem.md`, `knowledge.md`

### BREAKTHROUGH
- Potential proof discovered, awaiting human review
- Agent has done all verification it can
- **Entry**: Proof survived adversarial testing
- **Exit**: Human confirms (celebration!) or finds issue (back to ACT)
- **Signals**: GitHub label `loom:breakthrough`, notification

### PIVOT
- Current direction exhausted, need new angle
- Return to ORIENT with fresh perspective
- **Entry**: Exhausted approaches in current direction
- **Exit**: New direction identified in ORIENT phase

## State File Format

Each problem has a `state.md` file tracking its current state:

```markdown
# Research State: {problem-slug}

## Current State
**Phase**: OBSERVE | ORIENT | DECIDE | ACT | VERIFY | LEARN | BREAKTHROUGH | PIVOT
**Since**: 2025-01-15T10:30:00Z
**Iteration**: 3

## Current Focus
Brief description of what the agent is working on right now.

## Active Approach
approach-003 (if in ACT/VERIFY phase)

## Attempt Count
- Total attempts: 12
- Current approach attempts: 3
- Approaches tried: 3

## Blockers
Any blockers preventing progress.

## Next Action
What the agent should do next when resuming.
```

## Transition Functions

These are conceptual—implemented by the researcher agent's decision logic:

```
init_problem(problem_id):
  - Create problem workspace
  - Write initial problem.md
  - Write initial state.md with phase=OBSERVE
  - Return: problem ready

state_understood():
  - Verify agent has read all context files
  - Update state.md phase=ORIENT
  - Return: ready to explore

exploration_complete():
  - Verify literature survey exists
  - Verify related proofs identified
  - Update state.md phase=DECIDE
  - Return: ready to ideate

approach_selected(approach_id):
  - Create approach directory
  - Write hypothesis.md
  - Update state.md phase=ACT, active_approach=approach_id
  - Return: ready to attempt

attempt_succeeded():
  - Lean compilation successful
  - Update state.md phase=VERIFY
  - Return: ready for adversarial testing

attempt_failed(reason):
  - Document failure in attempt log
  - Increment attempt count
  - Update state.md phase=LEARN
  - Return: ready for post-mortem

failure_documented():
  - Post-mortem written
  - Knowledge base updated
  - Check if more approaches available
  - Update state.md phase=DECIDE or PIVOT
  - Return: next phase

verified():
  - All adversarial tests passed
  - Update state.md phase=BREAKTHROUGH
  - Add loom:breakthrough label to problem issue
  - Return: awaiting human review
```

## Agent Decision Logic

When a researcher agent starts, it reads `state.md` and decides what to do:

```
function decide_action(state):
  match state.phase:
    OBSERVE:
      - Read problem.md thoroughly
      - Read knowledge.md for prior insights
      - Read all approach post-mortems
      - Check related gallery proofs
      - When: full context acquired → transition to ORIENT

    ORIENT:
      - Search gallery for similar proofs
      - Identify applicable techniques
      - Look for analogies across domains
      - Build literature survey
      - When: have potential directions → transition to DECIDE

    DECIDE:
      - Run divergent ideation (generate many ideas)
      - Run convergent filtering (evaluate feasibility)
      - Rank approaches by promise
      - Select highest-ranked untried approach
      - When: approach selected → transition to ACT

    ACT:
      - Create/open attempt file
      - Write Lean code
      - Try to compile
      - If compiles → transition to VERIFY
      - If fails → analyze error, try fix, or transition to LEARN

    VERIFY:
      - Run adversarial attacks on proof
      - Check edge cases
      - Stress test assumptions
      - If survives → transition to BREAKTHROUGH
      - If fails → transition to ACT with new info

    LEARN:
      - Write post-mortem for failed attempt
      - Extract insights for knowledge base
      - If more approaches available → transition to DECIDE
      - If exhausted → transition to PIVOT

    PIVOT:
      - Clear current direction
      - Return to ORIENT with constraint: "not the previous direction"
      - Fresh exploration with accumulated knowledge

    BREAKTHROUGH:
      - Notify humans
      - Document proof thoroughly
      - Wait for human review
      - Ready to assist with verification
```
