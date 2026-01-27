# Mathematical Research System

> *"The Truth Mines were a honeycomb of abstract constructs, a vast, three-dimensional maze of crystallized theorems and conjectures. Every node, every tunnel, every chamber represented a different mathematical truth... The mines were inexhaustible."*
>
> — Greg Egan, *Diaspora*

An agentic framework for autonomous mathematical research on formal proofs.

## Overview

This system implements a systematic, falsification-driven research process for discovering and formalizing mathematical proofs in Lean 4.

**Core Philosophy**: We don't try to prove things correct. We try to break our own ideas. What survives rigorous attack becomes a candidate for truth.

## Fully Autonomous Operation

The system can run completely autonomously:

```bash
# Just say "do research" — the system handles everything
/research
```

This will:
1. Extract open problems from the proof gallery (427+ problems)
2. Select a tractable problem to work on
3. Initialize a research workspace
4. Run one OODA loop iteration
5. Report progress and prepare for next iteration

Repeat `/research` to continue advancing through the loop.

## Quick Start

### Option 1: Fully Autonomous

```bash
/research   # Selects problem, starts OBSERVE
/research   # Continues to ORIENT
/research   # Continues to DECIDE
...         # Keep going until BREAKTHROUGH or PIVOT
```

### Option 2: Manual Problem Selection

```bash
# See all extractable problems
npx tsx .lean/scripts/extract-problems.ts

# Initialize specific problem
./.lean/scripts/research.sh init goldbach-weak

# Edit problem definition
# research/problems/goldbach-weak/problem.md

# Start the OODA loop
/researcher
```

### Option 3: Check Status

```bash
# See all active problems
./.lean/scripts/research.sh status

# See specific problem state
./.lean/scripts/research.sh state goldbach-weak
```

## Problem Sources

Problems are automatically extracted from the proof gallery:

| Source | Count | Description |
|--------|-------|-------------|
| **openQuestions** | ~350 | Extensions suggested by completed proofs |
| **Incomplete** | ~15 | Proofs with `sorry` statements |
| **WIP** | ~6 | Work-in-progress proofs |
| **Conditional** | ~4 | Proofs depending on unproven hypotheses |
| **Millennium** | 7 | Millennium Prize Problems |
| **Hilbert** | 21 | Hilbert's 23 Problems |

**Total**: 427+ extractable open problems

### View Problems by Tractability

```bash
# Tractable (best for autonomous research)
npx tsx .lean/scripts/extract-problems.ts --tractability=tractable

# Challenging
npx tsx .lean/scripts/extract-problems.ts --tractability=challenging

# Export full list
npx tsx .lean/scripts/extract-problems.ts --json
```

## The OODA Loop

Research follows an iterative Observe-Orient-Decide-Act cycle:

```
OBSERVE → ORIENT → DECIDE → ACT → VERIFY → LEARN
    ↑                                    │
    └────────────────────────────────────┘
```

| Phase | Purpose | Output |
|-------|---------|--------|
| **OBSERVE** | Understand current state | Full context |
| **ORIENT** | Explore problem space | Literature survey |
| **DECIDE** | Generate & select approaches | Hypothesis |
| **ACT** | Attempt proof in Lean | Code |
| **VERIFY** | Adversarial testing | Attack report |
| **LEARN** | Document & extract insights | Post-mortem |

## Agent Roles

### Primary Role

**Researcher** (`/researcher`): Drives the main OODA loop. Reads state, decides what phase to execute, performs the work, updates state.

### Supporting Roles

| Role | Purpose | When Used |
|------|---------|-----------|
| **Scout** (`/scout`) | Deep exploration | ORIENT phase |
| **Adversary** (`/adversary`) | Attack proofs | VERIFY phase |
| **Chronicler** (`/chronicler`) | Document learnings | LEARN phase |

## Creativity Engine

The system includes structured ideation tools:

### Divergent Thinking (`research/creativity/divergent.md`)

Generate many ideas using these lenses:
- Analogical transfer
- Constraint relaxation/tightening
- Representation shift
- Decomposition
- Extreme cases
- Negation/contraposition
- Combination
- Wild card brainstorming
- Cross-domain perspective

### Convergent Thinking (`research/creativity/convergent.md`)

Evaluate and rank ideas by:
- Lean feasibility (0-3)
- Novelty (0-3)
- Attack surface (0-3)
- Complexity (0-3)

### Strategy Reference (`research/creativity/strategies.md`)

Catalog of proof techniques with guidance on when and how to apply each.

## Directory Structure

```
research/
├── README.md                 # This file
├── registry.json             # Active/completed problems
├── STATE_MACHINE.md          # State definitions
│
├── templates/                # Document templates
│   ├── problem.md            # Problem statement
│   ├── hypothesis.md         # Approach definition
│   ├── post-mortem.md        # Failure documentation
│   └── insight.md            # Knowledge capture
│
├── creativity/               # Ideation tools
│   ├── divergent.md          # Idea generation
│   ├── convergent.md         # Idea evaluation
│   └── strategies.md         # Technique catalog
│
├── knowledge/                # Cross-problem insights
│   └── techniques.md         # General learnings
│
└── problems/                 # Active research
    └── {problem-slug}/
        ├── problem.md        # Problem statement
        ├── state.md          # Current OODA state
        ├── knowledge.md      # Accumulated insights
        ├── literature/       # Related work
        │   ├── survey.md     # Scout's findings
        │   └── ...
        └── approaches/
            └── approach-{N}/
                ├── hypothesis.md   # The conjecture
                ├── attempts/       # Lean files
                │   ├── attempt-001.lean
                │   └── ...
                ├── attacks/        # Adversarial tests
                │   ├── attack-001.md
                │   └── ...
                └── post-mortem.md  # What we learned
```

## State Machine

Each problem tracks its state in `state.md`:

```markdown
# Research State: {slug}

## Current State
**Phase**: OBSERVE | ORIENT | DECIDE | ACT | VERIFY | LEARN | PIVOT | BREAKTHROUGH
**Since**: 2025-01-15T10:30:00Z
**Iteration**: 3

## Current Focus
[What the agent is working on]

## Active Approach
approach-003 (if in ACT/VERIFY phase)

## Attempt Count
- Total attempts: 12
- Current approach attempts: 3
- Approaches tried: 3
```

See `STATE_MACHINE.md` for full state definitions and transitions.

## Labels

| Label | Meaning |
|-------|---------|
| `loom:research-active` | Problem under investigation |
| `loom:hypothesis` | Approach awaiting testing |
| `loom:breakthrough` | Potential proof, needs review |

## Scripts

```bash
# Initialize new problem
./.lean/scripts/research.sh init <slug>

# Show all problems and their states
./.lean/scripts/research.sh status

# Show specific problem state
./.lean/scripts/research.sh state <slug>

# Create a new approach
./.lean/scripts/research.sh approach <slug> <N>

# List all problems
./.lean/scripts/research.sh list
```

## Knowledge Accumulation

The primary output of research is not proofs—it's **knowledge**.

Every failed attempt should produce:
1. **Post-mortem**: Why it failed
2. **Insights**: What we learned
3. **Implications**: What to try/avoid next

The knowledge base (`knowledge.md`) grows with each attempt, making future research more informed.

## Website Synchronization

Research knowledge is displayed on the website at `leangenius.org/research/<slug>`. To keep the website current:

### Architecture

```
research/problems/<slug>/
├── meta.json         # Source of truth for website data
├── knowledge.md      # Detailed session logs and insights
├── state.md          # Current OODA state
└── ...

src/data/research/problems/<slug>.json  # Website JSON (synced from meta.json)
```

### Workflow

1. **During research**: Update `knowledge.md` with detailed session logs
2. **When ready to publish**: Create/update `meta.json` with structured knowledge
3. **Sync to website**: Run `./scripts/sync-research.sh`

### The meta.json Structure

```json
{
  "slug": "problem-slug",
  "title": "Problem Title",
  "phase": "SURVEY | DEEP_DIVE | PIVOT | BREAKTHROUGH",
  "status": "active | graduated | blocked",
  "knowledge": {
    "progressSummary": "One-line summary of what we've achieved",
    "builtItems": [
      {"name": "theorem_name", "type": "theorem|definition|axiom", "description": "..."}
    ],
    "insights": ["Key insight 1", "Key insight 2"],
    "mathlibGaps": ["What Mathlib is missing"],
    "nextSteps": ["What to do next"]
  },
  "approaches": [...],
  "tags": [...],
  "references": {...}
}
```

### Sync Script

```bash
# Sync all meta.json files to website data
./scripts/sync-research.sh

# Output:
# ✓ Synced: weak-goldbach
# ✓ Synced: rh-consequences
# ○ Skipped (up to date): twin-prime-special
# ⚠ Orphaned (no meta.json source): old-problem.json
```

The script:
- Copies `research/problems/<slug>/meta.json` → `src/data/research/problems/<slug>.json`
- Only syncs files that are newer than the target
- Reports orphaned files in target that don't have a meta.json source

## Integration with Lean-Genius

Research outputs integrate with the main project:
- Successful proofs → Added to `proofs/Proofs/`
- New theorems → Get annotations in `src/data/proofs/`
- Related proofs → Cross-referenced in gallery
- **Research knowledge** → Synced to website via `./scripts/sync-research.sh`

## Best Practices

1. **Follow the loop**: Don't skip phases, each serves a purpose
2. **Document everything**: Future-you will thank present-you
3. **Be honest about failures**: They're the source of learning
4. **Use the creativity engine**: Systematic ideation beats random guessing
5. **Attack your own ideas**: If you can't break it, maybe it's true
6. **Accumulate knowledge**: The knowledge base is the durable output

## Limitations

This system is experimental. Be realistic about:
- **AI creativity limits**: Novel mathematical insight is hard
- **Lean complexity**: Formalization requires deep expertise
- **Time horizons**: Real research takes years, not hours

The system is most useful for:
- Systematic exploration of known techniques
- Exhaustive documentation of attempts
- Finding gaps in existing proofs
- Generating conjectures for human review
