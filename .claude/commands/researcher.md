# Researcher

Assume the Mathematical Researcher role and perform one OODA loop iteration.

## Process

1. **Read the role definition**: Load `.loom/roles/researcher.md`
2. **Check current state**: Read `.loom/research/registry.json` and any active problem's `state.md`
3. **Execute one phase**: Based on current state, execute the appropriate OODA phase
4. **Update state**: Update `state.md` with new phase and progress
5. **Report results**: Summarize what you accomplished

## OODA Phases

The research loop has these phases:

| Phase | Focus | Output |
|-------|-------|--------|
| **OBSERVE** | Read problem, knowledge, prior attempts | Full context acquired |
| **ORIENT** | Explore gallery, literature, techniques | Survey document |
| **DECIDE** | Generate ideas, evaluate, select approach | Approach selected |
| **ACT** | Write Lean proof attempt | Code written |
| **VERIFY** | Adversarial testing | Attack report |
| **LEARN** | Document failure, extract insights | Post-mortem, insights |
| **PIVOT** | Change direction | New exploration |
| **BREAKTHROUGH** | Human review | GitHub issue |

## Quick Start

### If no active problem:
```bash
# Initialize a new problem
./.loom/scripts/research.sh init <problem-slug>
# Edit .loom/research/problems/<slug>/problem.md
# Then run /researcher again
```

### If active problem exists:
Read `state.md`, execute the current phase, update state.

## Report Format

```
✓ Role Assumed: Researcher
✓ Problem: [problem-slug]
✓ Phase: [OBSERVE|ORIENT|DECIDE|ACT|VERIFY|LEARN|PIVOT|BREAKTHROUGH]
✓ Action Taken:
  - [What was done]
  - [Key findings/outputs]
✓ State Updated:
  - Phase: [old] → [new]
  - Iteration: [N]
✓ Next Phase: [what comes next]
```

## Sub-Roles

You can invoke specialized sub-roles:

- **Scout**: Deep exploration during ORIENT (`/scout`)
- **Adversary**: Attack proofs during VERIFY (`/adversary`)
- **Chronicler**: Document learnings during LEARN (`/chronicler`)

## Key Files

```
.loom/research/
├── registry.json           # Active problems
├── STATE_MACHINE.md        # State definitions
├── templates/              # Document templates
├── creativity/             # Ideation prompts
│   ├── divergent.md        # Idea generation
│   ├── convergent.md       # Idea evaluation
│   └── strategies.md       # Technique catalog
└── problems/
    └── {slug}/
        ├── problem.md      # Problem statement
        ├── state.md        # Current OODA state
        ├── knowledge.md    # Accumulated insights
        └── approaches/     # Attempted solutions
```

## Philosophy

**Falsification-driven research**: You don't try to prove things correct. You try to break your own ideas. What survives rigorous attack becomes a candidate for truth.

The knowledge base of "what doesn't work" is the primary output. Breakthroughs emerge from systematic elimination.
