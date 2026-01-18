# Vision: Distributed Mathematical Research Platform

## The Mission

**Systematically formalize and advance every unsolved Erdős problem** through a distributed research platform that pools:

- **Claude Code credits** → Strategic reasoning, proof architecture, insight generation
- **Aristotle API access** → Tactical proof search, tactic grinding, counterexample finding
- **Local compute** → Lean 4 compilation, parallel builds, verification

## Why This Matters

### The Erdős Legacy

Paul Erdős posed over **500 problems** spanning combinatorics, number theory, graph theory, and probability. Many remain unsolved decades later. These aren't just puzzles—they're doorways to deep mathematical truth.

| Category | Count | Examples |
|----------|-------|----------|
| Completely open | ~150 | Erdős #340 (Sidon growth), #44 (unit fractions) |
| Partially solved | ~150 | Weaker bounds proven, special cases verified |
| Solved but not formalized | ~200 | Human proofs exist, no machine verification |

### The Formalization Gap

Even for "solved" problems, formal verification is rare. Formalization:
- **Eliminates ambiguity** in problem statements
- **Machine-verifies** every logical step
- **Creates infrastructure** for future work
- **Enables collaboration** across time and space

### The AI Opportunity

For the first time, we have tools that can meaningfully contribute:
- **LLMs** (Claude) for strategic reasoning and proof architecture
- **Proof assistants** (Aristotle) for tactic search and verification
- **Formal systems** (Lean 4 + Mathlib) as the foundation of truth

## The Platform Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    LEAN GENIUS RESEARCH PLATFORM                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                     PROBLEM REGISTRY                             │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐   │   │
│  │  │Erdős #1 │ │Erdős #2 │ │  ...    │ │Erdős #N │ │Custom   │   │   │
│  │  │ status  │ │ status  │ │         │ │ status  │ │problems │   │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘   │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                │                                        │
│                                ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    RESOURCE POOL                                 │   │
│  │                                                                  │   │
│  │   Claude Credits    Aristotle API     Local Compute              │   │
│  │   ┌──────────┐     ┌──────────┐      ┌──────────┐               │   │
│  │   │ User A   │     │ User A   │      │ User A   │               │   │
│  │   │ User B   │     │ User B   │      │ User B   │               │   │
│  │   │ ...      │     │ ...      │      │ ...      │               │   │
│  │   └──────────┘     └──────────┘      └──────────┘               │   │
│  │        │                │                  │                     │   │
│  │        ▼                ▼                  ▼                     │   │
│  │   Strategic         Tactical           Verification              │   │
│  │   Reasoning         Search             Compilation               │   │
│  │                                                                  │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                │                                        │
│                                ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    RESEARCH ENGINE                               │   │
│  │                                                                  │   │
│  │   OBSERVE → ORIENT → DECIDE → ACT → VERIFY → LEARN              │   │
│  │       ↑                                         │                │   │
│  │       └─────────────────────────────────────────┘                │   │
│  │                                                                  │   │
│  │   • Knowledge accumulation per problem                           │   │
│  │   • Parallel work across contributors                            │   │
│  │   • Automatic progress merging                                   │   │
│  │   • Failed approach documentation                                │   │
│  │                                                                  │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                │                                        │
│                                ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    PROOF GALLERY                                 │   │
│  │                                                                  │   │
│  │   • Completed proofs (machine-verified)                          │   │
│  │   • Partial progress (best known bounds, special cases)          │   │
│  │   • Infrastructure (definitions, lemmas, reductions)             │   │
│  │   • Educational content (problem explanations, history)          │   │
│  │   • Open questions (what's still unknown)                        │   │
│  │                                                                  │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## What We Formalize for Open Problems

Even when a conjecture is **completely open**, there's valuable work:

### 1. The Conjecture Itself
- Precise Lean 4 statement (eliminates ambiguity)
- Alternative equivalent formulations
- Relationship to other conjectures

### 2. Known Partial Results
- "Best known bound is X" → **prove X in Lean**
- "True for n ≤ 100" → **verify with Decidable instances**
- "True for special cases" → **prove those cases**
- "Implies Y" → **prove the implication**

### 3. Infrastructure
- Definitions the full proof would need
- Basic lemmas that any approach requires
- Reductions: "If A then Conjecture"
- Counterexample structures (for attempted disproofs)

### 4. Failed Approaches (Valuable!)
- "Approach X doesn't work because Y"
- "Natural idea Z fails at step W"
- Barriers and obstructions identified

### 5. Computational Verification
- "Verified for all n ≤ 10^6"
- "No counterexample found in range R"
- Decidable instances for exhaustive search

## Example: Erdős #340 (Greedy Sidon Sequence)

**Problem**: Let A = {1,2,4,8,13,21,31,45,...} be the greedy Sidon sequence.
Conjecture: |A ∩ {1,...,N}| >> N^(1/2-ε) for all ε > 0.

**Status**: OPEN (best known: Ω(N^(1/3)))

**What We've Formalized**:
```
INFRASTRUCTURE BUILT:
├── IsSidon definition (sets with distinct pairwise sums)
├── IsSidon.subset (hereditary property)
├── IsSidon.diff_injective (distinct differences lemma)
├── isSidon_empty, isSidon_singleton, isSidon_pair
├── greedySidonSeq (axiomatized sequence)
├── greedySidonSeq_strictMono, greedySidonSeq_isSidon
└── greedySidonCount (counting function)

STATEMENTS FORMALIZED:
├── sidon_lower_bound (max ≥ n(n-1)/2)
├── sidon_upper_bound (Erdős-Turán bound)
├── greedySidon_growth_third (known Ω(N^(1/3)) bound)
└── erdos_340 (the main conjecture)

PROGRESS:
├── Basic lemmas: PROVED
├── Key infrastructure: PROVED
├── Lower/upper bounds: IN PROGRESS
├── N^(1/3) bound: OPEN
└── Main conjecture: OPEN (unsolved in mathematics)
```

## The Contribution Model

### How Users Contribute

1. **Run research sessions**: `/research erdos-340-greedy-sidon`
2. **Donate compute**: Local Lean builds verify proofs
3. **Share API access**: Aristotle jobs run on user's API key
4. **Review and merge**: Human oversight on proof integration

### Progress Tracking

```json
{
  "problem_id": "erdos-340-greedy-sidon",
  "contributions": {
    "sessions": 5,
    "claude_api_calls": 147,
    "aristotle_jobs": [
      {"id": "a17cbbc2-...", "status": "IN_PROGRESS", "percent": 5}
    ],
    "compute_hours": 2.3,
    "lines_of_lean": 220,
    "lemmas_proved": 8,
    "sorries_remaining": 6
  },
  "knowledge": {
    "insights": [
      "Sidon sets have all pairwise differences distinct",
      "Greedy sequence axiomatization avoids computational complexity",
      "Mathlib lacks Sidon infrastructure - needed to build ~60 lines"
    ],
    "failed_approaches": [
      "Direct computation of greedy sequence - too slow"
    ],
    "next_steps": [
      "Complete sidon_lower_bound using diff_injective",
      "Attempt N^(1/3) bound via forbidden differences counting"
    ]
  }
}
```

### Knowledge Merging

When multiple sessions work on the same problem:
1. **Insights accumulate** - new discoveries add to the knowledge base
2. **Approaches are tracked** - avoid duplicating failed attempts
3. **Infrastructure builds up** - later sessions benefit from earlier work
4. **Progress persists** - partial proofs carry forward

## The Erdős Problem Roadmap

### Phase 1: Foundation (Current)
- [x] Research framework operational
- [x] Aristotle MCP integration
- [x] Problem registry structure
- [ ] First 10 Erdős problems formalized
- [ ] Contribution tracking system

### Phase 2: Scale
- [ ] 50 Erdős problems in registry
- [ ] Multi-session progress merging
- [ ] Automated problem scraping from erdosproblems.com
- [ ] Public contribution dashboard

### Phase 3: Community
- [ ] 200+ Erdős problems tracked
- [ ] Multiple contributors per problem
- [ ] Leaderboard of contributions
- [ ] Integration with Mathlib contribution pipeline

### Phase 4: Breakthrough
- [ ] All 536 Erdős problems formalized (statements)
- [ ] Meaningful progress on 50+ open problems
- [ ] First AI-assisted solution to open Erdős problem
- [ ] Research published in mathematical venues

## The Bigger Picture

This isn't just about Erdős problems. It's about demonstrating that:

1. **AI can meaningfully contribute to mathematical research**
2. **Distributed effort can tackle hard problems**
3. **Formal verification scales to research mathematics**
4. **Open collaboration accelerates discovery**

The Erdős problems are our testbed. The methods we develop here apply to:
- Other open problem collections (Millennium, Hilbert, etc.)
- New conjectures as they arise
- Verification of claimed proofs
- Educational formalization

## How to Participate

### As a Researcher
```bash
# Pick up where others left off
/research erdos-340-greedy-sidon

# Start a new problem
/research erdos-44-unit-fractions

# Check overall progress
/research --status
```

### As a Contributor
1. Run research sessions (contributes Claude + local compute)
2. Configure Aristotle API key (contributes proof search)
3. Review and improve proofs (contributes expertise)
4. Document insights (contributes knowledge)

### As a Mathematician
1. Suggest formalization approaches
2. Review proof attempts
3. Identify missing lemmas
4. Connect to existing literature

## The Ecosystem: Building Truth Mines Together

> *"The Truth Mines were a honeycomb of truths, a vast three-dimensional maze of crystallized mathematics..."*
> — Greg Egan, *Diaspora*

We're not alone in this quest. Multiple projects are working to map the landscape of mathematical truth:

### Primary Sources

| Project | Focus | Link |
|---------|-------|------|
| **Erdős Problems** | Canonical database of 500+ Erdős problems | [erdosproblems.com](https://erdosproblems.com) |
| **Mathlib** | Lean 4 mathematical library (1M+ lines) | [github.com/leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) |

### Related Efforts

| Project | Approach | Link |
|---------|----------|------|
| **Erdosproblems-LLM-Hunter** | Tracking LLM solution attempts (informal) | [github.com/mehmetmars7/Erdosproblems-llm-hunter](https://github.com/mehmetmars7/Erdosproblems-llm-hunter) |
| **MathOverflow** | Community-curated open problems | [mathoverflow.net](https://mathoverflow.net) |

### Complementary Approaches

Different projects take different angles:

- **Informal LLM attempts** (Erdosproblems-LLM-Hunter): Tracks which frontier LLMs have attempted which problems, documenting exploratory reasoning without formal verification. Useful for identifying tractable subproblems and common pitfalls.

- **Formal verification** (Lean Genius): Machine-checked proofs in Lean 4. Higher bar for "solved" but produces verified mathematics.

- **Human-driven research** (erdosproblems.com): The canonical source, maintained by mathematicians, tracking the true state of knowledge.

These approaches strengthen each other. Informal attempts suggest proof sketches. Formal verification confirms truth. Human oversight ensures quality.

### Collaboration Philosophy

We view all these efforts as building the same structure—Greg Egan's "Truth Mines"—from different entrances. Every marker left by any explorer makes the territory clearer for those who follow.

If you're working on related efforts, we'd love to collaborate:
- Share problem formalizations
- Cross-reference progress
- Pool insights on common obstacles
- Coordinate on infrastructure (Mathlib contributions, etc.)

## Join the Quest

Every unsolved Erdős problem is a challenge. Every formalized statement is progress. Every failed approach teaches us something.

Together, we can:
- Build the most comprehensive formal mathematical research library
- Advance the frontier of human knowledge
- Demonstrate the power of human-AI collaboration
- Honor Paul Erdős's legacy of open problems

**The problems are waiting. Let's solve them.**

---

*"A mathematician is a device for turning coffee into theorems."* — Paul Erdős

*"An AI is a device for turning compute into conjectures."* — The Lean Genius Project
