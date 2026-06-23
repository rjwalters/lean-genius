# Roadmap

Inspired by Greg Egan's "Truth Mines" — a vision of mathematics as an explorable, ever-growing landscape.

## Current State (January 2026)

### What's Built

| Component | Status |
|-----------|--------|
| Gallery website | 969 annotated proofs |
| Lean proof library | 999 files |
| Erdős formalizations | 320 problems |
| Enhancement pipeline | Running (5 parallel agents) |
| Aristotle integration | 81 jobs processed |
| Loom orchestration | Installed |
| Docker build system | Working |

### What's Working

- Agents claim problems, enhance formalizations, create PRs
- Aristotle overnight runs prove ~15% of submitted theorems
- Gallery auto-generates from proof files
- Safe Lean builds via Docker memory limits

---

## Phase 1: Complete Erdős Coverage

**Goal**: Formalize all ~536 Erdős problems.

- [ ] Formalize remaining ~216 problems as stubs
- [ ] Enhance stubs with mathematical context
- [ ] Prepare files for Aristotle (no definition sorries)
- [ ] Integrate successful Aristotle proofs

## Phase 2: Reduce Manual Intervention

**Goal**: Agents work with minimal oversight.

- [ ] Auto-integrate Aristotle results on success
- [ ] Auto-rebuild gallery on proof changes
- [ ] Priority scoring for problem selection
- [ ] Health monitoring for agent pipelines

## Phase 3: Improve Discovery

**Goal**: Find new problems and gaps.

- [ ] Track Mathlib coverage gaps
- [ ] Identify shared infrastructure across problems
- [ ] Suggest related problems and reductions
- [ ] Monitor erdosproblems.com for updates

## Phase 4: Community Features

**Goal**: Support multiple contributors.

- [ ] Contribution tracking
- [ ] Public API for problem status
- [ ] Comment threads on proofs
- [ ] Documentation for contributors

## Phase 5: Broader Scope

**Goal**: Beyond Erdős problems.

- [ ] Other open problem collections
- [ ] Mathlib contributions from polished proofs
- [ ] Educational proof paths

---

## Near-term Actions

1. Continue enhancement pipeline
2. Submit ready problems to Aristotle
3. Improve gallery search/filtering
4. Document the workflow for contributors

---

## Design Principles

- **Incremental value**: Partial progress counts (statements, lemmas, bounds)
- **Fail forward**: Failed attempts inform future work
- **Human oversight**: Agents work autonomously, humans approve merges
- **Open by default**: All proofs and attempts publicly available
