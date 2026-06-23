# Feasibility Reconnaissance

**Do this BEFORE committing to a problem.**

## Quick Feasibility Protocol (15-30 min)

### Step 1: Mathlib Search

```bash
# Search for key terms in Mathlib
cd proofs && grep -r "keyword" ~/.elan/toolchains/*/lib/lean4/library/

# Or search Mathlib docs online
# https://leanprover-community.github.io/mathlib4_docs/
```

### Step 2: Prerequisite Mapping

| Required Concept | In Mathlib? | How Hard to Add? |
|-----------------|-------------|------------------|
| Concept A | Yes/No/Partial | Easy/Medium/Hard/Research |
| Concept B | ... | ... |

### Step 3: Milestone Tractability

Score each milestone separately:

| Milestone | Tractability | Time Estimate | Value |
|-----------|--------------|---------------|-------|
| Formal statement | ?/10 | ? hours | Low |
| Small cases (n ≤ 100) | ?/10 | ? hours | Low |
| Infinite family | ?/10 | ? days | Medium |
| Key lemma | ?/10 | ? days | High |
| Full proof | ?/10 | ? weeks/months | Complete |

### Step 4: Decision Matrix

| If... | Then... |
|-------|---------|
| No milestone is tractable (all < 3/10) | SKIP - choose different problem |
| Only trivial milestones tractable | SURVEY MODE - quick pass, document gaps |
| Medium milestone tractable (≥ 5/10) | DEEP DIVE - commit to real progress |
| High milestone tractable | PRIORITY - this is a good target |

### Step 5: Mode Selection

- **SURVEY**: 1-2 hours, formal statement + gaps documented, move on
- **DEEP DIVE**: Half day+, aim for Tier 3+ progress (infinite family)
- **SKIP**: Problem not tractable now, add to "future" list

## Progress Tiers

| Tier | Description | Value |
|------|-------------|-------|
| 1 | Formal statement only | Minimal |
| 2 | Small cases / examples | Low |
| 3 | Infinite family proven | **Medium - Real Progress** |
| 4 | Key lemma toward full proof | High |
| 5 | Full proof | Complete |

**Aim for Tier 3+ on deep dives. Tier 2 is acceptable for surveys.**

## Barrier Categories

When you can't progress further, categorize why:

| Barrier | Example | Remediation |
|---------|---------|-------------|
| **Mathlib Gap** | Circle method missing | Wait for Mathlib development |
| **Technique Gap** | Don't know the math | Study literature |
| **Computational** | Need to check 10^18 cases | Different approach needed |
| **Fundamental** | Problem is actually open | Celebrate partial progress |
