# Scout

Search for new knowledge that could unblock a stalled research problem.

## Purpose

The `/scout` skill performs targeted knowledge discovery on blocked or skipped problems. Unlike a full `/research` iteration, this focuses solely on finding new information that might change a problem's tractability.

## When to Use

- Periodically check if blocked problems have become tractable
- After major Mathlib releases (check release notes for relevant additions)
- When you've completed related proofs that might unlock new approaches
- When you have spare context and want to do lightweight research

## Step 1: Select a Problem to Scout

Pick a blocked/skipped problem, prioritizing:

1. **Longest time since last scout** - Fresh eyes on stale problems
2. **High significance** - Worth investing in S-tier and A-tier problems
3. **Recently related work** - If we just proved something adjacent, scout related blockers

```bash
# List skipped problems with their last update
jq -r '.candidates[] | select(.status == "skipped" or .status == "surveyed") |
  "\(.tier // "B") | \(.id) | \(.name) | Last: \(.lastScouted // "never")"' \
  research/candidate-pool.json | sort
```

Save the selected problem ID:
```bash
PROBLEM_ID="<selected-problem>"
```

## Step 2: Read Current Blockers

Understand exactly what's blocking this problem:

```bash
# Read the problem notes
jq -r '.candidates[] | select(.id == "'$PROBLEM_ID'") | .notes' research/candidate-pool.json

# Check for existing knowledge file
cat "research/problems/$PROBLEM_ID/knowledge.md" 2>/dev/null || echo "No knowledge file yet"
```

**Key question**: What specific Mathlib infrastructure or proof technique is missing?

## Step 3: Search for New Knowledge

### 3.1: Mathlib Search

Search for recent Mathlib additions:

```
WebSearch: "Mathlib4 [topic] 2025"
WebSearch: "Mathlib GitHub PR [missing infrastructure]"
WebSearch: "leanprover-community [topic] merged"
```

Check Mathlib docs directly:
```
WebFetch: https://leanprover-community.github.io/mathlib4_docs/
```

### 3.2: Literature Search

Search for new proof approaches:

```
WebSearch: "[theorem name] elementary proof"
WebSearch: "[theorem name] formalization Lean Coq Isabelle"
WebSearch: "arXiv [topic] 2024 2025"
WebSearch: "[theorem name] simplified proof"
```

### 3.3: Related Work in Our Gallery

Check if we've added related proofs since the problem was blocked:

```bash
# List recent proofs
git log --oneline --since="2024-01-01" -- proofs/Proofs/*.lean | head -20

# Search for related keywords
grep -l "[relevant-keyword]" proofs/Proofs/*.lean
```

## Step 4: Document Findings

Create or update the knowledge file:

```bash
# Ensure problem directory exists
mkdir -p "research/problems/$PROBLEM_ID"

# Add scouting session to knowledge.md
```

Add a session entry:

```markdown
## Scout Session: [DATE]

### Search Queries
- [query 1]: [what was found]
- [query 2]: [what was found]

### Mathlib Changes
- [New relevant theorems/definitions found, if any]
- [Or: "No relevant changes found"]

### Literature Findings
- [New papers or approaches discovered]
- [Or: "No new approaches found"]

### Related Gallery Proofs
- [Our proofs that might help, if any]

### Assessment
**Blocker Status**: [UNCHANGED | PARTIALLY RESOLVED | RESOLVED]
**Reasoning**: [Why the status hasn't changed, or what new opportunity exists]

### Recommendation
- [ ] Keep blocked - blocker still exists
- [ ] Move to available - can now attempt proof
- [ ] Move to surveyed - can do preliminary work
- [ ] Schedule deep dive - promising but needs investigation
```

## Step 5: Update Pool Status

If scouting revealed new opportunities:

```bash
# Update lastScouted timestamp
jq '(.candidates[] | select(.id == "'$PROBLEM_ID'")).lastScouted = "'$(date -Iseconds)'"' \
  research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json

# If blocker resolved, update status
jq '(.candidates[] | select(.id == "'$PROBLEM_ID'")).status = "available"' \
  research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json
```

## Step 6: Report

```markdown
## Scout Report: [PROBLEM_ID]

**Problem**: [name]
**Prior Status**: [skipped/surveyed]
**Tier**: [S/A/B/C]

### Original Blocker
[What was blocking this problem]

### Search Summary
- Mathlib searches: [N queries]
- Literature searches: [N queries]
- Related proofs checked: [N files]

### Key Findings
1. [Most important finding]
2. [Second finding]
3. [Third finding]

### Blocker Assessment
**Status**: UNCHANGED | WEAKENED | RESOLVED
**Confidence**: LOW | MEDIUM | HIGH

### Recommendation
[What should happen next with this problem]

### Next Scout
Suggest re-scouting in: [1 week | 1 month | after Mathlib X release | never]
```

## Scouting Strategy for Millennium Problems

For S-tier problems (Millennium Prize), use a more thorough approach:

### Riemann Hypothesis
- Search: "Mathlib zeta function", "Mathlib complex analysis", "Mathlib prime counting"
- Key blocker: L-functions and analytic continuation not in Mathlib

### P vs NP
- Search: "Mathlib computational complexity", "Mathlib Turing machines"
- Key blocker: Computational complexity framework not in Mathlib

### Birch and Swinnerton-Dyer
- Search: "Mathlib elliptic curves", "Mathlib L-functions", "Mathlib BSD"
- Key blocker: L-functions attached to elliptic curves not in Mathlib

### Hodge Conjecture
- Search: "Mathlib algebraic cycles", "Mathlib Hodge theory"
- Key blocker: Advanced algebraic geometry not in Mathlib

### Yang-Mills
- Search: "Mathlib gauge theory", "Mathlib quantum field theory"
- Key blocker: QFT foundations not in Mathlib

### Navier-Stokes
- Search: "Mathlib Navier-Stokes", "Mathlib fluid dynamics", "Mathlib PDE"
- Key blocker: 3D existence/regularity requires heavy analysis not in Mathlib

### Poincare (Solved!)
- This is actually provable since Perelman solved it
- Search: "Mathlib manifolds", "Mathlib Ricci flow"
- Key blocker: Ricci flow with surgery not in Mathlib

## Quick Scout (5 minutes)

For a fast check on a single problem:

```bash
PROBLEM_ID="riemann-hypothesis"

# 1. Read blocker
jq -r '.candidates[] | select(.id == "'$PROBLEM_ID'") | .notes' research/candidate-pool.json

# 2. Quick Mathlib search
# WebSearch: "Mathlib4 zeta function 2025"

# 3. Update scout timestamp
jq '(.candidates[] | select(.id == "'$PROBLEM_ID'")).lastScouted = "'$(date -Iseconds)'"' \
  research/candidate-pool.json > tmp.json && mv tmp.json research/candidate-pool.json

echo "Quick scout complete. Blocker status: [UNCHANGED|CHANGED]"
```
