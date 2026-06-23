# Knowledge Base: erdos-1155-oq-01

Triangle removal process exact asymptotics f(n) = Θ(n^{3/2}).

---

## Problem Understanding

Erdős Problem #1155: Start with K_n, repeatedly remove random triangle (all 3 edges) until triangle-free. Let f(n) = remaining edges. Is E[f(n)] ≍ n^{3/2}?

Known: BFL (2015) proved f(n) = n^{3/2+o(1)} a.s. The gap to Θ(n^{3/2}) is open.

---

## Session 2026-03-11 (Session 1) - Survey

**Mode**: FRESH
**Outcome**: surveyed

### What I Did
- Read Erdos1155Problem.lean (5 axioms, 4 proved theorems, 2 sorries)
- Read Erdos1155OQ01.lean (6 axioms, 18 proved theorems, 0 sorries)
- OQ01 already proves the parent sorries (triangleFree_iff_cliqueFree3, complete_has_triangles)
- Comprehensive formalization: hierarchy, ratio characterization, sufficient conditions, exponent tightness

### Key Findings
- File is at full survey quality: 0 sorries, 18 proved theorems
- 6 axioms encode known published results (BFL bounds, Mantel theorem, process properties)
- The open conjecture f(n) = Θ(n^{3/2}) is genuinely open — no further formalization progress possible
- Parent file's `trivial_upper_bound` sorry could be proved from `triangleRemoval_mantel_bound` but is redundant

### Next Steps
- No further work needed unless new mathematical results appear
- Problem is survey-complete

---

## Insights

- The gap between BFL and the conjecture is precisely: n^{-ε} ≤ f/n^{3/2} ≤ n^ε vs c ≤ f/n^{3/2} ≤ C
- limit_implies_conjecture: if f(n)/n^{3/2} → L > 0, full conjecture follows
- limsup_liminf_implies_conjecture: bounded ratio suffices

---

## Dead Ends

- The open conjecture is not provable from current knowledge
