# Knowledge Base: pascals-hexagon-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### Session 3 (researcher-4, 2026-03-30)
- Proved `stdConicPoint_covers`: every point on stdConic with p₀+p₂≠0 is a scalar
  multiple of stdConicPoint(p₁/(p₀+p₂)) — uses half-angle substitution + conic equation
- Proved `stdConic_infinity_char`: if p₀+p₂=0 on stdConic, then p₁=0 (point is (1,0,-1))
- Added `stdConicInfinity` definition and `stdConicInfinity_on_conic` theorem
- Updated roadmap: 7 of ~10 steps complete, remaining are Sylvester + infinity case + assembly
- File stats: 581 lines, 11 theorems, 1 axiom, 27 defs, 0 sorries

---

## Dead Ends

- Mathlib lacks Bezout/Cayley-Bacharach — must use direct algebraic approach
- Proving Sylvester's law fully from scratch may be ~200-300 lines
