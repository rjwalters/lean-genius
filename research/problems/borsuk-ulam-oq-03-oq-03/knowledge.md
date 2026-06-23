# Knowledge Base: borsuk-ulam-oq-03-oq-03

Constructive 2D Borsuk-Ulam via Tucker's Lemma.

---

## Session 2026-03-17 (Session 1) - Survey

**Mode**: FRESH
**Outcome**: surveyed

### Current State
- **2608 lines, 0 sorries, 1 axiom** (tucker_2d_grid)
- Complete proof chain: Tucker axiom -> grid infrastructure -> approximate BU -> exact BU
- The open question "Can BU be proved via Tucker?" is answered: YES
- The remaining axiom (Tucker's 2D lemma on triangulated grid) is equivalent to Brouwer's FPT in 2D

### The Remaining Axiom
tucker_2d_grid: any antipodal labeling of the triangulated grid on [-1,1]^2 has a complementary edge

### Three Approaches to Eliminate the Axiom
1. Path-following / complementary pivoting (~500-1000 lines)
2. Hex theorem reduction (~300 + Hex proof ~300-500 lines)
3. Poincare-Miranda / intersection theory (~300-500 lines)

All are equivalent to Brouwer's FPT in 2D.

### Assessment
- Eliminating the axiom is a BUILD task requiring 500-1000 lines minimum
- Not tractable in a single session
- The open question itself IS answered (Tucker -> BU chain is complete)
