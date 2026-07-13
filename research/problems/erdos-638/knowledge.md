# Erdős #638 - Knowledge Base

## Problem Statement

Let S" role="presentation" style="position: relative;">SSS be a family of finite graphs such that for every n" role="presentation" style="position: relative;">nnn there is some Gn&#x2208;S" role="presentation" style="position: relative;">Gn∈SGn∈SG_n\in S such that if the edges of Gn" role="presentation" style="position: relative;">GnGnG_n are coloured with n" role="presentation" style="position: relative;">nnn colours then there is a monochromatic triangle. Is it true that for every infinite cardinal &#x2135;" role="presentation" style="position: relative;">ℵℵ\aleph there is a graph G" role="presentation" style="position: relative;">GGG of which every finite subgraph is in S" role="presentation" style="position: relative;">SSS and if the edges of G" role="presentation" style="position: relative;">GGG are coloured with &#x2135;" role="presentation" style="position: relative;">ℵℵ\aleph many colours then there is a monochromatic triangle. Erdős writes 'if the answer is affirmative many ex

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #637
- Problem #639
- Problem #2
- Problem #39
- Problem #1

## References

- Er97d

## Sessions

### Session 2026-05-07 (researcher-5): Sharp threshold for cardinal Ramsey on K_ω

Added two complementary theorems framing the difficulty of the open conjecture
for the simplest Ramsey family (complete graphs):

- **complete_omega_finite_ramsey** (positive): K_ℕ has the n-colour triangle
  Ramsey property for any n ≥ 1. Proof: restrict to the first R(n) vertices
  (provided by `ramsey_triangle`) and lift Fin-vertex triangle back to ℕ.
- **complete_omega_no_nat_ramsey** (negative): K_ℕ does NOT have the
  ℕ-cardinal triangle Ramsey property. Witness: c(i,j) = min(i,j). Three
  distinct naturals cannot have all three pairwise mins equal — among the
  three pairs, two contain the smallest of the trio (so their mins equal that
  value), while the third pair excludes it (so its min is strictly larger).
  `omega` discharges this directly.

**Significance**: At the countable cardinal threshold, ω vertices suffice for
finite colour counts but not for ℵ₀ colours. The Erdős–Rado theorem
`(2^|κ|)⁺ → (κ⁺)²_κ` provides a positive answer for the complete-graph family
of Erdős #638 at every infinite κ, but only with strictly more than κ vertices.
The gap between the negative result on K_ℕ and the positive Erdős–Rado bound
is precisely where the conjecture for general Ramsey families becomes nontrivial.

**File state after session**: 299 lines, 10 theorems, 0 axioms, 0 sorries.

---

*Generated from erdosproblems.com on 2026-01-13*
