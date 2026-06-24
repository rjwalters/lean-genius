# Knowledge Base: pentagonal-number-theorem-oq-01

## Problem Understanding

Gallery entry `pentagonal-number-theorem-oq-01` is **verified/original**, 0-axiom,
39 theorems (`proofs/Proofs/PentagonalNumberTheoremOQ01.lean`, imports Mathlib
only). It characterizes the generalized pentagonal numbers `g(k)=k(3k−1)/2` by the
square-discriminant test (`isGenPent_iff_isSquare`: `m` is generalized pentagonal
iff `24m+1` is a perfect square; explicit root `24·g(k)+1=(6k−1)²`), and machine-
checks both ends of Euler's identity through Mathlib's `Partition.genFun`.

It carries **three open questions**:
1. **Open core** — Franklin's sign-reversing involution
   `∑_{p∈distincts n}(−1)^{#parts} = pentSeriesCoeff(n)`. The genuinely hard
   combinatorial gap; still **OPEN**.
2. Derive Euler's partition recurrence for `p(n)` as a corollary.
3. Extend the square-discriminant viewpoint to higher figurate families.

## Progress

### 2026-06-23 (researcher-1) — answered OQ-03 with a new child entry

Created **`pentagonal-number-theorem-oq-01-oq-03`** (new verified/original entry,
`Proofs/PentagonalNumberTheoremOQ01OQ03.lean`, 18 theorems / 2 defs / 0 sorries /
0 axioms / no native_decide, host-lean verified against Mathlib 4.26.0):

- generalized **heptagonal** numbers `h(k)=k(5k−3)/2` with recognition criterion
  `isGenHept_iff_isSquare` (`m` heptagonal iff `40m+9` is a perfect square;
  converse via `ZMod 10`, mirroring the pentagonal `ZMod 6` argument), explicit
  roots `40·h(k)+9=(10k−3)²`, and the `±k` structural facts;
- the **general s-gonal discriminant identity** `disc_genPolygonal`:
  `8(s−2)·P+(s−4)² = ((2s−4)k−(s−4))²` (pentagonal s=5 and heptagonal s=7 as
  instances) — the unifying square-completion behind all figurate tests.

The **open core (OQ-01, Franklin involution) remains OPEN** — not touched.
Releasing the parent research claim; OQ-03 is shipped as the child entry.
