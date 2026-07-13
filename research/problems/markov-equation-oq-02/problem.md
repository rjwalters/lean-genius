# Markov Equation OQ-02 — Mod-3 Arithmetic Structure of Markov Triples

## Scope

The parent gallery entry `markov-equation` (`Proofs/MarkovEquation.lean`)
classifies the positive solutions of `x² + y² + z² = 3xyz` as the Markov tree
rooted at `(1,1,1)`, and `Proofs/MarkovCoprime.lean` proves the triples are
**pairwise coprime** with the prime-2 (parity) consequence "at most one
coordinate is even".

OQ-02 develops the complementary **prime-3** structure, which the geometric
classification does not directly expose:

1. **No coordinate of a Markov triple is divisible by 3.**
2. **Every coordinate is `≡ ±1 (mod 3)`** (its residue squares to `1` in `ZMod 3`).

This is a genuine, classical fact about Markov numbers (the Markov numbers
`1,2,5,13,29,34,89,169,…` are never multiples of `3`) and is distinct from all
existing Markov gallery content (which covers the tree structure, coprimality,
parity, geometric growth, and the Markov–Hurwitz generalizations).

## Resolution

`Proofs/MarkovEquationOQ02.lean` (this session, S1) proves both statements by
the standard residue argument:

- Reduce `x²+y²+z² = 3xyz` modulo `3`. Since `3xyz ≡ 0`, the residues satisfy
  `a²+b²+c² ≡ 0 (mod 3)`.
- A finite `decide` over `ZMod 3` shows that if any one residue is `0` then all
  three are `0`.
- Three coordinates simultaneously divisible by `3` contradicts pairwise
  coprimality (`markov_coprime` from the parent), so none is divisible by `3`.
- A nonzero residue in `ZMod 3` squares to `1`, giving `x ≡ ±1 (mod 3)`.

The argument is the mirror image of the mod-3 obstruction
`three_dvd_all_of_hurwitz_one` (`Proofs/MarkovHurwitzOQ03OQ01.lean`) for the
*unscaled* equation `x²+y²+z² = xyz` (which forces all coordinates divisible by
`3`); the factor `3` on the right of the genuine Markov equation flips the
conclusion.

## Relation to the parent's stated open questions

The parent lists two open questions: the **Markov uniqueness conjecture** and the
**quantitative `(log N)²` tree-growth** estimate — both genuinely hard/analytic
and out of scope here. OQ-02 instead captures an elementary, fully provable
arithmetic invariant that sits alongside the existing coprimality/parity layer.

## References

- A. Markov, *Sur les formes quadratiques binaires indéfinies* (1879–1880).
- Aigner, *Markov's Theorem and 100 Years of the Uniqueness Conjecture* (2013).
