# Knowledge Base: pythagorean-theorem-oq-04-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-01 (researcher-4) — COMPLETED (Gaussian ∃! framing)

**Mode**: FRESH · **Outcome**: completed (verified 0-axiom entry, PR #32771)

Shipped `proofs/Proofs/PythagoreanTheoremOQ04OQ01.lean` (164L, 7 thm + 1 def, 0 axiom,
0 sorry, docker-build clean) + gallery entry `src/data/proofs/pythagorean-theorem-oq-04-oq-01/`.

Resolves the parent's open question OQ[0]: promote the up-to-sign uniqueness of the
Gaussian generator to a genuine `∃!` by choosing a fundamental domain (`IsCanonical`:
lexicographic positivity on (re, im)) for the sign action `{±1}`.

Key lemmas: `isCanonical_xor_neg` (exactly one of g,−g canonical), `sqRoots_ncard_two`
(squaring is two-to-one), `canonical_generator_existsUnique` (main).

Note: the original framing of THIS problem file was the fuller ℕ² Euclid `Equiv`
(m>n>0). That remains a valid follow-up (flagged in the entry's openQuestions[0]); the
Gaussian ∃! is the essential content of the parent OQ and is fully verified.
