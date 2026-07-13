# Knowledge Base: pythagorean-triples-oq-07-oq-01

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

## Session 2026-07-05 (Session 1) — Even Leg Divisible by 4 [COMPLETE]

**Mode**: FRESH
**Outcome**: completed (0 axioms, 0 sorries, verified)

### What I Did
- Formalized the claim "in a primitive Pythagorean triple the even leg is divisible by 4" in `proofs/Proofs/PythagoreanTriplesOQ07OQ01.lean` (133 lines, 6 theorems).
- Built with the Docker wrapper — succeeded first try.
- Created gallery entry `src/data/proofs/pythagorean-triples-oq-07-oq-01/` (meta.json, annotations.json, index.ts).

### Key Findings
- The whole strengthening rides on one residue upgrade: **odd² ≡ 1 (mod 8)** (parent used only mod 4). Proof: (2k+1)² = 4k(k+1)+1 with k(k+1) even.
- With even leg x and y,z odd: x² = z² − y² ≡ 1 − 1 = 0 (mod 8); an even integer with square ≡ 0 mod 8 is divisible by 4.
- The symmetric-triple trick (y x z is Pythagorean whenever x y z is) removes duplicate case work.

### Files Modified
- proofs/Proofs/PythagoreanTriplesOQ07OQ01.lean (new)
- src/data/proofs/pythagorean-triples-oq-07-oq-01/{meta.json,annotations.json,index.ts} (new)

### Next Steps
- Push residue structure further: exactly one leg div by 3, one of {legs,hyp} div by 5 ⇒ 60 ∣ xyz.
- 2-adic valuation packaging v₂(even leg) = 1 + v₂(mn).
