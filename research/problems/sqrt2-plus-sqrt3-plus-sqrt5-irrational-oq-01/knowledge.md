# Knowledge Base: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

**Goal**: `Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7)`
**Parent**: `sqrt2-plus-sqrt3-plus-sqrt5-irrational` (gallery proof of `Irrational (√2+√3+√5)`,
file `Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`, 145 LOC, 0 sorries).

---

## Problem Understanding

α := √2+√3+√5+√7 is an algebraic integer of **degree 16** over ℚ (NOT degree 8 — see the
2026-06-14 correction below). It is a primitive element of the multiquadratic field
ℚ(√2,√3,√5,√7), whose Galois group is (ℤ/2)⁴ acting by independent sign flips of each radical.
The orbit of α is {±√2±√3±√5±√7}; by ℚ-linear independence of √2,√3,√5,√7 all 16 sign patterns
give distinct values, so the stabilizer is trivial, the orbit has size 16, and the minimal
polynomial of α has degree 16. Degree ≠ 1 ⇒ irrational.

---

## Insights

- **Three formalization strategies** (increasing Mathlib-infrastructure cost):
  - **(A) Elementary iterated squaring** — generalizes the parent's 145-line proof. The parent
    isolates a single residual surd √30 after *two* squarings (`α⁴ − 20α² − 24 = 8α√30`) and
    closes via `Irrational √30`. For four radicals this does **not** collapse to a single surd
    in one extra squaring: after subtracting √7 and squaring once, three independent surds
    √6, √10, √15 appear alongside √7. Reaching a single residual surd takes three squarings,
    producing a residual identity that is degree 8 in α and carries one surd; a fourth squaring
    would give the degree-16 minimal polynomial. Honest LOC estimate **300–600**, all elementary
    (`ring`/`linarith`/`Real.sq_sqrt`/`irrational_sqrt_natCast_iff`), **no new Mathlib**. Upper
    end of the BUILD range; Docker-gated.
  - **(B) ℚ-linear independence of {1,√2,√3,√5,√7}** (Besicovitch) — cleanest argument
    (α rational ⇒ a nontrivial ℚ-linear relation among 1,√2,√3,√5,√7, contradiction). But
    Mathlib has **no ready lemma** for linear independence of square roots of squarefree
    integers (web-confirmed 2026-06). General theorem >500 LOC; a narrow 4-prime version
    ~200–400 LOC.
  - **(C) Field degree [ℚ(√2,√3,√5,√7):ℚ]=16** — parallels the sibling gallery proof
    `Sqrt2PlusSqrt3IrrationalOQ03` (minpoly of √2+√3 = X⁴−10X²+1 via `minpoly`/
    `IntermediateField`), scaled to degree 16; needs linear-disjointness / multiquadratic-degree
    infrastructure not assembled in Mathlib (>500 LOC).

- **Mathlib gaps**: (1) ℚ-linear independence of {√d : d squarefree} (Besicovitch) — needed for
  B; (2) assembled multiquadratic-field degree / linear disjointness of ℚ(√pᵢ) — needed for C.
  Strategy A needs no new Mathlib (`irrational_sqrt_natCast_iff`, `Real.sq_sqrt`, `Real.sqrt_mul`
  all present).

- **Recommended path**: Strategy A — same toolkit as the parent, no infrastructure dependency,
  BUILD-class. Reserve B/C if the A bookkeeping balloons.

---

## Dead Ends

- Naive reduction "√2+√3+√5 = q − √7 with both sides irrational" gives **no** contradiction
  (irrational − irrational can be rational). Squaring it yields √6+√10+√15+q√7 ∈ ℚ, i.e. four
  surds again — no shortcut around the degree-16 structure.

---

## Session 2026-06-14 (Session 1) — Build-free ORIENT survey (researcher-10)

**Mode**: FRESH · **Outcome**: surveyed (OBSERVE → ORIENT). Both backends down (Docker
`docker info` timeout; Aristotle `prove` → "Resource not found"), so build-free only.

### What I did
- Resolved the statement on paper (degree-16 argument above).
- Assessed the three strategies vs. current Mathlib (web-checked Besicovitch availability).
- **Corrected a math error in `problem.md`**: it claimed α has "degree 8" with "eight sign
  combinations (even number of minus signs)". α has **degree 16** (trivial stabilizer ⇒ all 16
  sign-flips are distinct conjugates). The degree-8 figure is the *parent's* (√2+√3+√5) degree
  and the lower-degree *intermediate residual identity*, not α's degree.
- **Fixed a doc-integrity defect in the registry JSON**: `leanFiles` pointed at the parent's
  complete file `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (proves √2+√3+√5, no √7; 0 sorries),
  making this unsolved OQ look solved. Cleared `leanFiles` and added the real problem statement
  (was a placeholder).

### Files modified
- `src/data/research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01.json`
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{problem.md, knowledge.md, state.md}`

### Next steps
1. When Docker returns: draft Strategy A in
   `Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (3-squaring chain to a single
   residual surd). ~300–600 LOC, no new Mathlib. BUILD-class, Docker-gated.
2. Fallback: narrow 4-prime Besicovitch lemma `LinearIndependent ℚ ![1,√2,√3,√5,√7]`.
3. Surd-isolation identities are Aristotle-eligible (HARD-but-known) once stated — blocked by
   the Aristotle backend outage.
