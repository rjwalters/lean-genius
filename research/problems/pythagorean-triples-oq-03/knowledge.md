# Knowledge Base: pythagorean-triples-oq-03

Rational Circle Parametrization for x² + y² = p (primes p ≡ 1 mod 4).

---

## Status: VERIFIED (0 sorries, 0 axioms)

`proofs/Proofs/PythagoreanTriplesOQ03.lean` now type-checks fully against the
Lean 4.26.0 / Mathlib olean cache. Both previously-deferred sorries are closed.
`#print axioms` on the two capstone theorems reports only the foundational
`propext, Classical.choice, Quot.sound`.

---

## Problem Understanding

For a prime p, study the conic C_p : x² + y² = p over ℚ:
- EXISTENCE: C_p has a rational point ⟺ p ≢ 3 (mod 4).
- PARAMETRIZATION: once a rational base point (a,b) exists, every rational
  point is the stereographic image of a chord slope t through (a,b).

---

## Insights

- **The rational obstruction needs no extra descent.** "p ≡ 3 ⟹ p is not a sum
  of two RATIONAL squares" reduces, by clearing denominators, to the integer
  equation X² + Y² = p·W² (W ≠ 0). Infinite descent on |W| (Nat.strongRecOn)
  then closes it — the same descent that handles the integer case.

- **The mod-p step is short via ZMod.** `ZMod.exists_sq_eq_neg_one_iff`
  (`IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3`) together with the field structure of
  `ZMod p` (from `Fact p.Prime`) gives, in ~10 lines:
  p ≡ 3 (mod 4), p ∣ X² + Y² ⟹ p ∣ X ∧ p ∣ Y. No Gaussian integers required.

- **param_recovers coefficients.** The surjectivity identity, after
  `div_eq_iff` + `field_simp`, closes with `linear_combination (a-x)*hcirc`
  (px) and `linear_combination (b-y)*hcirc` (py). The coefficients are the
  quotient of goal_diff by the circle relation x²+y²-a²-b², found by symbolic
  polynomial division.

---

## Key lemmas (all in PythagoreanTriplesOQ03.lean)

- `param_on_circle`, `param_mem_circle` — stereographic map lands on the circle.
- `param_recovers` — surjectivity / completeness of the parametrization.
- `rational_point_of_not_three_mod_four` — existence via `Nat.Prime.sq_add_sq`.
- `prime_dvd_of_dvd_sq_add_sq` — mod-p obstruction (ZMod field argument).
- `no_int_sol_of_three_mod_four` — infinite descent for X²+Y²=pW².
- `no_rational_point_three_mod_four` — rational obstruction (clear + descend).
- `rational_point_iff` — full existence characterization.

---

## Dead Ends / Notes

- Docker (containerd) backend was down this session; verification used `lean`
  directly with a hand-assembled LEAN_PATH over the prebuilt olean cache
  (build dirs now nest under `.lake/build/lib/lean/`).

## Session 2026-06-28 (Session 2) — GALLERY INTEGRATION

**Mode:** FOLLOW-UP (proof already merged via #30916)
**Outcome:** added missing gallery entry

### What I Did
- The verified proof shipped in #30916 but had NO gallery directory
  (`src/data/proofs/pythagorean-triples-oq-03/` was absent), so it never
  surfaced in the web gallery. Created it:
  - `meta.json` — full overview/sections/conclusion/crossReferences, 13 theorems,
    2 defs, 255 lines, badge `mathlib`, 0 sorries / 0 axioms.
  - `annotations.json` — 9 annotations (header, param def, param-on-circle,
    completeness, easy existence, mod-p obstruction, descent, rational
    obstruction + iff, instances), ranges verified within the 255-line file.
- Validated: `pnpm gallery:check-size` EXIT 0 ("all 4124 entries within caps").
  `pnpm annotations:validate` scans all 4124 proofs and times out (~200s, perf
  limit, not a schema error); both files are valid JSON matching the live
  erdos-307-oq-02-oq-01 schema field-for-field.

### Files Modified
- `src/data/proofs/pythagorean-triples-oq-03/meta.json` (new)
- `src/data/proofs/pythagorean-triples-oq-03/annotations.json` (new)
