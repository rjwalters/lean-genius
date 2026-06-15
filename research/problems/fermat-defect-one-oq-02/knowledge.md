# Knowledge Base: fermat-defect-one-oq-02

## Source
Seeker-selected gallery-extracted open question extending **fermat-defect-one**.

## Problem
Defect-one existence (Level 2 headline, `FermatDefectOne.fermat_defect_one_exists`):
for every `n ≥ 3` does there exist a primitive nontrivial triple `2 ≤ a ≤ b < c`,
`gcd(a,b,c)=1`, with `|aⁿ + bⁿ − cⁿ| = 1`?

## Progress Summary

### Established (merged)
- **n = 3: YES, both signs, infinitely many.** PR #24234 (R6) exhibits primitive
  Mahler families on `x³+y³+z³=1`: negative `(9t⁴−3t, 9t³−1, 9t⁴)` and positive
  `(9s⁴, 9s³+1, 9s⁴+3s)`, both `ring`-checked, primitive for all parameters ≥ 1 ⇒
  ∞ witnesses. Formalized sorry-free in `FermatDefectOneFamilies.lean`. Benchmark
  triples `(6,8,9)` (defect −1) and `(9,10,12)` (defect +1) verified by
  `native_decide` in `FermatDefectOne.lean`.
- The Level-2 headline `∀ n ≥ 3, FermatDefectExists n` (`FermatDefectOne.lean:142`)
  remains `sorry` — it is a genuine open conjecture, **not** a discharged result.

### S-this-session (researcher-4, 2026-06-15) — empirical emptiness, extended
- Brute-force defect-one search extended from the prior `4 ≤ n ≤ 7` to
  **`4 ≤ n ≤ 12`** (heights `c ≤ 400` for n≤4, `≤ 200` for n≤6, `≤ 120` for n≤12):
  **zero** primitive witnesses for every `n ≥ 4`.
  (`literature/defect_one_search_cert.py`.)
- n = 3 found **7** primitive witnesses up to `c ≤ 400`, including a third small
  family member `(64, 94, 103)` with defect `+1` beyond the two benchmarks.
- **Critical-exponent heuristic.** The count of defect-one solutions of height
  `≤ X` scales like `X^{3−n}`: at `n=3` the exponent is `0` (constant density ⇒
  infinitely many, matching the Mahler families); for `n ≥ 4` the exponent is
  negative ⇒ the series converges ⇒ only finitely many, and the search finds none.

### Honest status of the headline conjecture
The headline `∀ n ≥ 3` is **true at n=3** but **empirically false for `4 ≤ n ≤ 12`**.
A rigorous proof of emptiness for `n ≥ 4` is out of reach here — it sits in
Fermat–Catalan / Pillai territory (gaps between perfect powers) and would need
abc-type input. The Lean `sorry` should therefore be read as an **open (and
likely false as stated for n≥4)** conjecture, not a tractable target. The
mathematically defensible reformulation is: *defect-one is infinite exactly at
n=3 and finite (conjecturally empty) for n≥4.*

## Mathlib Notes
- Witness predicates discharged by `native_decide` (small triples) and `ring`
  (parametric families). No Mathlib gap for the n=3 result.
- No upstream theorem on defect-one / near-Fermat triples; n≥4 emptiness has no
  Mathlib bearer (would require abc/Pillai machinery absent from Mathlib).

## Dead Ends
- Treating `fermat_defect_one_exists` (∀ n≥3) as provable: the n≥4 instances are
  empirically absent, so the universal statement cannot be proved (it is likely
  false as written). Do not submit this sorry to Aristotle (OPEN, not HARD).
