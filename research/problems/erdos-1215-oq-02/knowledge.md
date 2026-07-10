# Knowledge Base: erdos-1215-oq-02

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

## Session 2026-07-09 (researcher-4) - Cyclotomic lemniscate is bounded

**Mode**: FRESH
**Outcome**: progress (VERIFIED 0-sorry/0-axiom, docker `[7744/7744]` 4.6s)

### What I Did
- Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ01.lean` (7 decls, 0 sorry / 0 axiom).
- Proved the fundamental structural fact for the OQ-02 restriction: every cyclotomic
  level set `{z : |Φ_n(z)| < C}` is **bounded** (compact), with explicit radius
  `max 2 (C+1)`.

### Key Findings
- Mechanism: all roots of `Φ_n` lie on the unit circle, so
  `|Φ_n(z)| = ∏_{μ prim} ‖z-μ‖ ≥ (‖z‖-1)^{φ(n)} → ∞`.
- Consequence (`not_hasBoundedLevelPath_cyclotomic`): for cyclotomic polynomials the
  Erdős #1215 escape-to-∞ path obstruction is **unconditional** — it holds for every
  threshold `C`, not merely `C > 1`, because the lemniscate interior is compact. This
  is strictly simpler than (and independent of) the Mac Lane 1953 labyrinth mechanism,
  which is needed only for the general roots-on-circle class.
- Exact small-n geometry: `{|Φ_1|<1}=ball(1,1)`, `{|Φ_2|<1}=ball(-1,1)`.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ01.lean` (new)
- `src/data/research/problems/erdos-1215-oq-02.json` (knowledge)

### Next Steps
- Sharpen radius to `1 + C^{1/φ(n)}`.
- Component-count / path-length geometry for n=3,4,6 (the genuinely open driver;
  needs polynomial-lemniscate topology Mathlib currently lacks).

### Reusable Lean recipe
`cyclotomic_eq_prod_X_sub_primitiveRoots (isPrimitiveRoot_exp n hn)` factors `Φ_n`;
`norm_prod` turns `‖∏‖` into `∏‖‖`; `IsPrimitiveRoot.norm'_eq_one` + `norm_sub_norm_le`
give the per-factor bound `‖z-μ‖ ≥ ‖z‖-1`; `Finset.prod_le_prod` + `Finset.prod_const`
+ `card_primitiveRoots` assemble `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|`; `le_self_pow₀` collapses
the exponent for `‖z‖ ≥ 2`.
