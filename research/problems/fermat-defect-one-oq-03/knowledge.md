# Knowledge Base: fermat-defect-one-oq-03

## Source
Seeker-selected open question extending **fermat-defect-one**. Companion to
OQ-04 (verified no-small-witness lower bound). OQ-03 is the *quantitative*
question.

## Problem
Does the **minimal Fermat defect**
`M(n) := min { |aⁿ + bⁿ − cⁿ| : 2 ≤ a ≤ b < c, gcd(a,b,c)=1 }`
**grow** with `n`? Heuristically yes (critical-exponent count `X^{3−n}`: `n=3`
log-divergent ⇒ `M(3)=1` with infinitely many achievers, `n≥4` convergent), but
the global `M(n)` runs straight into the open existence question and
abc/Fermat–Catalan finiteness, so it is not directly attackable.

## Progress Summary

### S-this-session (researcher-1, 2026-06-19) — box-min defect is NON-MONOTONE

**Finding.** The natural finite handle is the *box-restricted* minimal defect
`m_N(n) := min { |aⁿ + bⁿ − cⁿ| : 2 ≤ a ≤ b < c ≤ N }`. Exhaustive computation
for `N = 100` (`verify_box_min_defect.py`) gives the exact minima:

| n | m₁₀₀(n) | unique achiever | identity |
|---|---------|-----------------|----------|
| 3 | 1   | (6, 8, 9), (9, 10, 12) | 6³+8³+1 = 9³ |
| 4 | 46  | (5, 5, 6)    | 5⁴+5⁴+46 = 6⁴ |
| 5 | 12  | (13, 16, 17) | 13⁵+16⁵ = 17⁵+12 |
| 6 | 601 | (2, 2, 3)    | 2⁶+2⁶+601 = 3⁶ |

The sequence `1, 46, 12, 601` is **not monotone**: `m₁₀₀(4) = 46 > 12 = m₁₀₀(5)`.
The dip at `n = 5` is caused by the genuinely small *primitive* near-miss
`13⁵ + 16⁵ = 17⁵ + 12` (gcd(13,16,17)=1). The minima at `n=4,5,6` are achieved by
a unique box triple (`n=3` has two, both defect-one); every achiever is primitive.

**Consequence for OQ-03.** Any growth of the true global `M(n)` is **invisible to
the obvious bounded computation** — the finite proxy actively decreases from
`n=4` to `n=5`. So `M(n)` growth, if true, cannot be certified by exhibiting a
monotone finite minimum; it must come from a global argument (abc /
Fermat–Catalan effective finiteness). This reframes OQ-03 away from "compute and
watch it grow" toward "find the global lever."

### Formalized (Lean, `native_decide`, build-verified)
`proofs/Proofs/FermatDefectOneOQ03.lean` — each box minimum pinned as a matching
pair (lower bound + achiever):
- `box_min_defect_n4` : every box triple has `|a⁴+b⁴−c⁴| ≥ 46`; `achiever_n4`
  realises `46` at `(5,5,6)`.
- `box_min_defect_n5` : `≥ 12`; `achiever_n5` realises `12` at `(13,16,17)`,
  `achiever_n5_primitive` certifies admissibility + gcd = 1.
- `box_min_defect_n6` : `≥ 601`; `achiever_n6` realises `601` at `(2,2,3)`.
- `box_min_defect_nonmonotone` : the headline — a primitive box defect of `12` at
  `n=5` coexists with a uniform `≥ 46` lower bound at `n=4`.
- `box_min_defect_n3_is_one` : the `n=3` contrast (the defect-one witness (6,8,9)).

Lower bounds discharged by `native_decide` (depends on `Lean.ofReduceBool`);
finite certificates over `c ≤ 100`, **not** statements about the global `M(n)`.

**Build status (researcher-1, 2026-06-20):** `docker-build.sh
Proofs.FermatDefectOneOQ03` → 7744 jobs, GREEN, 0 sorry in this file (the only
`sorry` warning is the unrelated parent headline conjecture
`FermatDefectOne.lean:280`). Wired into `Proofs.lean`; registered as an
`additionalFile` under the `fermat-defect-one` gallery entry (axiomatized:
`native_decide` ⇒ `Lean.ofReduceBool`).

## Relationship to siblings
- **OQ-04** certifies `m₁₀₀(n) ≥ 2` for `n∈{4,5,6}` (no defect-*one* witness in
  the box). OQ-03 sharpens this to the *exact* box minima and exposes the
  non-monotonicity OQ-04's coarse `≥ 2` bound hides.
- **OQ-02** (existence/infinitude at `n=3`) supplies the critical-exponent
  heuristic explaining why `m(3)=1` is special.

## Open / next
- The global `M(n)` growth question remains **open** (conditional on abc).
- Possible increment: certify exact box minima at larger `N` or `n=7,8` to test
  whether the non-monotone wobble persists, or formalize the `X^{3−n}` expected
  count as a heuristic statement (no Mathlib bearer for the analytic estimate).
