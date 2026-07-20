# Knowledge Base: combinations-formula-oq-03-oq-04

Unimodality of the Gaussian (q-)binomial coefficient sequence.

---

## Problem Understanding

Target: the coefficient sequence `(a_0, …, a_{k(n-k)})` of `[n,k]_q ∈ ℤ[q]` is
unimodal. The pinned open-question statement is the *no interior strict valley*
form: no `i` with `a_{i-1} > a_i < a_{i+1}`.

Prior work (axiom-free over `ℤ[X]`): palindromy/self-reciprocity
(`qBinom_reciprocal`, `qBinom_X_reflect`, `qBinom_X_coeff_symm'`), degree/monicity,
constant term `1`, coefficient nonnegativity, pinned extreme coefficients, and the
base-change bridges. The **reduction** (`unimodalCoeffs_of_palindromic_of_monotone_left`,
PR #39335) turns full unimodality into the single hypothesis `hmono` — coefficients
weakly increase up to `⌊k(n-k)/2⌋`.

---

## Insights

- **The reduction cleanly isolates the open substance.** With palindromy +
  nonnegativity already proven, `UnimodalCoeffs (qBinom X n k)` reduces to `hmono`
  (one-sided monotonicity to the midpoint). Everything symmetric is discharged.
- **k = 1 discharges `hmono` for free.** `[n,1]_q = [n]_q = 1 + q + … + q^{n-1}`
  (`qBinom_one_right`) has a **flat** coefficient sequence `1,…,1` on `[0, n-1]`, so
  weak monotonicity on the left half is trivial. This gives `qBinom_X_one_unimodal`
  unconditionally — the first NONTRIVIAL column (degree `n-1`), vs the vacuous k=0.
  (n = 0 is the zero polynomial, handled separately.)
- **The no-valley target follows from `UnimodalCoeffs`.** `CoeffNoValley` +
  `coeffNoValley_of_unimodalCoeffs` connect the strong "single hump" shape to the
  open question's exact statement; k ≤ 1 discharged.

## Built (CombinationsFormulaOQ03OQ04.lean)

Prior (#39335): `UnimodalCoeffs`, `unimodalCoeffs_of_palindromic_of_monotone_left`,
`qBinom_X_unimodalCoeffs_of_monotone_left`, `qBinom_X_unimodalCoeffs_zero`.

This session:
- `qNumber_X_coeff : (qNumber X n).coeff j = if j < n then 1 else 0`
- `qBinom_X_one_coeff`
- `qBinom_X_one_unimodal` (unconditional k=1)
- `CoeffNoValley` + `coeffNoValley_of_unimodalCoeffs`
- `qBinom_X_zero_noValley`, `qBinom_X_one_noValley`

## Dead Ends / Open

- General-`k` `hmono` (Sylvester 1878; Proctor's sl₂ proof 1982) remains OPEN —
  Mathlib lacks the sl₂/hard-Lefschetz stack; O'Hara's decomposition is heavy.

## Next directions

- `k = 2`: coefficients `⌊j/2⌋+1` rising to the midpoint — first non-flat left half;
  discharge `hmono` directly, then the reduction closes it.
- General `hmono` via Proctor/O'Hara is the remaining substance.
