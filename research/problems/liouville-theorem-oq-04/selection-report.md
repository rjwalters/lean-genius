# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 26 available, 557 in-progress, 1408 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: liouville-theorem-oq-04
- **Name**: Liouville's Theorem: p-adic and Function Field Extensions
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 4/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 47** — third among genuinely unselected candidates. Selected for
   domain diversity: p-adic Diophantine approximation is distinct from any other problem
   selected in this session.

2. **Concrete Lean infrastructure available** — Mathlib has substantial p-adic machinery:
   `Padic`, `PadicInt`, `padicNorm`, and the ultrametric property. The archimedean
   Liouville bound already exists in the gallery. The p-adic analogue requires plugging
   the minimal polynomial lower bound argument into the non-archimedean norm — a
   structural parallel to the existing proof, not a new proof idea.

3. **Clear gallery extension** — the parent `liouville-theorem` proves |α - p/q| ≥ c/qⁿ
   for degree-n algebraic numbers. The p-adic analogue replaces |·| with |·|_p and ℝ
   with ℚ_p. The essential step (lower-bounding the p-adic norm of a polynomial
   evaluation via the ultrametric) has the same shape as the archimedean argument.

4. **Function field bonus** — the function field analogue over 𝔽_q(T) often has cleaner
   proofs due to the function field / number field dictionary. Mathlib's `RatFunc`
   provides some infrastructure, making this a secondary target if the p-adic case stalls.

## Rejection Summary

- **Candidates considered**: 7 remaining unselected available problems
- **Moonshot candidates rejected**: twin-primes-special-oq-01, weak-goldbach-oq-01,
  sophie-germain-oq-01 (tractability ≤ 2)
- **szemeredi-full-oq-01**: deferred for domain diversity (Szemerédi family already
  represented in this session)
- **Confidence**: medium — p-adic Liouville bounds are classical mathematics with a
  clear proof sketch; the challenge is Lean 4 infrastructure for padicNorm interactions
  with minimal polynomial evaluations

## Related Gallery Proofs

- `liouville-theorem`: Parent proof — archimedean Liouville inequality and transcendence
  of Liouville numbers. The proof strategy (polynomial non-zero evaluation lower bound)
  transfers to the p-adic setting with `padicNorm` replacing `abs`.
- `minkowski-fundamental-theorem-oq-04` (also selected this session): Uses arithmetic
  lower-bound arguments in a related number-theoretic context.

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/LiouvilleTheorem.lean` — find the key lemma that
   lower-bounds `|f(α) - f(p/q)|` using the minimal polynomial and its derivative.
   Identify which parts use `Real.norm` vs `abs` and which can be abstracted to a
   general valued field.

2. **ORIENT**: Survey Mathlib's `padicNorm` API. Key facts needed:
   - `padicNorm.nonzero`: if x ≠ 0 then padicNorm p x ≠ 0
   - Ultrametric: `padicNorm p (a + b) ≤ max (padicNorm p a) (padicNorm p b)`
   - `padicNorm.eq_pow_of_ne_zero`: exact value for rationals
   State the p-adic Liouville theorem: for α ∈ ℚ_p algebraic of degree n over ℚ,
   ∃ c > 0, ∀ r ∈ ℚ, ‖α - r‖_p ≥ c / ‖denom(r)‖^n.

3. **DECIDE**: Follow the archimedean proof structure:
   - Take minimal polynomial f ∈ ℤ[X] of α, degree n
   - For r = p/q ∈ ℚ near α: `q^n · f(r) ∈ ℤ`, so `|q^n · f(r)|_p` is controlled
   - The ultrametric forces `|f(α) - f(r)|_p` to bound from above, `f(α) = 0` from below
   This reduces to `nlinarith`/`norm_num` after identifying the right Mathlib lemmas for
   `padicNorm` and `minpoly`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 26 |
| In Progress | 557 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

- Pool depth: **adequate** (26 available, threshold=15)
- Recommendation: Pool healthy.
- Next refresh recommended: next scheduled cycle (~30 min)

## Initialized

- [x] Research workspace exists (`research/problems/liouville-theorem-oq-04/`)
- [x] problem.md populated
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher
