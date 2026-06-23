# Proving Budan's Upper Bound Axiom (descartes-rule-of-signs-oq-02-oq-01)

## Problem Summary

The parent problem **descartes-rule-of-signs-oq-02** formalizes Budan's
theorem (1807) as a generalization of Descartes' Rule of Signs. The main
result, formalized in
`proofs/Proofs/DescartesRuleOfSignsOQ02.lean`, is

```lean
axiom budan_upper_bound_axiom (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b
```

where
- `budanCount p x` = sign-variation count of the **derivative tower**
  evaluated at `x`, i.e.
  `signChangesInList [p(x), p'(x), p''(x), …, p^(n)(x)]`,
- `rootsInInterval p a b` = `Multiset.card (p.roots.filter (a < · ∧ · ≤ b))`.

The open question recorded as **oq-02-oq-01** is:

> Can the `budan_upper_bound_axiom` from OQ-02 be fully proved in Lean (and
> the corresponding `axiom` declaration replaced by a `theorem`)?

## Statement (informal)

Prove: for every nonzero real polynomial `p` and every half-open interval
`(a, b]` with `a < b`,
```
#(roots of p in (a, b], counted with multiplicity) ≤ V_p(a) − V_p(b)
```
where `V_p(x) = signChangesInList [p(x), p'(x), …, p^(deg p)(x)]`.

## Why This Matters

The Budan-Fourier upper bound is the foundational result behind:
- Vincent's theorem for real root isolation (1834)
- The VAS (Vincent–Akritas–Strzeboński) algorithm — used today in CAD/RUR
- Modern real algebraic geometry computations and certified root counting

Mathlib currently provides `Polynomial.roots_countP_pos_le_signVariations`
(Descartes' rule for positive roots, via a coefficient-based
`signVariations`) but has **no Budan-Fourier infrastructure at all** —
neither the derivative-tower variation count `V_p(x)` nor the half-open
interval generalization. So proving this axiom does not duplicate Mathlib;
it adds genuinely missing infrastructure.

## Classification

```yaml
tier: C
significance: 7
tractability: 5
status: AXIOMATIZED
parent: descartes-rule-of-signs-oq-02
sibling-files:
  - DescartesRuleOfSignsOQ02OQ01.lean   # this slug's scaffold
  - DescartesRuleOfSignsOQ02.lean       # parent Budan formalization
tags:
  - polynomials
  - real-analysis
  - root-counting
  - rolle
  - budan-fourier
  - axiom-elimination
```

## Existing Infrastructure

### In `DescartesRuleOfSignsOQ02.lean` (parent, 699 LOC, 0 sorries, 3 axioms)

Definitions usable by the eventual proof:
- `iterDeriv : ℝ[X] → ℕ → ℝ[X]` — the iterated derivative
- `budanSequence p n x : List ℝ` — `[p(x), p'(x), …, p^(n)(x)]`
- `signChangesInList : List ℝ → ℕ` — sign-variation count (zeros skipped)
- `budanCount p x : ℕ` — `signChangesInList (budanSequence p p.natDegree x)`
- `rootsInInterval p a b : ℕ` — `Multiset.card (p.roots.filter (a<· ∧ ·≤b))`

Proved helpers (zero sorries):
- `budanCount_C`, `budanCount_zero`, `rootsInInterval_C`,
  `rootsInInterval_zero`, `rootsInInterval_split`
- `iterDeriv_eval_zero` — `(p^(k))(0) = k! · p.coeff k`
- `budanCount_zero_eq_coeff_sign_changes` — bridge to Mathlib's
  coefficient-based `signVariations`
- `budanCount_smul` — invariance under nonzero scaling
- `rolle_polynomial` — Rolle's theorem for polynomials (from
  `Mathlib.Analysis.Calculus.LocalExtr.Rolle.exists_deriv_eq_zero`)
- `n_roots_derivative_roots` — `n+1` ordered roots of `p` imply `n` roots
  of `p'` between them
- `budanCount_le_natDegree`, `descartes_from_budan`

### In `DescartesRuleOfSignsOQ02OQ01.lean` (this slug, 192 LOC, 0 sorries, 0 axioms — after S1 #17193)

Inside a **separate namespace** `BudanUpperBound` (no `import` of the
parent file). The five S1-merged iterDeriv structural lemmas plus three
building blocks:

| Theorem | Status |
|---|---|
| `iterDeriv_zero_eq`, `iterDeriv_succ` | `rfl` |
| `iterDeriv_of_zero` | proved |
| `iterDeriv_natDegree_le` | proved (via `Polynomial.natDegree_derivative_le`) |
| `iterDeriv_eq_zero_of_natDegree_lt` | proved |
| `constant_no_roots` | proved (deg-0 base) |
| `linear_at_most_one_root` | proved (deg-1 has ≤ 1 root in any interval) |
| `rolle_polynomial` | proved (re-stated from Mathlib's IVT/Rolle) |
| `root_of_sign_change` | proved (IVT-based) |

Note: this file is **self-contained**. It does not import OQ-02 and
therefore does not yet **discharge** `budan_upper_bound_axiom` — the
helpers live in a parallel namespace.

## High-Level Strategy

Strong induction on `p.natDegree`.

1. **Base case** `natDegree p ≤ 0`:
   `p = C c` with `c ≠ 0` ⇒ `rootsInInterval p a b = 0`,
   `budanCount p a = budanCount p b = 0` (both via `budanCount_C`),
   bound trivial.

2. **Base case** `natDegree p = 1`:
   `p = bX + c` with `b ≠ 0`. The unique root is `r = −c/b`. Case
   analysis: whether `r ∈ (a, b]` or not. In each case the budan
   sequence `[p(x), b]` has either 0 or 1 sign changes; the algebraic
   accounting matches `rootsInInterval`.

3. **Inductive step** `natDegree p ≥ 2`:
   By Rolle (already proved): between consecutive roots of `p` in `(a,b]`
   the derivative `p'` has a root. Combined with sign-change accounting:
   the number of sign changes in the derivative tower drops by at least
   the count of roots in the interval. Formally one needs

   ```
   (V_p(a) - V_p(b)) - (V_{p'}(a) - V_{p'}(b)) ≥ rootsInInterval p a b
                                                  - rootsInInterval p' a b
   ```

   then apply the IH to `p'` (which has `natDegree = natDegree p − 1`).

Of these, step 1 is one-liner-trivial against the existing OQ-02 lemmas.
Step 2 is concrete but case-heavy (~40-60 LOC). Step 3 is the hard part
and is essentially the **sign-change accounting layer** that the S1 PR
explicitly flagged as future work.

## Reference

- Budan de Boislaurent, *Nouvelle méthode pour la résolution des
  équations numériques* (1807).
- Fourier, *Analyse des équations déterminées* (1831, posthumous).
- Akritas, *Vincent's theorem of 1836: overview and future research*
  (2008).
- Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed.,
  §2.2 (Budan-Fourier and Sturm).
- Mathlib `Polynomial.RuleOfSigns` — provides
  `signVariations`/`roots_countP_pos_le_signVariations` but no
  Budan-Fourier API. Uses a **factor-out-a-positive-root induction**
  pattern, NOT Rolle.
