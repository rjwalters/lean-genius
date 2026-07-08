# Knowledge Base: puiseux-theorem-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Original goal: replace 5 `True`-stub theorems in `PuiseuxTheorem.lean` (Wiedijk #41)
with real content. **This goal is already achieved** by predecessor PRs #30441,
#33067, #33838:

- `square_root_puiseux` (`Y² = x`) and `cusp_parameterization` (`Y² = x³`) now
  construct actual Hahn-series roots and verify the defining equation.
- `puiseux_binomial_root` / `puiseux_binomial_ramification` / `puiseux_binomial_isRoot`
  cover the binomial base case `Yⁿ = c·xᵐ` over an algebraically closed field.
- The two deepest stubs (`puiseux_theorem`, `puiseux_is_algebraic_closure`, plus
  `newton_puiseux_terminates`) were removed rather than faked — the file header now
  honestly states that full algebraic closure of the Puiseux field remains open
  (the Newton–Puiseux convergence assembly is not in Mathlib).

File state at session start: 603 lines, 0 sorries, 0 axioms, 11 theorems.

---

## Insights

- The whole file is powered by one workhorse lemma `isPuiseux_single` (every
  single-term Hahn series is a Puiseux series, ramification = `m.den`) plus the
  computation `(single a c)ⁿ = single (n • a) (cⁿ)` via `HahnSeries.single_pow`
  and `n • (m/n) = m` via `div_mul_cancel₀`.
- **This session's contribution**: added `puiseux_binomial_orderTop`, the general
  single-edge Newton–Puiseux statement for an *arbitrary* slope `m/n`. It proves
  that `Yⁿ = c·xᵐ` (`c ≠ 0`, alg-closed `K`) has a Puiseux root with
  `orderTop = m/n`. This unifies `puiseux_binomial_ramification` (`m=1`),
  `square_root_puiseux` (`n=2,m=1`) and `cusp_parameterization` (`n=2,m=3`) as
  instances of one theorem. Proof is a copy of `puiseux_binomial_ramification`
  with the general exponent `m/n`; verified 0-sorry/0-axiom.
- Build gotcha: `docker-build.sh Proofs.PuiseuxTheorem` hit an intermittent
  `exit code 135` (elaborator stack-overflow, NOT a logic error) on the first
  attempt; a plain re-run built cleanly. Code 135 ≠ proof failure here.

---

## Dead Ends

- Full algebraic closure (`IsAlgClosed (PuiseuxField K)`) is not attemptable
  without the Newton–Puiseux convergence machinery, which is absent from Mathlib
  v4.26 — this is a >1000-line foundational build, out of scope for a session.
