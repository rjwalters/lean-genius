# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S2)
**Iteration**: 2
**Last Updated**: 2026-05-12 (researcher-1)

## Current Focus

S2 (researcher-1) delivered the Solymosi–Stojaković 2013 existential
lower bound as a `theorem ... := by sorry` together with the corollary
that Erdős's original $\Theta(n^{3/2})$ conjecture is refuted by the
same construction.  Both new theorems are sorry stubs — the
construction itself uses algebraic geometry over finite fields and is
deferred to a much later iteration.  No new axioms were introduced.

## Active Approach

**Statement-first scaffold; small cases + recorded lower bound.**

Following S1's "statement-first" pattern, S2 records:

1. `solymosi_stojakovic_lower_bound` — $\forall C > 0, \exists N, \forall n \geq N,
   \exists P$ with $|P| = n$, no-five-collinear, and
   $\text{fourPointLineCount}\,P \geq n^{2 - C / \sqrt{\log n}}$. Sorry.
2. `erdos_three_halves_conjecture_refuted` — there is no $N$ such that
   every no-five-collinear $P$ with $|P| \geq N$ satisfies
   $\text{fourPointLineCount}\,P \leq |P|^{3/2}$.  Sorry (real-analysis
   arithmetic — discharges from (1) by $2 - C/\sqrt{\log n} > 3/2$ for
   sufficiently large $n$).

## Next Action

S3 candidates (in order of expected value):

1. **Discharge `erdos_three_halves_conjecture_refuted`.** The proof is
   pure real-analysis arithmetic given S2's
   `solymosi_stojakovic_lower_bound`: pick $C = 1/2$ (or any
   $C > 0$), find $N$ with $2 - C/\sqrt{\log n} > 3/2$ for $n \geq N$,
   then derive the contradiction.  Estimated 30–60 lines of
   `Real.rpow_lt_rpow` + `Real.log_pos` manipulation.

2. **`Asymptotics.IsBigO` / `IsLittleO` bridge.** Show
   `(fun n => maxFourPointLines n) =O[atTop] (· ^ 2)` from the
   real-valued $n^2/12$ bound; record the conjecture as
   `=o[atTop] (· ^ 2)` `sorry`.  Requires defining
   `maxFourPointLines : ℕ → ℕ` via `Finset.sup'` or `Set.Sup`.

3. **Investigate per-point Cauchy–Schwarz refinements.** The parent
   file's `fourCollinearThrough_bound` $\leq (n-1)/3$ combined with
   second-moment double counting may give a $1 - o(1)$ leading
   constant on the $n^2/12$ elementary bound.  Not $o(n^2)$, but a
   concrete *improvement on a non-trivial constant* would be the
   first sub-elementary upper bound.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S2 lower-bound recording)
- Approaches tried: 1 (S1 scaffold, S2 lower-bound recording —
  same statement-first approach extended)

## Build Status

S2 build: PENDING.  New imports
(`Mathlib.Analysis.SpecialFunctions.Pow.Real`,
`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
`Mathlib.Analysis.SpecialFunctions.Sqrt`) provide `Real.rpow`,
`Real.log`, `Real.sqrt` used in the lower-bound statement.  CI is
ground truth.

S2 risk profile:
* 2 new theorems, both `theorem ... := by sorry` — no proof tactics
  to fail on.
* 3 new Mathlib imports are well-established modules.
* No changes to existing theorems or definitions.

## Blockers

None for S2 (statement-only).  Closing the OPEN conjecture is itself a
$\$100$ Erdős prize-level result and not a single-session goal.
