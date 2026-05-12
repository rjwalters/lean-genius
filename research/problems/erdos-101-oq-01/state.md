# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11 (S1)
**Iteration**: 1
**Last Updated**: 2026-05-11 (researcher-3)

## Current Focus

S1 (researcher-3): Initial scaffold for OQ-01 of Erdős Problem #101.
Records the formal $\Sigma_2$-style statement of the $\$100$ open
conjecture, the asymptotic vocabulary (`IsLittleOh_n_squared`,
`BoundsAtRate`), and the small-case lemmas the conjecture subsumes
— all unconditional except the main theorem.

## Active Approach

**Statement-first scaffold; small cases first.**

The conjecture is OPEN; this iteration does NOT attempt a proof.
Instead it:

1. Pins the formal Σ₂ statement in Lean syntax.
2. Records the equivalent rate-form via `BoundsAtRate`.
3. Proves the small-case (`|P| ≤ 3`) lemma unconditionally so the
   ε–N form is meaningful only in the regime $|P| \to \infty$.
4. Connects to the parent file's `improved_upper_bound` via a
   real-valued $n^2/12$ bound — exhibiting the elementary bound
   that is *not* $o(n^2)$.

## Next Action

S2 candidates (in order of expected value):

1. **Formalise the Solymosi–Stojaković existence statement** as a
   recorded *axiom-free `theorem ... := by sorry`* (since the
   construction is beyond elementary Lean). Refutes Erdős's
   $\Theta(n^{3/2})$ conjecture in the gallery.

2. **`Asymptotics.IsBigO` / `IsLittleO` bridge**. Show
   `(fun n => maxFourPointLines n) =O[atTop] (· ^ 2)` from the
   real-valued $n^2/12$ bound; record the conjecture as a
   `=o[atTop] (· ^ 2)` `sorry`. Lets future progress slot into
   Mathlib's asymptotic-comparison framework.

3. **Investigate per-point Cauchy–Schwarz refinements.** The parent
   file's `fourCollinearThrough_bound` $\leq (n-1)/3$ combined with
   second-moment double counting may give a $1 - o(1)$ leading
   constant on the $n^2/12$ elementary bound. Not $o(n^2)$, but a
   concrete *improvement on a non-trivial constant* would be the
   first sub-elementary upper bound.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1 (S1 scaffold)
- Approaches tried: 0 (no proof attempts yet)

## Build Status

S1 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink; local Docker builds re-fresh-clone Mathlib. CI is
ground truth.

S1 risk profile:
* 5 of 6 theorems are trivial or restate parent lemmas — low risk.
* 1 theorem (`bounds_at_rate_quadratic_over_twelve`) uses
  `Nat.cast_div_le` + `push_cast` for a ℕ→ℝ rate cast — standard
  Mathlib pattern.
* No new imports; everything transitive via `Proofs.Erdos101Problem`.

## Blockers

None for S1 (statement-only). Closing the OPEN conjecture is itself
a $\$100$ Erdős prize-level result and not a single-session goal.
