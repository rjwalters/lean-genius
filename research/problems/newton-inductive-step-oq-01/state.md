# Research State: newton-inductive-step-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-03-30T04:42:49-07:00 (OBSERVE); 2026-05-06 (ACT, via PR #16309)
**Last Updated**: 2026-05-13 (state-sync per `sessions/2026-05-13-state-sync-and-inductive-expansion-design.md`)
**Iteration**: 6

## Current Focus
Discharge the **1 remaining sorry** at line 154 of
`proofs/Proofs/NewtonInductiveStepOQ01.lean` — the general-k inductive step
of `newton_inequality_binomial` (k ≥ 2). The k=1 case is fully proven (line
199-334 via the sum-of-squares identity).

The sorry directly load-bears on `newton_inequality_means` (line 442-470,
uses `newton_inequality_binomial` at line 447). All other consequences
(`maclaurin_first_step`, `amgm_from_newton`) already route through the
proven k=1 case and are sorry-free.

## Active Approach
Induction on list length with Cauchy-Schwarz expansion of
`F_k² − F_{k−1}·F_{k+1}` via the recurrence
`esymm (x::xs) j = esymm xs j + x·esymm xs (j−1)`. The coefficient match
in `x` decomposes into three sub-inequalities:

- **`x⁰`**: IH at k + `binom_log_concave` (line 341)
- **`x²`**: IH at k-1 + `binom_log_concave` (with k=1 boundary case)
- **`x¹`**: cross-term — requires product of IH(k) and IH(k-1) followed by
  AM-GM, OR a refactor to the means-form recurrence (which has cleaner
  convex-combination structure)

See `sessions/2026-05-13-state-sync-and-inductive-expansion-design.md` §3
for the full design memo (~130 LOC budget, medium risk on the cross-term).

## Attempt Count
- Total attempts: 3+
- Current approach attempts: 1 (general-k Cauchy-Schwarz expansion, stalled
  at the `x¹` cross-term — sorry left at line 154)
- Approaches tried:
  1. Direct expansion without absorption identities (PR #16309 attempt,
     proved up to the inductive expansion structure but left the cross-term
     as `sorry`)
  2. k=1 base case via sum-of-squares identity (PR #16920, **proved**)
  3. Lean 4.26 API drift fix (PR #16927, unrelated to sorry discharge)

## Blockers
- **General-k Cauchy-Schwarz expansion** (line 154 sorry). The `x¹`
  cross-term coefficient `2·α(m+1,k-1)·α(m+1,k+1)·E_k·E_{k-1} ≥
  α(m+1,k)²·(E_{k-1}·E_k + E_{k-2}·E_{k+1})` cannot be derived from a single
  IH application; it requires combining IH(k) and IH(k-1) via square-root +
  AM-GM (or a means-form refactor that bypasses this expansion).
- **Mathlib gap**: at `v4.26.0` (lake-pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), there is no
  `Newton`/`newton_inequality`/`esymm_log_concave`/`Maclaurin` (other than
  the Leibniz pi series). `MvPolynomial.esymm` exists but is multivariate
  polynomial-valued, not directly evaluable on `List ℝ`. The file's custom
  `esymm : List ℝ → ℕ → ℝ` is the correct abstraction.

## Next Action
**Two-route recommendation per design memo §3.7:**

1. **Direct discharge** of line 154 sorry via the 3-coefficient decomposition
   in §3.4-3.5 (~130 LOC, medium risk on the `x¹` cross-term Cauchy-Schwarz).
2. **Means-form refactor**: prove `newton_inequality_means` directly via the
   cleaner convex-combination mean recurrence
   `ē_j(x::xs) = (m/(m+1))·ē_j(xs) + ((m+1−j)/(m+1))·x·ē_{j−1}(xs)`,
   then downgrade `newton_inequality_binomial` to a one-line corollary
   (~100 LOC, risk on the means-recurrence Cauchy-Schwarz).

S-ACT researcher chooses. After discharge:
- Sorry count: 1 → 0 (main file); 1 (Aristotle companion, downstream)
- Gallery `meta.json`: bump `sorries` 2 → 1 (then 1 → 0 after Aristotle)
- Slug status: `formalized` → `verified` (post-Aristotle)
