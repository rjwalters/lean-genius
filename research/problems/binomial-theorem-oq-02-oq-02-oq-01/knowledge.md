# q-Vandermonde Identity via Gaussian Binomial Coefficients — Knowledge Base

## Problem Statement

Can the q-Vandermonde identity

$$
\sum_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q = \binom{m+n}{r}_q
$$

be formalized using Mathlib's Gaussian binomial coefficient API?

## Status

**Slug Status**: `graduated` (verified-original)
**Gallery Badge**: `original`
**Aristotle Suitable**: Partially — Aristotle can attempt the inductive step of full q-Vandermonde and the dual q-Pascal recurrence, both well-scoped and HARD-classified. Not suitable for the full identity unless guided by an explicit decomposition.

## Lean Slug Status

- **File**: `proofs/Proofs/BinomialTheoremOQ02OQ02OQ01.lean` (297 LOC)
- **Theorems**: 13
- **Definitions**: 1 (`qBinomial : R → ℕ → ℕ → R` over arbitrary `CommSemiring R`)
- **Axioms**: 0
- **Sorries**: 0
- **Status**: `verified` (badge: `original`)
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean toolchain `v4.26.0`)
- **PRs merged**: #16707 (q-Vandermonde m=0 / n=0 base cases), #16779 (k=1 closed form via geometric sum + reflection at k=1)

## Architecture

Gaussian binomial coefficient API built from first principles over an arbitrary `CommSemiring R`:

- `qBinomial : R → ℕ → ℕ → R` via the q-Pascal recurrence
- All identities derived inductively (no polynomial-quotient or rational-function machinery)
- Same definition specializes to `ℕ` at $q = 1$ and to `ℤ[q]` for the analytic theory, with no extra coercion machinery

## Built Items (12)

1. `qBinomial : R → ℕ → ℕ → R` — definition over `CommSemiring` via q-Pascal recurrence
2. `qBinomial_zero_right` — boundary lemma $\binom{n}{0}_q = 1$
3. `qBinomial_zero_succ` — boundary lemma $\binom{0}{k+1}_q = 0$
4. `qBinomial_succ_succ` — q-Pascal recurrence $\binom{n+1}{k+1}_q = q^{k+1} \binom{n}{k+1}_q + \binom{n}{k}_q$
5. `qBinomial_eq_zero_of_lt` — vanishing $\binom{n}{k}_q = 0$ for $k > n$
6. `qBinomial_self` — diagonal $\binom{n}{n}_q = 1$
7. `qBinomial_at_one` — $q \to 1$ specialization $\binom{n}{k}_{q=1} = \binom{n}{k}$ (in `ℕ`)
8. `qVandermonde_zero_left` — base case $m = 0$
9. `qVandermonde_zero_right` — base case $n = 0$
10. `vandermonde_zero_left_nat`, `vandermonde_zero_right_nat` — classical $q = 1$ base cases in `ℕ`
11. `qBinomial_one_eq_geom_sum` — $k = 1$ closed form $\binom{n}{1}_q = \sum_{i=0}^{n-1} q^i$ (induction on $n$ via q-Pascal)
12. `qBinomial_succ_pred_eq_geom_sum` — symmetric closed form $\binom{n+1}{n}_q = \sum_{i=0}^{n} q^i$; `qBinomial_reflection_at_one` — k=1 reflection corollary $\binom{n+1}{1}_q = \binom{n+1}{n}_q$
13. Gallery entry at `src/data/proofs/binomial-theorem-oq-02-oq-02-oq-01/meta.json` — `status: verified`, `badge: original`

## Insights (5)

1. **Mathlib v4.26.0 has no `GaussianBinomial` API** — the entire `qBinomial` definition + identities had to be built from first principles via the q-Pascal recurrence (no rational-function or polynomial-quotient machinery).
2. **`CommSemiring` is the right base** — defining `qBinomial` over an arbitrary `CommSemiring` (rather than a field or `ℤ[q]`) allows the same definition to specialize to `ℕ` at $q = 1$ and to `ℤ[q]` for the analytic theory, with no extra coercion machinery — a `CommSemiring` is exactly enough structure to support the q-Pascal recurrence.
3. **Induction-via-q-Pascal as engine** — the $k = 1$ closed form proof is the prototypical example: the q-Pascal recurrence collapses to $a_{n+1} = q \cdot a_n + 1$ with $a_0 = 0$, whose unique solution is the geometric sum $\sum_{i=0}^{n-1} q^i$.
4. **Symmetric closed form supports reflection** — `qBinomial_succ_pred_eq_geom_sum` parallels `qBinomial_one_eq_geom_sum` via `qBinomial_self`, enabling the $k = 1$ reflection corollary as a one-line consequence.
5. **The full inductive step is genuinely harder** — extending to general $(m, r)$ requires re-indexing the convolution sum $\sum_k q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q$ with careful tracking of the weight exponents; the dual q-Pascal recurrence (now within reach given the $k = 1$ closed form) would be a stepping stone.

## Mathlib Gaps (1)

- **`GaussianBinomial` namespace** absent from Mathlib v4.26.0 (verified via Grep at lake pin `2df2f0150c…`). The API built in this slug — `qBinomial`, `qBinomial_succ_succ` (q-Pascal), `qBinomial_eq_zero_of_lt`, `qBinomial_self`, `qBinomial_at_one`, geometric-sum closed forms — is a candidate for upstream contribution once the inductive step of q-Vandermonde is also formalized.

## Next Steps (3 — deferred to future iteration)

1. **Inductive step of q-Vandermonde** — leverage `qBinomial_succ_succ` (q-Pascal recurrence) on the $m + 1$ side and re-index the convolution sum with careful tracking of the $q^{(m-k)(r-k)}$ weights.
2. **Dual q-Pascal recurrence** — $\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q$. Now within reach given the $k = 1$ closed form (geometric sum); enables general reflection symmetry.
3. **General reflection symmetry** — $\binom{n}{k}_q = \binom{n}{n-k}_q$ for $k \leq n$, derived from dual q-Pascal.

## Sessions

| Session | Date | Mode | Outcome | PR |
|---------|------|------|---------|-----|
| 1 | 2026-05-07 | FRESH | Initial qBinomial API: definition, q-Pascal recurrence, boundary lemmas, vanishing, diagonal, q→1 specialization, q-Vandermonde base cases (m=0, n=0), classical base cases in `ℕ` | #16707 |
| 2 | 2026-05-07 | FRESH | Closed form at k=1 via geometric sum (`qBinomial_one_eq_geom_sum`), symmetric closed form (`qBinomial_succ_pred_eq_geom_sum`), reflection at k=1 corollary | #16779 |
| (doc) | 2026-05-08 | research-doc | Documented completion in research JSON | #16955 |
| 3 | 2026-05-16 | REVISIT (catch-up) | Doc-only STATE-SYNC: problem.md template fill (autogen "AVAILABLE:" → actual statement + LaTeX + 3-row cross-ref table + references), new knowledge.md (this file), new sessions/ directory, JSON iteration 2→3 + lastUpdate refresh, pool status `available` → `graduated` | (this session) |

For per-session detail, see `sessions/`:

- `sessions/2026-05-16-s01.md` — Session 3 catch-up STATE-SYNC

## Tags

- combinatorics
- q-analogs
- gaussian-binomial
- q-vandermonde
- extension
- seeker-selected
- research

---

*Last updated: 2026-05-16T09:11Z (Session 3 catch-up STATE-SYNC)*
*Slug graduated 2026-05-08 (PRs #16707 + #16779 + #16955); pool entry caught up to `graduated` 2026-05-16.*
