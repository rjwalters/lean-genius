# Knowledge Base: erdos-1144-oq-03

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

---

## Session (researcher-3, 2026-07-09): reduction-lemma formalization

Created `Erdos1144OQ03.lean` (VERIFIED, 3059 jobs, 0 sorry / 0 new axiom). Encoded OQ-03 as
a correct logical reduction instead of a risky axiom:

- `EventualPowerBound` / `FrequentPowerExceedance`: competing ceiling-vs-exceedance shapes.
- `not_frequentExceedance_of_eventualBound`: reduction lemma (eventual ≤ contradicts frequent >).
- `no_power_upper_bound_of_frequent_exceedance`: OQ-03 as an implication, deep lower bound = HYPOTHESIS.
- `atherfold_refutes_frequent_exceedance`: an UNCONDITIONAL `∀K, FrequentPowerExceedance` axiom
  would be INCONSISTENT with the parent's `atherfold_upper_bound` (caps growth at exponent 1+ε).

**Key honesty point / trap avoided:** the naive nextStep "add an axiom capturing an a.s. maximal
lower bound of order √N(log N)^{1-ε}" — if phrased as `∀K, FrequentPowerExceedance f K C` — is
INCONSISTENT with Atherfold. The o(1)-is-genuine result is a statement about a NARROWER exponent
range; asserting "no fixed K" literally is refuted by Atherfold at K=2. So it must be a hypothesis,
not a standalone axiom (cf. the erdos-1018 removed-inconsistent-axiom precedent).

**Gotcha:** in `∃ᶠ/∀ᶠ N in atTop, ...` where the body starts with `Real.sqrt (N:ℝ)` before any
`partialSum f N`, elaboration fixes `N : ℝ` (from the `(N:ℝ)` coercion) and then `partialSum f N`
(wants ℕ) mismatches. Annotate the bound variable `(N : ℕ)` explicitly.
