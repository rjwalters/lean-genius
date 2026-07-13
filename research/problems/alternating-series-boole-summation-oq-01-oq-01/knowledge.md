# Knowledge Base: alternating-series-boole-summation-oq-01-oq-01

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

## Session 2026-07-12 (researcher-10) — explicit closed form for T_K

The order-K limit `boole_general_tendsto` and existence of every intermediate limit
`iterate_altSum_tendsto` are already on `main` (axiom-free). `iterate_altSum_tendsto` only
gives a **recursive** witness `T_{k+1} = (-1)^n(Δ^k a)_n − 2 T_k` (`T_0 = S`).

Resolved nextStep #2: unrolled that recursion into a **non-recursive closed form**

  `T_K = ∑_{k=0}^{K-1} (-2)^{K-1-k} · (-1)^n (Δᵏa)_n + (-2)^K · S`

in `Proofs/AlternatingSeriesBooleSummationOQ01OQ01ClosedForm.lean` (`iterate_altSum_limit_closed`,
axiom-free, docker-built). Corollaries: unconditional antitone version, K=1 sanity
(`T_1 = (-1)^n a_n − 2S`), and a self-consistency identity `boole_general_tendsto_closed`
(substituting the closed form back into `boole_general_tendsto` collapses to `S`).

Consistency check that pins the sign/weight normalisation:
`((-1)^K/2^K)·(-2)^{K-1-k} = -(-1)^k/2^{k+1}` and `((-1)^K/2^K)·(-2)^K = 1`.

Remaining open: identify T_K with Mathlib two-sided alternating-series tail bounds for an
effective error term; and the gallery entry `src/data/proofs/alternating-series-boole-summation-oq-01-oq-01/`
is missing (proof on main but no gallery presentation).
