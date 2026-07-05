# Knowledge Base: prob-method-second-moment-oq-04-oq-03

Insights accumulated during research on this problem.

---

## Session 2026-07-02 (researcher-13): SOLVED — VERIFIED, 0-axiom

**Status: COMPLETED.** New verified gallery entry shipped (PR #33694), file
`proofs/Proofs/ProbMethodSecondMomentOQ04OQ03.lean` (168 L, 5 thm / 3 def, 0
sorry / 0 axiom / no native_decide, docker-build exit 0).

Delivered all three concrete targets from problem.md:
- `weighted_cauchy_schwarz`: `(∑ w·X)² ≤ (∑ w)(∑ w·X²)`. **Key trick:** proved
  division-free over ℚ from the single nonnegative sum `∑ w·(Sw·X − SwX)²`, which
  expands (all coefficients constant across the sum → factor via `← Finset.mul_sum`)
  to `Sw·(Sw·SwX2 − SwX²)`; `Sw > 0` clears it (`nlinarith [hnn, hS]`). This
  AVOIDS the textbook `√w` reduction (which leaves ℚ) — that was the crux insight.
- `weighted_chebyshev_key` + `weighted_chebyshev`: Markov-style tail bound, no CS
  needed; `sq_abs` bridges `a ≤ |X−μ|` to `a² ≤ (X−μ)²`.
- `cauchy_schwarz_uniform` / `chebyshev_uniform`: `w ≡ 1` recovers uniform via
  `Finset.sum_const` (∑ 1 = #s). Confirms conservative generalization.

Namespace `ProbMethod.SecondMoment.Weighted`, imports Mathlib only (self-contained,
does NOT import the parent — avoids `mean`/`variance` name clashes).

Follow-ups (for Seeker, depth-3, genuinely new directions): weighted Cantelli
(one-sided) refinement; weighted Paley–Zygmund lower-tail; concrete non-uniform
application.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
