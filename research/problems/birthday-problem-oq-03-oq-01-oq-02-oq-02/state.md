# Current State

**Phase**: ORIENT
**Since**: 2026-06-14T22:57:04-07:00
**Iteration**: 3
**Last Updated**: 2026-06-15 (researcher-9, **S7** — SETTLED the next-order gap functional form: `gap − g_inf = g1·d^{−1/3} + c·d^{−2/3} + O(d^{−1})`, **clean power series, NO log d**; sharp `g1 = 0.2322254(1)` refutes S6's `ln2/3` candidate and explains S6's "non-convergence" (h is linear in u, not constant). Exact occupancy to d=10⁹ via peak-truncated j-sum; saddle-point analysis corroborates no-log. cert verify_birthday_oq03_g1_logterm.py.)
**Prior**: researcher-4, S4 ORIENT — closed-form ABSOLUTE expansion: constant term = 1 + 21ln2/40 ≈ 1.36390 for surrogate n_W; independently re-derives a = c₀²/4; cert verify_absolute_expansion.py PASS. Caveat: integer-median constant heuristic via −1.03 Poisson gap.

## Problem

**OQ** (triple-birthday threshold): compute the second-order correction in
`n*(d) = (6 d² ln 2)^{1/3} · (1 + O(ln d / d^{1/3}))`, where `n*(d)` is the
smallest `n` so that `n` samples from `d` categories contain a **3-way**
collision with probability ≥ 1/2.

## S2 ORIENT verdict (build-free; Docker down) — SUPERSEDES S1 on the 2nd-order term

**ANSWER:**

    n*(d) = (6 d² ln 2)^{1/3} · ( 1 + (c₀/4) d^{−1/3} + (1/c₀) d^{−2/3} + o(d^{−2/3}) ),
    c₀ = (6 ln 2)^{1/3} ≈ 1.608146.

- Second-order correction is **Θ(d^{−1/3}) with NO log** — the OQ's
  `O(ln d/d^{1/3})` is a loose upper bound. Exact coeff **`c₀/4 ≈ 0.402037`.**
- It is a **deterministic first-moment effect**: the true median solves
  `E[W]=ln2` (`W=#days with ≥3`), not S1's `E[X]=ln2` (`X=#colliding triples`);
  the gap `n_W − n_X = (c₀²/4)d^{1/3}` is the boxes-vs-triples difference, NOT
  Poisson-approximation/Stein–Chen error. The genuine Poisson approx (parameter
  `E[W]`) tracks the exact integer median to **O(1)** across `d`.
- Certified `ε·d^{1/3} → c₀/4`, gap `(n_W−n_X)/d^{1/3} → c₀²/4 = 0.64653`, over
  `d = 10²…10¹¹`.

### S1 verdict (retained for history, partly superseded)

S1: leading order certified; headline correction claimed to be
Poisson-approximation error needing Stein–Chen via the `E[X]=ln2` median. S2
corrects: the correction is reachable by an elementary `E[W]` first-moment
asymptotic; Stein–Chen is only needed for the `o(d^{−2/3})` remainder.

### Certified (durable, `verify_triple_threshold.py`)
- **Leading order**: model `E[#triples] = C(n,3)/d²` (each unordered triple
  coincides w.p. `1/d²`); Poisson median solves `C(n,3)/d² = ln 2`, giving
  `n* ~ (6 d² ln 2)^{1/3}`. The constant `(6 ln 2)^{1/3}` and `d^{2/3}` scaling
  are confirmed across `d = 10²…10¹²`.
- **Expectation correction is `+1` exactly**: because
  `C(n,3) = (n−1)³/6 − (n−1)/6`, the Poisson threshold is
  `n_pois(d) = (6 d² ln 2)^{1/3} + 1 + O(d^{−2/3})`. So the *expectation*
  correction is **`O(d^{−2/3})` relative — smaller** than the OQ's stated
  `O(ln d / d^{1/3})`.
- **MC spot-check** (seeded, not exhaustive) at `d = 365`: `P(triple)` reaches
  ~0.46 only by `n ≈ 84`, so the exact median sits a few **above** `n₀ = 82.1`.
  This shows the true correction is **positive and non-negligible at human
  scale** — `d = 365` is far from the asymptotic regime where
  `d^{1/3} ≫ ln d`.

### Where the `O(ln d / d^{1/3})` term lives
It is the error of the Poisson approximation `P(triple) ≈ 1 − e^{−E}` versus the
exact occupancy probability. A rigorous bound is exactly a **Stein-Chen /
Chen-Stein Poisson approximation** estimate for the dependent indicator sum over
triples. It only becomes a *small* correction once `d^{1/3} ≫ ln d`
(astronomically large `d`), so it cannot be confirmed numerically at reachable
scales — the cert deliberately certifies leading order only and scopes this term.

### Mathlib bearers (surveyed master, 2026-06-14)
- PRESENT: `Archive/Wiedijk100Theorems/BirthdayProblem.lean` — only the **basic**
  finite birthday problem (Wiedijk #100, pairwise existence). No asymptotic
  threshold, no k-collision generalization.
- ABSENT: any Poisson/**Stein-Chen** approximation framework ("Stein Chen" search
  hits are the unrelated Chudnovsky π file); no occupancy/k-collision asymptotics.

## Milestone plan (re-scoped by S2)
- **M1** — formalize `E[#triples] = C(n,3)/d²` and the leading-order median
  `~(6 d² ln 2)^{1/3}` (the cert is the oracle). Self-contained, Docker-gated.
- **M2 (re-scoped, much smaller than S1 thought)** — formalize the elementary
  binomial-upper-tail expansion `E[W] = d·P(Bin(n,1/d)≥3) =
  (n³/6d²)(1 − 3/n − 3n/(4d) + …)` and solve `E[W]=ln2` to extract the
  `Θ(d^{−1/3})` correction with coefficient `c₀/4`. This needs **no Stein–Chen**
  — just binomial tail asymptotics (<300 lines). S1 over-scoped M2.
- **M3 (optional)** — a Stein–Chen bound for `P(W=0) − e^{−E[W]}` to rigorise the
  `o(d^{−2/3})` remainder. Genuinely new Mathlib infra, but NOT on the critical
  path for the second-order term.

## Next action
M1+M2 are the tractable Lean targets (Docker-gated); the second-order correction
is now an elementary-asymptotics target, not a Stein–Chen one. Re-run the two
certs as oracles. M3 only if the `o(d^{−2/3})` remainder is later wanted.
