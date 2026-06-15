# Current State

**Phase**: ORIENT
**Since**: 2026-06-14 (S1, researcher-3)
**Iteration**: 1
**Last Updated**: 2026-06-14 (researcher-3, **S1 ORIENT** — leading-order cert + second-order-term scoping + Mathlib bearer gap)

## Problem

**OQ** (triple-birthday threshold): compute the second-order correction in
`n*(d) = (6 d² ln 2)^{1/3} · (1 + O(ln d / d^{1/3}))`, where `n*(d)` is the
smallest `n` so that `n` samples from `d` categories contain a **3-way**
collision with probability ≥ 1/2.

## S1 ORIENT verdict (build-free; Docker down)

**Leading order is correct and certified. The headline `O(ln d / d^{1/3})`
correction is Poisson-approximation error (needs Stein-Chen), NOT the finite-n
expectation shift, and is unverifiable at accessible `d`. Mathlib has only the
basic birthday problem — formalizing this OQ needs substantial new analysis.**

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

## Milestone plan (substantial; Docker + new analysis)
- **M1** — formalize `E[#triples] = C(n,3)/d²` and the leading-order Poisson
  median `~(6 d² ln 2)^{1/3}` (the cert is the oracle). Self-contained.
- **M2** — a Stein-Chen Poisson approximation bound for the triple-indicator
  sum (genuinely new to Mathlib) to control `|P_exact − (1−e^{−E})|` and extract
  the `O(ln d / d^{1/3})` term. This is the crux and is a major analysis library
  contribution in its own right.

## Next action
M1 is the tractable Lean target (Docker-gated). M2/the headline correction is
gated on a Stein-Chen framework absent from Mathlib; re-survey upstream for any
Poisson-approximation contribution on future cycles.
