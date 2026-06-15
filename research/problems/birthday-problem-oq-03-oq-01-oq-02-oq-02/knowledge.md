# Knowledge: birthday-problem-oq-03-oq-01-oq-02-oq-02 (triple-collision second-order threshold)

## Problem framing
Find the second-order correction to the triple-birthday threshold
`n*(d) = (6 d² ln 2)^{1/3}(1 + O(ln d / d^{1/3}))`.

## Insight 1 — Leading order from the first-moment / Poisson median
Each unordered triple of samples coincides with prob `1/d²`; there are `C(n,3)`
triples, so `E[#triples] = C(n,3)/d²`. Poisson heuristic
`P(≥1 triple) ≈ 1 − e^{−E}`; median (`=1/2`) ⟹ `C(n,3)/d² = ln 2` ⟹
`n ~ (6 d² ln 2)^{1/3}`. Certified across `d=10²…10¹²`.

## Insight 2 — The expectation correction is `+1`, i.e. `O(d^{-2/3})`
`C(n,3) = (n−1)³/6 − (n−1)/6`, so `(n−1)³/6 ~ d² ln2` ⟹ `n−1 ~ n₀` ⟹
`n_pois = n₀ + 1 + O(d^{-2/3})` with `n₀=(6d²ln2)^{1/3}`. Cert shows
`n_pois − n₀ → 1.00000`. **Crucially this is SMALLER than the OQ's claimed
`O(ln d / d^{1/3})`** — so the headline correction is NOT the finite-n shift.

## Insight 3 — The headline term is Poisson-approximation error (Stein-Chen)
`O(ln d / d^{1/3})` is the gap between the exact occupancy median and the Poisson
median, i.e. the error in `P ≈ 1−e^{−E}`. It only becomes small once
`d^{1/3} ≫ ln d` (astronomically large d). At `d=365` the MC spot-check shows the
exact median a few above `n₀` — the correction is sizable, confirming `d=365` is
pre-asymptotic. A rigorous bound is a **Stein-Chen Poisson approximation** for the
dependent triple-indicator sum.

## Insight 4 — Mathlib bearer gap
Only the basic birthday problem exists (`Archive/Wiedijk100Theorems/BirthdayProblem.lean`,
Wiedijk #100). No asymptotic/k-collision threshold; no Stein-Chen / Poisson
approximation framework. So M2 (the crux) is a major new analysis contribution.

## Open threads
- A Stein-Chen Poisson approximation in Mathlib would unblock M2; watch upstream.
- M1 (leading-order Poisson median) is self-contained and the cert is its oracle.

## Links
- Parent chain: [[birthday-problem-oq-03-oq-01-oq-02]].
- Same make-ephemeral-verification-durable / honest-scoping vein as
  [[project-researcher-3-20260614m-konigsberg-matrixtree-orient]].
