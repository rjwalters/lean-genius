# Knowledge: birthday-problem-oq-03-oq-01-oq-02-oq-02 (triple-collision second-order threshold)

## Problem framing
Compute the second-order correction to the triple-birthday median threshold
`n*(d) = (6 d² ln 2)^{1/3}(1 + O(ln d / d^{1/3}))`, where `n*(d)` is the smallest
`n` so that `n` uniform samples from `d` categories contain a **3-way** collision
with probability ≥ 1/2.

## RESULT (S2, researcher-9) — exact second-order term

    n*(d) = (6 d² ln 2)^{1/3} · ( 1 + (c₀/4) d^{−1/3} + (1/c₀) d^{−2/3} + o(d^{−2/3}) ),
    c₀ = (6 ln 2)^{1/3} ≈ 1.608146.

- **The correction is Θ(d^{−1/3}) with NO logarithm**; the OQ's `O(ln d/d^{1/3})`
  is a loose upper bound. Exact leading coefficient **`c₀/4 ≈ 0.402037`**.
- It is a **deterministic first-moment effect** (the "boxes-vs-triples" gap),
  not a Poisson-approximation fluctuation.
- Certified `ε·d^{1/3} → c₀/4` over `d = 10²…10¹¹` and gap
  `(n_W − n_X)/d^{1/3} → c₀²/4 = 0.64653`.

## Insight 1 — Leading order from the first-moment / Poisson median
Each unordered triple coincides w.p. `1/d²`; `E[#triples] = C(n,3)/d²`. Poisson
heuristic median `C(n,3)/d² = ln 2` ⟹ `n ~ (6 d² ln 2)^{1/3}`. Certified
`d=10²…10¹²`. (Leading order — unchanged from S1.)

## Insight 2 — CORRECT Poisson parameter is E[W], not E[X] (corrects S1)
`P(no triple) = P(W=0)`, `W = #{days with ≥3 people}` — a sum of nearly
independent rare indicators over the `d` days, so `P(W=0) ≈ e^{−E[W]}` and the
median solves **`E[W] = ln 2`**. S1 instead solved `E[X] = ln 2` with
`X = #colliding triples`; but `C(m,3) ≥ 1[m≥3]` ⟹ `E[X] ≥ E[W]`, so the
`E[X]` root `n_X` **undershoots** the median by `(c₀²/4) d^{1/3}`. S1
mis-attributed this gap to "Poisson-approximation error / Stein–Chen"; it is a
deterministic first-moment difference. The genuine Poisson approximation (with
parameter `E[W]`) tracks the exact integer median to **O(1)** across all tested
`d` — Stein–Chen is NOT needed for the second-order term.

## Insight 3 — The expansion
`E[W] = d·P(Bin(n,1/d)≥3) = (n³/6d²)(1 − 3/n − 3n/(4d) + …)`. Setting
`E[W] = n₀³/(6d²)`, `n = n₀(1+ε)` ⟹ `ε = 1/n₀ + n₀/(4d) + …`, i.e.
`ε·d^{1/3} = (1/c₀)d^{−1/3} + c₀/4 + …`. The `n₀/(4d) ~ (c₀/4)d^{−1/3}` term
dominates the `1/n₀ ~ (1/c₀)d^{−2/3}` finite-`n` shift S1 found.

## Insight 4 — Mathlib bearer gap (re-scoped from S1)
Only `Archive/Wiedijk100Theorems/BirthdayProblem.lean` (basic pairwise problem).
No occupancy/k-collision asymptotics, no Stein–Chen. **But the second-order
correction needs only an elementary binomial-upper-tail expansion of `E[W]`
(<300 lines, Docker-gated), NOT Stein–Chen** — S1 over-scoped this. Stein–Chen
is only for the `o(d^{−2/3})` remainder `P(W=0) − e^{−E[W]}` (numerically tiny).

## Open threads
- (Docker up) Formalize M1 (leading order) + the `E[W]` expansion to `Θ(d^{−1/3})`.
- Keep the Poisson limit (`p_no_triple_tendsto`-style) axiomatised; the
  coefficient claim refines the same deferred limit.

## Links
- Parent chain: [[birthday-problem-oq-03-oq-01-oq-02]].
- Sibling deferral: [[birthday-problem-oq-03-oq-01-oq-02-oq-01]].
- Same durable-verify / honest-scoping vein as
  [[project-researcher-3-20260614m-konigsberg-matrixtree-orient]].

---

## Session 2026-06-14 (S1, researcher-3) — ORIENT (superseded in part by S2)
Certified leading order; identified Mathlib gap. Attributed the headline
correction to Poisson-approximation error / Stein–Chen via the `E[X]=ln2`
median. S2 corrects this: the correct median uses `E[W]=ln2`, the gap is a
first-moment effect of order `d^{−1/3}`, coefficient `c₀/4`, no log.
Original script `verify_triple_threshold.py` retained.

## Session 2026-06-14 (S2, researcher-9) — ORIENT
Derived + certified the exact second-order term `Θ(d^{−1/3})`, coeff `c₀/4`;
corrected S1's Stein–Chen framing; re-scoped M2. Scripts
`verify_birthday_oq03_second_order.py`, `verify_birthday_oq03_correction_coeff.py`.
Full detail: `sessions/2026-06-14-s2-orient.md`.
