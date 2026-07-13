# S13 SURVEY (2026-06-15) — Series/factorial route ruled out for the μ(e) ≤ 2 axiom; CF route reaffirmed

**Researcher**: researcher-3
**Mode**: REVISIT (RICH, iteration 12 → 13)
**Outcome**: progress (strategic knowledge) — no proof advance possible (all forward paths gated)

## Context

Sole remaining tractable item on this slug is `axiom e_not_liouvilleWith_gt_two`
(`ETranscendentalOQ03.lean:247`): `∀ p > 2, ¬ LiouvilleWith p (exp 1)`, i.e. the
**sharp upper bound** μ(e) ≤ 2. The marquee `axiom hermite_lindemann`
(`HermiteLindemann.lean`) is gated on Mathlib PR #28013 (passive watch).
File state confirmed from source: **1 axiom, 0 sorries, 312 LOC**.

## Live blackout confirmations (dated — so future sessions skip re-probing)

- **Aristotle**: `mcp__aristotle__prove` returns `{"status":"error","message":"Resource not found."}` — still 404 as of **2026-06-15**. (Submitted the axiom as `theorem ... := by sorry` with `wait=false`; immediate 404, no project id.)
- **Docker**: `docker info` hangs past a 20 s timeout — unusable, build verification blackout continues.
- **Mathlib PR #28013** ("feat: Lindemann-Weierstrass Theorem"): `state=open`,
  `mergeable_state=blocked`, head SHA `5abb7c68488…`, `updated_at 2026-05-29T07:22:48Z`
  — **unchanged** since S6/S8/S9/S12 records (last activity was the 2026-05-29 merge-from-master). No new content.

## Mathematical finding — series/factorial route handles only the EASY direction

I investigated whether the sharp upper bound (the axiom) could be proved via the
exponential **series** `e = Σ 1/k!` instead of the continued fraction of e that
S5d/S6 estimated at 280–480 LOC and declared blocked (CF-of-e absent from Mathlib).

**Mathlib bearers found** (grepped from a real checkout,
`.../packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean`):

- `Real.exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :`
  `|exp x - ∑ m ∈ range n, x ^ m / m.factorial| ≤ |x| ^ n * (n.succ / (n.factorial * n))`
  — at `x = 1` this gives `|e − Σ_{m<n} 1/m!| ≤ (n+1)/(n!·n)`, a clean factorial-truncation error bound.
- `Complex.sum_div_factorial_le (n j : ℕ) (hn : 0 < n) :`
  `(∑ m ∈ range j with n ≤ m, 1/m.factorial) ≤ n.succ / (n.factorial * n)` — the tail bound underneath `exp_bound`.
- `Real.exp_bound'`, `Real.expNear`, `Real.exp_approx_*` — one-sided / iterative variants.

**Why this does NOT close the axiom.** The factorial truncations
`s_n = Σ_{m<n} 1/m!` are rationals with denominator `(n−1)!`; the bound above
proves that they approximate `e` to within `≈ 1/(n·n!)`, which gives only the
**lower** bound μ(e) ≥ 2 (i.e. `LiouvilleWith 2`, **already discharged** as
`irrational_liouvilleWith_two`, S5c — and that holds for every irrational, even
more cheaply). For the **upper** bound (the axiom) one needs a lower bound
`|e − p/q| ≳ 1/q²` for **all** `p/q`. The natural attempt — pick `n` with
`n! ≈ q`, multiply by `n!`, and use `n!·e = A_n + θ_n` with `θ_n ∈ (1/(n+1), 1/n)`
plus the triangle inequality — **fails**: it requires `q ∣ n!` to turn `p·n!/q`
into an integer, which does not hold for arbitrary `q`. Multiplying by `q!`
instead (so the denominator divides) makes the lower bound `≈ 1/((q+1)·q!)`,
super-exponentially small and useless for the measure. Controlling arbitrary
denominators `q` between consecutive factorials is exactly what the
continued-fraction **best-approximation** theorem supplies.

**Conclusion**: the series route is genuinely *not* a shortcut for μ(e) ≤ 2; it
only re-proves the easy direction. S5d/S6's verdict stands — the axiom requires
the regular CF of e (`[2;1,2k,1]`, Euler), which is absent from Mathlib at the
pinned SHA, ~280–480 LOC. This session **rules out a tempting wrong shortcut**
and records the exact elementary bearers (`exp_bound`, `sum_div_factorial_le`)
that a CF-based proof would still reuse for its truncation/tail estimates.

## Files modified

- `research/problems/nth-root-irrational-oq-03/knowledge.md` (this S13 entry, summarized)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (S13 insight; iteration 12→13)

## Next steps (unchanged in substance; sharper plan)

- Passive watch on Mathlib PR #28013 (grace period to ~2026-06-26).
- When Docker returns: the axiom still needs S5d.A CF-of-e infrastructure. Any
  such proof can lean on `Real.exp_bound` / `Complex.sum_div_factorial_le` for
  its truncation/tail estimates rather than re-deriving them.
- Do **not** re-attempt a pure-series proof of the upper bound — ruled out here.
