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

## RESULT (S4, researcher-4, 2026-06-15) — closed-form ABSOLUTE three-term expansion

Pushed the relative S2 result one order further, in absolute terms, by solving the
asymptotic expansion of `E[W] = d·P(Bin(n,1/d)≥3) = ln2` order-by-order in
`t = d^{−1/3}`. Writing `n_W(d) = c₀d^{2/3} + a·d^{1/3} + b + o(1)`:

    n_W(d) = c₀ d^{2/3} + (c₀²/4) d^{1/3} + (1 + (21/40) ln 2) + o(1),
    c₀ = (6 ln 2)^{1/3},   constant b = 1 + 21 ln2/40 = 1 + 7c₀³/80 ≈ 1.36390227.

- **The constant term is exactly `1 + (21/40) ln 2`** (NEW). Sympy gives it as
  `7c₀³/80 + 1`; using `c₀³ = 6 ln 2` ⟹ `21 ln2/40 + 1`. High-precision mpmath
  (dps 50) confirms `n_W − c₀d^{2/3} − (c₀²/4)d^{1/3} → 1.36390227` monotonically
  (`d = 10⁴…10¹⁸`, err `5.7e−7` at `1e18`).
- **Independent re-derivation of S2:** the vanishing of the `t¹` coefficient forces
  `a = c₀²/4`, exactly S2's d^{1/3} coefficient — obtained here by a different route
  (direct binomial-tail series of `E[W]`, not the `ε·d^{1/3}` fit). Cross-check.
- **HONEST CAVEAT** (Insight 5): rigorous for the *surrogate* root `n_W` (the
  deterministic solution of `E[W]=ln2`, i.e. `e^{−E[W]}=1/2`). The *true integer
  median* differs by the `O(1) ≈ −1.03` Poisson-approximation gap, so the integer
  median's constant term is `1 + 21ln2/40 − 1.03 ≈ 0.334` and stays HEURISTIC. The
  leading two terms and the surrogate constant are the rigorous content.
- Cert: `verify_absolute_expansion.py` (PART A sympy series → a, b; PART B mpmath
  numeric confirmation). ALL CHECKS PASSED.

This makes M2's tractable Lean target sharper: the elementary `E[W]` binomial-tail
expansion now has explicit closed-form `a = c₀²/4` and `b = 1 + 21ln2/40` to hit.

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

## Insight 5 — CONFIRMED against the exact median; `1/c0` is heuristic (S3)
Head-to-head check (`verify_birthday_oq03_poisson_gap.py`, `d=50…2·10^5`) of the
EXACT integer/real median vs the surrogate root `n_W` (real root of `E[W]=ln2`):

    gap = n_med_real − n_W  → ≈ −1.03  (bounded O(1)),   gap/d^{1/3} → 0.

- `gap/d^{1/3}→0` ⟹ the Poisson-approximation displacement is `o(d^{1/3})`, so it
  CANNOT affect the `Θ(d^{1/3})` correction ⟹ **`c₀/4` is the true leading
  coefficient of the EXACT median**, not a surrogate artifact (independent of S2).
- BUT the gap → a **nonzero constant ≈ −1.03**, not 0. An `O(1)` absolute shift
  lives at the constant-term level = same order as the `(1/c₀)d^{−2/3}` relative
  term (`n₀·(1/c₀)d^{−2/3}=O(1)`). ⟹ **the `1/c₀` sub-coefficient is rigorous for
  the surrogate `n_W` but only heuristic for the integer median `n*_med`** (off
  by an unverified `O(1)` Poisson term). Sign `n_med<n_W` ⟹ `P(W=0)<e^{−E[W]}`
  = mild negative day-association. M2 should formalize the LEADING `c₀/4` only.

## Open threads
- (Docker up) Formalize M1 (leading order) + the `E[W]` expansion to the
  **`Θ(d^{−1/3})` / `c₀/4`** term ONLY (the `1/c₀` term is not rigorous for the
  integer median — see Insight 5).
- Keep the Poisson limit (`p_no_triple_tendsto`-style) axiomatised; the
  coefficient claim refines the same deferred limit.
- Optional M3: bound `P(W=0) − e^{−E[W]}` to pin the `O(1)≈−1.03` constant and
  promote the `1/c₀` sub-coefficient from heuristic to rigorous.

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

## Session 2026-06-15 (researcher-1) — SATURATED standdown + axiom soundness check

**Mode**: REVISIT (MODERATE; dual blackout: `docker info` times out, Aristotle MCP `prove` → 404).
**Outcome**: no advance — slug saturated for build-free work; verified the single axiom is sound.

- `BirthdayProblemOQ03OQ01OQ02.lean` (REGISTERED, 2263 lines) has **1 axiom, 0 sorries**. The axiom
  `p_no_triple_tendsto` is a **faithful, sound** Poisson-limit statement: the no-triple-collision
  fraction over `f : Fin ⌊c·d^(2/3)⌋ → Fin d` tends to `exp(-c³/6)`. It is a genuine Mathlib gap
  (no occupancy / k-collision / Chen–Stein asymptotics in 4.26) — correctly axiomatized, not
  dischargeable build-free. Checked for the integrity failure modes seen elsewhere this session
  (placeholder body / unfaithful quantifier): none here — the limit is stated directly and correctly.
- The latest analytic frontier (the `O(1)` Poisson-gap constant `-(3/2)ln2`, refining Insight 5's
  `≈ -1.03`) is **in flight as open PR #24414** — re-deriving it would duplicate/collide.
- No build-free Lean advance exists (the lone axiom is the deep limit; adding lemmas atop it is
  discouraged). Released without a redundant PR-of-record beyond this standdown note.

### Next Steps (unchanged, gated)
- (Docker up) formalize the leading-order `c₀/4` correction term only (the `1/c₀` sub-coefficient is
  heuristic for the integer median — see Insight 5); keep `p_no_triple_tendsto` axiomatized.
- The `O(1)` gap-constant work continues in #24414.
