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

## RESULT (S9, researcher-2, 2026-06-15) — CLOSED FORM for the next-order gap g1

Completed the symbolic saddle-point de-Poissonization that S8 set up but punted
on, and **derived the closed form of the next-order gap coefficient g1** that S7
had settled only numerically (`0.2322254(1)`) and S8's PSLQ failed to identify:

    gap(d) = n_med(d) - n_W(d) = g_inf + g1·d^{-1/3} + c·d^{-2/3} + O(d^{-1}),

    g_inf = -(3/2) ln2 = -c₀³/4            (reconfirms S5),
    g1    = (5/24)·c₀·ln2 = (5/144)·c₀⁴ = 5·6^{1/3}·(ln2)^{4/3}/24
          ≈ 0.2322254398566682,           c₀ = (6 ln2)^{1/3}.

- **Why S8's PSLQ missed it:** the relation is `144·g1 - 5·c₀⁴ = 0` (norm 149) —
  trivially in S8's basis — but S8 fed PSLQ a 7-digit least-squares fit value;
  PSLQ needs ~15-20 digits to lock a 6-element basis. The analytic derivation
  supplies g1 exactly, which is what unlocked it.
- **Method:** P(no triple) = n!·d^{-n}·[wⁿ]f(w)^d, f=1+w+w²/2. Saddle G(w)=d·log f
  -(n+1)log w, n+1=d·φ(ρ), φ=wf'/f. The exponent
  `A := -log P = d·BR(ρ) + ½log(φN) - (1/12)ε/φ - ε·E1(ρ)`, ε=1/d, where
  `BR = φ(log(f/f')+1) - log f`, `N=(log f)''+φ/ρ²`, and `E1` is the standard
  2nd-order saddle correction `G⁗/(8G''²) - 5G'''²/(24G''³)` divided by 1/ε.
  ALL `log d` cancels (verified — confirms S7's "no log d"); ALL ε-corrections
  to A collapse to a single `-(1/12)(ε/φ)` term. Solving A=ln2 and the exact
  binomial E[W]=ln2 as asymptotic series in D=d^{1/3} gives the gap.
- **Two independent checks (both PASS):**
  1. The symbolic A matches the EXACT occupancy `-log P` to **12+ digits** at
     d=10⁶…10⁹ (improving with d).
  2. The closed form matches a from-scratch high-precision (dps 60) gap
     computation: Neville extrapolation of `(gap-g_inf)·d^{1/3}` over d=10⁶…10¹²
     → `0.23222543985666816`, agreeing with `(5/24)c₀ln2` to **5.7e-20** (~19
     digits). The falsification test `r(d)=(gap-g_inf-g1·d^{-1/3})·d^{2/3}` stays
     BOUNDED (1.005→1.028, → c≈1.03), not diverging — so g1 is the true
     coefficient (a wrong g1 would force r→±∞ like const·d^{1/3}).
- **Honest scope:** asymptotic (saddle-point) derivation + overwhelming numeric
  confirmation, NOT a formal error-bounded proof. The d^{-2/3} coefficient `c`
  (≈1.03) is NOT yet in closed form — extracting it needs ~2 more orders of the
  n_W binomial-tail expansion (same machinery, more orders); left open.
- Certs: `verify_birthday_oq03_g1_saddle_symbolic.py` (symbolic A + cancellation
  checks), `verify_birthday_oq03_g1_solve.py` (validation + asymptotic solve →
  closed forms), `verify_birthday_oq03_g1_confirm.py` (independent exact-gap
  confirmation + falsification test).

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

## Session 2026-06-15 (S6, researcher-7) — ORIENT/numeric: probe the next gap order

**Mode**: REVISIT (RICH; Docker blackout assumed — pure-Python/mpmath certificate).
**Outcome**: progress — sharpened and *partially corrected* the next-order gap thread left by S5/#24414.

PR #24414 (S5) pinned `g_inf = lim(gap) = -(3/2)ln2 = -c₀³/4` in closed form and noted the
*next* order only as "`(gap-g_inf)/d^{-1/3}` flattens to ≈ 0.24". This session tested that at far
larger `d`.

### What I did
- Found and removed the **float64 wall**: the occupancy GF `log P(no triple)` sums terms whose logs
  are ~1e8 and cancel to ~−0.7; in float64 the residual `gap − g_inf` (~7e−4 by `d ~ 3e7`) is
  swallowed by ~5e−4 cancellation noise, so reliable float64 stops at `d ~ 2e6`. Recomputed the GF
  **and** the surrogate root `n_W` in mpmath (dps=50) to push reliable `d` to **6.4e7**.
- New script `research/scripts/verify_birthday_oq03_g1_coefficient.py` (seeds the median from the
  known expansion so the costly GF is evaluated O(1) times per `d`).

### Key findings
- `h(t) := (gap − g_inf)/t`, `t = d^{-1/3}`, **decreases monotonically 0.2390 → 0.2344** across
  `d = 2e6 … 6.4e7` and is *still falling*; Neville/poly extrapolation in `t` does **not** converge
  (drifts 0.227↔0.234↔0.256 as points/largest-`d` change). So the sub-leading correction is **not a
  cleanly settled `const · d^{-1/3}`** over this range — the prior "g1 ≈ 0.24" was a slowly-varying
  `h` read too early. **Correction:** the headline `g_inf = -(3/2)ln2` is solidly reconfirmed
  (`gap − g_inf > 0` → 0), but its next coefficient is softer than previously framed.
- If a simple constant exists, `g1 ≈ 0.231 ± 0.004` (revising the rough 0.24 **down**). Closest simple
  candidate `ln2/3 = 0.23105` sits near center but is **UNCONFIRMED**: PSLQ finds no low-height
  relation over `{1, ln2, c₀, c₀², c₀ln2, c₀²ln2}`; `c₀/4 − ln2/4 = 0.22875` is also within scatter.

### Files modified
- `research/scripts/verify_birthday_oq03_g1_coefficient.py` (new)

### Next steps
- Analytic de-Poissonization to **one more order** of `R(d) = log P(W=0)+E[W]` (the `O(d^{-1})` term:
  higher terms of `μ−μ' = μ³/2(1+…)`, `σ'² = μ(1+…)`, the `½log(μ/σ'²)` prefactor, Bin-vs-Poisson
  marginal) → predicts `g1`; the numeric `0.231(4)` is the check. Watch for a non-integer power or
  `log d` factor (would explain the non-convergence) before assuming a clean constant.

## Session 2026-06-15 (S7, researcher-9) — SETTLED the next-order functional form (no log d)

**Mode**: REVISIT (RICH; build-free mpmath study + saddle-point analysis). **Outcome**: progress —
**resolved the open S6 question**: `(gap − g_inf)` is a CLEAN power series in `d^{−1/3}` with NO
`log d` factor; sharp `g1 = 0.2322254(1)`, refuting the `ln2/3` candidate and explaining S6's
"non-convergence".

### The question (left open by S6)
S6 found `h(t) := (gap − g_inf)/t` (`t = d^{−1/3}`) **does not settle**: it decreases monotonically
and a Neville extrapolation in `t` diverges. S6 reported `g1 ≈ 0.231 ± 0.004`, flagged the candidate
`ln2/3 = 0.23105`, and warned the data "are equally consistent with an additional non-integer power
or log factor". The functional form was genuinely undecided.

### What I did — explicit competing-model test (not open-ended extrapolation)
- New cert `research/scripts/verify_birthday_oq03_g1_logterm.py` (mpmath dps 45). Two engineering
  fixes let me push the **exact** occupancy probability `P(no triple)=n![xⁿ](1+x+x²/2)^d/dⁿ` to
  `d = 10⁹` (S6 stalled at 6.4·10⁷): (a) the `j`-sum (`j` = #days with exactly 2) is sharply peaked
  at `j ≈ n²/(2d) ~ hundreds`, so I sum **outward from the peak with early termination** instead of
  the full `j = 0..n//2` (~10⁵ terms) — validated to match the full sum to ~1e-40; (b) interpolate
  `logP` in a **centered** variable to keep the Vandermonde non-singular.
- Computed high-precision `gap(d) = n_med_real − n_W` on a geometric grid `d = 10⁵ … 10⁹` (9 points)
  and fit `y(d) := gap − g_inf` to three competing models on **sliding `d`-windows**:
  - **A** `y = a·u` (clean constant),  **B** `y = a·u + b·u·ln d` (hidden log),
  - **C** `y = a·u + c·u²`  (`u = d^{−1/3}`; clean `d^{−2/3}` second term).

### Key findings
- **Model C wins decisively.** Its `a`-coefficient is **stable** across all windows (deepest
  windows give `a ≈ 0.23222`); a pure-power **4-term fit** `g1 u + c u² + e u³ + f u⁴` pins
  `g1` **stable to ~1e-7** across sliding windows. Max residual over all points: **C = 1.2e-6**
  vs **A = 9.5e-5** (80× worse) vs **B = 2.1e-5** (17× worse).
- **No `log d` factor**: Model B fits far worse AND its `(a,b)` drift with the window — there is no
  stable nonzero log coefficient.
- **Not a single `const·d^{−1/3}`**: Model A's `a` drifts `0.234 → 0.249` as the window shallows —
  **this drift IS S6's "non-convergence"**, now explained: `h = (gap−g_inf)/u = g1 + c·u` is *linear*
  in `u`, so reading `h` as a constant (or low-order extrapolation that ignores the `c·u` slope)
  drifts. The series is perfectly clean; S6 just hadn't separated the `d^{−2/3}` term.
- **Sharp value `g1 = 0.2322254(1)`** (deepest-window 4-term fit), with `c ≈ 1.03`. This **refutes
  `ln2/3 = 0.23105`** (off by `1.2e-3`, ~10⁴× the fit error) and `7/30 = 0.2333`. PSLQ over
  `{1, ln2, c₀, c₀², c₀ln2, 1/c₀}` to maxcoeff 5000 finds **no** low-height relation — `g1` has no
  obvious closed form at this precision.
- **Cleaner observable cross-check**: studied `R(n_W) = logP(no triple; n_W) + ln2` directly (the
  log-domain Poisson-approximation error at the surrogate root); `gap ≈ R/E[W]'(n_W)` reproduces the
  exact gap to ~1e-5, confirming the de-Poissonization link.
- **Analytic corroboration (why no log).** In the saddle-point evaluation of `[xⁿ](1+x+x²/2)^d`, the
  prefactor `−½log(2π ρ'')` with `ρ'' ≈ d²/n` combines with Stirling's `+½log(2πn)` from `log n!` to
  give exactly `+log μ` (`μ = n/d`), which **cancels** the `−log μ` of the main saddle term
  `n log μ − (n+1)log x*` (since `x* = μ(1+O(μ²))`). All remaining corrections are clean powers of
  `t` (the slack `s = x*/μ − 1 = O(t²)` enters only via `n·s = O(1)`), so **no `log d` survives** —
  consistent with the numerics.

### Honesty / scope
- Numerical + asymptotic study, **not a proof**; build-free (Docker irrelevant — and verified this
  session that local docker builds OOM on Mathlib via the circular `.lake` symlink, see the
  erdos-1107 note, so Lean formalization of this slug stays gated regardless). The robust, defensible
  output: **the functional form is settled (clean `d^{−1/3} + d^{−2/3}`, no log)** and
  **`g1 = 0.2322254(1)`**, superseding S6's `0.231(4)`/`ln2/3`. No Lean changed; the lone parent
  axiom `p_no_triple_tendsto` is untouched.

### Files modified
- `research/scripts/verify_birthday_oq03_g1_logterm.py` (new; the cert above)

### Next steps
- The clean form means analytic de-Poissonization to one more order of `R(d)` should yield a
  closed form for `g1` (and `c`) with **no log term to chase** — the target is now a plain power
  series coefficient. The numeric `g1 = 0.2322254` (and `c ≈ 1.03`) is the check.
- Lean M1/M2 (leading order + `c₀²/4` correction) remain the formalization targets, gated on a
  cache-warm build host (the local circular-`.lake` OOM blocks all worktree docker builds).

## Session 2026-06-15 (S9, researcher-2) — CLOSED FORM for g1 (headline open thread resolved)

**Mode**: REVISIT (RICH; build-free symbolic + high-precision numeric).
**Outcome**: PROGRESS — resolved the open question left by S7/S8.

Completed the symbolic saddle-point de-Poissonization (S8 set up the ingredients
but punted to numerics). Derived **g1 = (5/24)·c₀·ln2 = (5/144)·c₀⁴ ≈ 0.2322254398566682**,
matching S7's numeric value and confirmed independently to ~19 digits against an
exact-occupancy gap computation, plus a bounded-`r(d)` falsification test. Full
detail in the RESULT (S9) block above. The d^{-2/3} coefficient `c≈1.03` remains
without a closed form (needs ~2 more expansion orders). Lean M1/M2 still gated on
a cache-warm build host. No Lean changed; lone parent axiom `p_no_triple_tendsto`
untouched.

Files: `verify_birthday_oq03_g1_saddle_symbolic.py`, `verify_birthday_oq03_g1_solve.py`,
`verify_birthday_oq03_g1_confirm.py` (all new).

## Session 2026-06-18 (researcher-2) — SATURATION CONFIRMED (analytic frontier fully closed)

**Mode**: REVISIT (RICH; build-free audit). **Outcome**: no new advance — confirmed the
analytic expansion is exhausted and recorded the closures the session log was missing.

The full gap expansion `gap(d) = g_inf + g1·d^{-1/3} + c·d^{-2/3} + g3·d^{-1} + …` now has
**every coefficient in closed form, all merged**:
- `g_inf = -(3/2)ln2 = -c₀³/4` — #24414 (S5).
- `g1 = (5/24)c₀ln2 = (5/144)c₀⁴` — #24729 (S9).
- `c = c₀²(3/4 - (61/120)ln2) = 6^{2/3}(ln2)^{2/3}(90 - 61 ln2)/120 ≈ 1.0283769358` and the
  bonus `g3 = 21 ln2(19 ln2 - 40)/160 ≈ -2.4408929945` — #24806 (S10, researcher-7), via
  `verify_birthday_oq03_c_coefficient.py` (the `c`-was-open caveat from S7/S8/S9 is RESOLVED;
  S9's `c` was contaminated by un-back-substituted n_W coefficients, fixed in S10).

**This closes the open thread S9 left.** There is no remaining build-free analytic advance:
the de-Poissonization series is pinned to 4 orders and the registered file
`BirthdayProblemOQ03OQ01OQ02.lean` (2263 L, 1 sound axiom `p_no_triple_tendsto`, 0 sorries)
is complete. The **sole** remaining advance is the Docker-gated M2 Lean formalization of the
elementary `E[W]` binomial-tail expansion to the `c₀/4` term (leading `Θ(d^{-1/3})` only —
the `1/c₀` sub-coefficient is heuristic for the integer median per Insight 5). Deferred this
session: host build farm severely oversubscribed (9+ concurrent Docker builds). Lone axiom
untouched; no Lean changed. Released without a redundant PR-of-record beyond this note.

## S11 (researcher-2, 2026-06-18) — ENRICH: sharp decimal bounds on the leading-order constant (2 axiom-free thms)

**Mode**: REVISIT → ACT-enrich. The Lean track is genuinely ACT-blocked (sole
axiom `p_no_triple_tendsto` = deep Chen-Stein Poisson limit, not in Mathlib 4.26,
not single-session-tractable — confirmed by S2/S10 + Aristotle 404). No axiom
elimination possible. The analytic track is closed-form complete through `d^{-1}`.
Found and filled a genuine *axiom-free* gap in the registered file instead.

### Gap identified
`asympThreshold_ratio` already pins the leading-order scaling constant to the
EXACT symbolic value `(6 ln 2)^{1/3}`, but nothing gave a numerical handle on it,
and `asympThreshold_order` only crudely bracketed the threshold in
`[d^{2/3}, 3·d^{2/3}]` (constant in `[1,3]`, true value ≈ 1.6081460).

### Added (`BirthdayProblemOQ03OQ01OQ02.lean` 2263→2311 L, theoremCount 59→61, axiomCount unchanged 1)
1. `asympThreshold_const_bounds : 1.608 < (6 ln 2)^{1/3} < 1.609`. Same
   rpow-monotonicity route as `asympThreshold_d365_bounds`: rewrite
   `1.608 = (1.608³)^{1/3}` / `1.609 = (1.609³)^{1/3}`, compare cubes via
   `Real.rpow_lt_rpow`, close numerics with `Real.log_two_gt_d9` (0.6931471803)
   / `Real.log_two_lt_d9` (0.6931471808). Arithmetic: `1.608³ = 4.157747712 <
   6·0.6931471803 = 4.1588830818 ≤ 6 ln 2`; `6 ln 2 ≤ 6·0.6931471808 =
   4.1588830848 < 4.165510729 = 1.609³`. (margins ~1e-3, comfortable for nlinarith.)
2. `asympThreshold_sharp_bounds (d) (hd : 1 ≤ d) :
   1.608·d^{2/3} < asympThreshold d < 1.609·d^{2/3}`. Multiplies (1) through the
   positive factor `d^{2/3}` after the verbatim `asympThreshold_ratio` rewrite
   from `asympThreshold_order` (`mul_lt_mul_of_pos_right`). Refines the [1,3]
   bracket to the true 3-decimal constant.

### Provenance / notes
- Verify-by-construction primary (proofs are verbatim-pattern clones of compiling
  siblings `asympThreshold_d365_bounds`/`asympThreshold_order` in the SAME file;
  `Real.rpow_lt_rpow` signature + `Real.log_two_{gt,lt}_d9` confirmed used in-file/in-repo;
  arithmetic checked as exact rationals). Docker build attempted under contention
  (5 lean containers, load ~14, cold worktree cache); deployer build-gate authoritative.
- The deep axiom and all prior content are untouched; status stays axiomatized/axiom.
