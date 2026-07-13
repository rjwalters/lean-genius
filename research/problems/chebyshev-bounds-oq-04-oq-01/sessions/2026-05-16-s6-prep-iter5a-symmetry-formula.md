# S6 — Iter 5a PREP: Selberg symmetry formula bearer manifest + scope honesty (doc-only)

**Date**: 2026-05-16T04:37Z
**Researcher**: researcher-9
**Phase**: PREP (Iter 5a planning, doc-only)
**Scope**: Pre-ACT manifest for Iter 5a (Selberg's symmetry formula `Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`). Absorbs Iter 4 ACT merge (PR #19400 at 2026-05-16T03:52:02Z). 0 Lean changes; sessions/ memo + state.md head replacement + slug JSON refresh.

## §0 Summary

This PREP **does not ship Lean code**. It does three things:

1. **STATE-SYNC the Iter 4 merge**: state.md and slug JSON still say "this PR" / "PR pending" for Iter 4; PR #19400 merged 2026-05-16T03:52:02Z (~40min before this PREP). The notation is updated to MERGED with the PR# and timestamp.
2. **Bearer manifest** for Iter 5a's analytic infrastructure at the current Mathlib pin (`v4.26.0` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): what exists, what does not, where each lemma lives.
3. **Scope honesty**: the Iter 4 session memo (`2026-05-16-s5-iter4-act-moebius-log-literal.md` §7) estimated Iter 5a at **80–120 LOC**. After surveying Mathlib for the two main missing pieces (Mertens bound `Σ μ(d)/d = O(1)` and the asymptotic `Σ (log m)² = x · (log x)² − 2x · log x + 2x + O(log² x)`), a more honest estimate is **150–230 LOC across three sub-steps**, with a recommendation to split Iter 5a into **5a-α / 5a-β / 5a-γ**.

## §1 Pre-claim survey

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open` at session start returned **0 OPEN PRs**:

| PR | Status | Resolved at | Touch list |
|---|---|---|---|
| #19400 (Iter 4 ACT) | MERGED | 2026-05-16T03:52:02Z | `ChebyshevBoundsOQ04OQ01.lean` +24/-11 (selbergLambda2_eq_moebius_log_sq), state.md +56/-46, slug JSON, meta.json, sessions/ memo |
| #19171 (S4 PREP) | MERGED | 2026-05-15T22:56:46Z | doc-only PREP for the literal Möbius–log form (consumed by Iter 4) |
| #19092 (Iter 3 ACT) | MERGED | 2026-05-15T22:59:33Z | dual identity `Σ Λ₂(d) = (log n)²` + 3 thm + 2 parent v4.26.0 fixes |

The Iter 4 work is **finished and merged** — algebraic core of the Selberg–Erdős 1949 strategy is complete (both dual `Σ Λ₂(d) = (log n)²` and literal `Λ₂(n) = Σ μ(d) log²(n/d)` forms now exist as theorems in the slug file).

`origin/main` HEAD at session start: `78448f56d0a` (post-birthday-problem S5 STATE-SYNC). The slug Lean file `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` is at 325 LOC / 16 theorems / 3 noncomputable defs / 0 sorries / 0 axioms (Iter 4 final state). Parent `proofs/Proofs/ChebyshevBoundsOQ04.lean` is at 386 LOC with one open axiom `chebyshevPsi_asymptotic` (the elementary PNT terminal goal).

`proofs/lake-manifest.json` Mathlib `rev` field: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (same as Iter 4). The Mathlib pin has not moved since Iter 2 (2026-05-13).

## §2 STATE-SYNC: absorb Iter 4 merge

### Stale notation in state.md (pre-PREP)

Lines 21 and 198 of `state.md` referred to Iter 4 as "this session, PR pending" and "this Iter 4" respectively, written from the perspective of researcher-6's Iter 4 ACT session (~40min before this PREP claim). The phase line (line 5) and iteration counter (line 6) already reflect post-Iter 4 state correctly — only the **iteration log block** for Iter 4 and the **Race awareness block** were stale.

### Stale notation in slug JSON (pre-PREP)

`src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`:

- `currentState.focus` describes Iter 4 as "(this PR)" — needs PR# reference.
- `currentState.since` is `2026-05-16T03:00:00.000Z` (Iter 4 session start) — should be advanced to this PREP session start `2026-05-16T04:37:00.000Z`.
- `currentState.attemptCounts.total = 4` is correct (Iter 1+2+3+4); this PREP is bookkeeping, not a new attempt, so `total` stays at 4 (next ACT will be Iter 5a, which will bump to 5).
- `lastUpdate = 2026-05-16T03:00:00.000Z` is stale (Iter 4 session start, not Iter 4 merge); should be advanced to this PREP push time.

### Corrected narrative

**Iter 4 — MERGED at 2026-05-16T03:52:02Z as PR #19400**. Body delivered one new theorem `selbergLambda2_eq_moebius_log_sq` (+24 LOC body, +13 LOC docstring/sections, file 312 → 325 LOC). Docker-verified 7744/7744 jobs at base SHA `8a3cda556b6`. Sessions memo `2026-05-16-s5-iter4-act-moebius-log-literal.md` documents the 2-Docker-iteration build trap (`m : ℕ` annotation needed to prevent Lean inferring `m : ℝ` from `Real.log m`).

## §3 Iter 5a mathematical target

**Theorem statement** (informal):

```
∃ C : ℝ, ∀ N : ℕ, |selbergSum2 N - 2 * N * Real.log N| ≤ C * N    (N ≥ 2)
```

i.e. `selbergSum2 N = 2N · log N + O(N)`. This is the central analytic identity of the Selberg–Erdős 1949 elementary PNT proof.

**Lean signature sketch** (post-Iter 5a-γ assembly):

```lean
/-- Selberg's symmetry formula: the partial Selberg sum has leading term `2N · log N`
    with error `O(N)`. This is the central analytic input to the elementary PNT proof. -/
theorem selbergSum2_asymptotic :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |selbergSum2 N - 2 * (N : ℝ) * Real.log (N : ℝ)| ≤ C * (N : ℝ) := by
  sorry  -- assembled from Iter 5a-α (log² sum asymp) + Iter 5a-β (Mertens bound) + Möbius hyperbola
```

**Proof skeleton** (from Iter 4 session memo §7 + standard analytic-NT exposition, e.g. Tenenbaum I.6.2 + III.4):

Step 1. Sum Iter 4's identity over `n ≤ N`:

```
selbergSum2 N = Σ_{n ≤ N} Σ_{d ∣ n} μ(d) · (log (n/d))²
              = Σ_{d ≤ N} μ(d) · Σ_{m ≤ N/d} (log m)²     (Möbius hyperbola; sum swap)
```

Step 2. Use the inner-sum asymptotic (Iter 5a-α):

```
Σ_{m ≤ x} (log m)² = x · (log x)² − 2x · log x + 2x + O(log² x)
```

Substitute with `x = N/d`:

```
selbergSum2 N = Σ_{d ≤ N} μ(d) · ((N/d) · (log (N/d))² − 2(N/d) · log (N/d) + 2(N/d) + O(log²(N/d)))
```

Step 3. Expand `log (N/d) = log N − log d` and group by the `log N` powers. The leading-term in `N · log N` comes from the `−2(N/d) · log (N/d)` cross-term times the Mertens bound `Σ_{d ≤ N} μ(d) / d = O(1)`:

```
−2N · Σ_{d ≤ N} (μ(d)/d) · (log N − log d) = −2N · log N · O(1) + 2N · Σ_{d ≤ N} (μ(d)/d) · log d
```

With Mertens' theorem M2 `Σ_{d ≤ N} (μ(d)/d) · log d = O(1)` (a sharper variant of the standard M1 `Σ μ(d)/d = O(1)`), the *negative* leading `−2N log N · O(1)` term is matched by the positive contribution from `(N/d) · (log (N/d))²` expansion — the standard sign-cancellation that produces the **+2N · log N** asymptotic (cf. Tenenbaum III.4 Theorem 4.1).

## §4 Mathlib bearer manifest at v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

### §4.1 Iter 4 bearers (post-merge drift recheck)

| Lemma | File:Line | Form | Status |
|---|---|---|---|
| `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240` | `[NonAssocRing R]` iff between `∑ i ∈ n.divisors, f i = g n` and `∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n` | **stable — 0 drift** from Iter 4 cited line |
| `Nat.sum_divisorsAntidiagonal` (via `@[to_additive]` on `prod_divisorsAntidiagonal`) | `Mathlib/NumberTheory/Divisors.lean:543` | `∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.divisors, f i (n / i)` | **stable — 0 drift** from Iter 4 cited line |

Pin confirmed via `gh api .../contents/Mathlib/.../...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The Iter 4 bearer pins remain authoritative.

### §4.2 Iter 5a candidate bearers (Abel-summation route)

| Lemma | File:Line | Signature | Role for Iter 5a-α |
|---|---|---|---|
| `sum_mul_eq_sub_sub_integral_mul` | `Mathlib/NumberTheory/AbelSummation.lean:129` | `c : ℕ → 𝕜`, `f : ℝ → 𝕜`, `[RCLike 𝕜]`; `0 ≤ a`, `a ≤ b`; `DifferentiableAt`/`IntegrableOn deriv` hyps; conclusion `Σ_{a ≤ k ≤ b} c(k) · f(k) = ...sub-sub-integral form...` | general Abel summation between two `ℝ` endpoints |
| `sum_mul_eq_sub_sub_integral_mul'` | `Mathlib/NumberTheory/AbelSummation.lean:175` | as above but `n m : ℕ`, `n ≤ m` | **likely first-choice bearer** for `Σ_{m ≤ N} (log m)²` once we identify the convenient `c, f` factorisation |
| `sum_mul_eq_sub_integral_mul` | `Mathlib/NumberTheory/AbelSummation.lean:189` | specialisation `a = 0` | useful since Selberg sums begin at `n = 1` (or `n = 0` with `Λ₂(0) = 0`) |
| `sum_mul_eq_sub_integral_mul'` | `Mathlib/NumberTheory/AbelSummation.lean:200` | as above with `m : ℕ` endpoint | drop-in for `selbergSum2 N` |
| `sum_mul_eq_sub_integral_mul₀` | `Mathlib/NumberTheory/AbelSummation.lean:211` | specialisation `c 0 = 0` | applicable since `selbergLambda2 0 = 0` (Iter 1 lemma `selbergLambda2_zero`) |
| `sum_mul_eq_sub_integral_mul₀'` | `Mathlib/NumberTheory/AbelSummation.lean:229` | as above with `m : ℕ` endpoint | **strongest candidate** if our final Iter 5a-γ assembly wants Selberg-Erdős-style splitting |

### §4.3 Iter 5a candidate bearers (Sum/Integral comparison route)

| Lemma | File:Line | Signature | Role for Iter 5a-α / 5a-β |
|---|---|---|---|
| `AntitoneOn.integral_le_sum` | `Mathlib/Analysis/SumIntegralComparisons.lean:81` | `f` antitone on `Icc x₀ (x₀+a)`; `∫ f ≤ Σ f` | bounds `∫ log²` from above by sum (wrong direction for log²; `log² x` is monotone on `[1, ∞)`) |
| `MonotoneOn.integral_le_sum_Ico` | `Mathlib/Analysis/SumIntegralComparisons.lean:195` | `f` monotone on `Icc a b`; `∫_a^b f ≤ Σ_{k ∈ Ico a b} f(k)` | **applicable bound**: `∫_1^N (log t)² dt ≤ Σ_{k ∈ Ico 1 (N+1)} (log k)²` (with the shift) |
| `MonotoneOn.sum_le_integral_Ico` | `Mathlib/Analysis/SumIntegralComparisons.lean:185` | `f` monotone; `Σ_{k ∈ Ico a (b-1)} f(k) ≤ ∫_a^b f` (roughly; check sign) | **dual bound** for the integral asymptotic |

These give the integral-bound side; the explicit `∫_1^N (log t)² dt = N · (log N)² − 2N · log N + 2N − 2 · (log N − 1)` (closed form, no asymptotic notation) comes from `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean` (closed-form integrals of `log` and `log²`, search for `integral_log`).

### §4.4 Iter 5a missing infrastructure (Mathlib gaps)

| Need | Mathlib status | Sketch of needed work |
|---|---|---|
| `Σ_{m ≤ x} (log m)² = x · (log x)² − 2x · log x + 2x + O(log² x)` | **MISSING** (no `sum_log_sq`-style lemma) | Abel-summation against `f(t) = (log t)²` with `c(n) = 1`, integrating `2 log t / t` for `f'`. ~25-40 LOC if Abel-summation bearers cooperate. |
| `Σ_{d ≤ N} μ(d) / d = O(1)` (Mertens M1) | **MISSING** (`docs/1000.yaml` lists "Mertens's theorems" as TODO) | One of the three classical Mertens theorems. Proof via `M(N) := Σ μ(d) = o(N)` (Prime Number Theorem!) gives M1, but that's circular. Elementary route: Σ μ(d)/d → 0 follows from |Σ_{d ≤ x} μ(d)| ≤ x with summation by parts; weak bound `|Σ μ(d)/d| ≤ 1 + log x` is elementary. ~30-50 LOC for the weak bound. |
| `Σ_{d ≤ N} (μ(d)/d) · log d = O(1)` (Mertens M2) | **MISSING** | Sharper variant; needed for the leading-term cancellation in Iter 5a-γ. ~30-50 LOC. |
| Selberg symmetry formula assembly | **MISSING** (this is what we're building) | Combines the above + Möbius hyperbola swap + `log_div` expansion. ~40-60 LOC. |

### §4.5 Mathlib has `Chebyshev.psi` and `Chebyshev.theta` natively!

**Notable discovery** (surfaced during this PREP's bearer survey): `Mathlib/NumberTheory/Chebyshev.lean` (272 LOC, upstreamed from PrimeNumberTheoremAnd) defines:

```lean
noncomputable def Chebyshev.psi (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n
noncomputable def Chebyshev.theta (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p
```

with `Chebyshev.psi_le_const_mul_self : ψ x ≤ (log 4 + 4) * x` and `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` already proven. This is an upper bound `ψ(x) ≤ O(x)` but **not** the asymptotic `ψ(x) ~ x`.

**Implications for OQ-04-OQ-01 architecture**:

1. The parent file `ChebyshevBoundsOQ04.lean` defines its own `chebyshevPsi` and axiomatises `chebyshevPsi_asymptotic`. This pre-dates the Mathlib upstream and is **not blocked** by it — the Mathlib `Chebyshev.psi` is a *plain* `ℝ`-indexed function with `Ioc 0 ⌊x⌋₊` while our parent likely uses an `ℕ`-indexed sum. The two definitions are equivalent but typed differently.

2. **No rewrite is required for Iter 5a–7+** — we will continue to work with the slug's `selbergSum2 (N : ℕ) : ℝ := Σ_{n ∈ range (N+1)} selbergLambda2 n`. Re-routing through `Chebyshev.psi` would require an `ℕ ↔ ℝ` translation lemma and is **strictly more work** than the direct route.

3. **Recommendation for a future iter (Iter 7+ Tauberian step)**: when discharging the parent's `chebyshevPsi_asymptotic` axiom, consider bridging `parent.chebyshevPsi` ↔ `Chebyshev.psi` as a single conversion lemma so that downstream `Chebyshev.*` API (e.g. `psi_le_const_mul_self`, `abs_psi_sub_theta_le_sqrt_mul_log`) is directly usable. This is a 2-LOC bridge if the underlying sums match.

This is a **side note**, not a course correction for Iter 5a. The Selberg–Erdős elementary route remains the right strategy for OQ-04-OQ-01.

## §5 Honest scope statement & recommended split

The Iter 4 session memo (`2026-05-16-s5-iter4-act-moebius-log-literal.md` §7) estimated Iter 5a at **80–120 LOC**. After the §4.4 bearer survey, that estimate is **too optimistic** by roughly **2×**. A more honest budget:

| Sub-iter | Deliverable | Estimated LOC | Estimated Docker iters | Risk |
|---|---|---|---|---|
| **5a-α** | `Σ_{m ≤ N} (log m)² = N · (log N)² − 2N · log N + 2N + O(log² N)` (cleaner: a witnessed `Σ - leading_terms` bound) | 60–90 | 2–4 | medium (integration-by-parts elaboration in Lean; `log` differentiation at `1`) |
| **5a-β** | `\|Σ_{d ≤ N} μ(d) / d\| ≤ 1 + Real.log N` (weak Mertens M1; sufficient for the `O(1)` use in 5a-γ) | 50–80 | 2–3 | medium (`M(N) := Σ μ(d)` bound — `\|M(N)\| ≤ N` is `abs_sum_le_sum_abs` + `Int.abs_moebius_le_one`; summation by parts) |
| **5a-γ** | Möbius hyperbola sum swap + assembly into `\|selbergSum2 N − 2N · log N\| ≤ C · N` | 40–60 | 2–4 | high (sign cancellation; coefficient bookkeeping; `log_div` expansion sensitivity) |
| **Total Iter 5a** | Selberg's symmetry formula | **150–230 LOC** | **6–11** Docker iters | overall high |

### §5.1 Why split

1. Each sub-iter is a self-contained mathematical statement with a clean acceptance criterion (Docker-clean + sorry/axiom count constant).
2. Sub-iters 5a-α and 5a-β are **independent** (could be parallelised across two researcher sessions).
3. 5a-γ depends on both 5a-α and 5a-β, so its claim should wait until both predecessors merge — but if 5a-α merges first, a separate researcher can begin 5a-γ assembly using a `sorry`-stub for the 5a-β bearer.
4. Splitting also limits Docker rebuild churn — each sub-iter touches the slug file by 30-80 LOC, not 150-230, reducing the cache-invalidation footprint per round-trip.

### §5.2 Alternative: monolithic Iter 5a (NOT recommended)

A single ~200-LOC ACT submission would:
- Have a high merge-conflict risk if another researcher claims the slug between sessions.
- Require ~6-11 Docker iterations all bundled into one session (~30-60min of build time, plus elaboration debug).
- Bury the three independent technical contributions (asymptotic, weak-Mertens, sign-cancellation assembly) in a single diff, making PR review harder.

**Recommendation**: split into 5a-α / 5a-β / 5a-γ.

## §6 Iter 5a-α acceptance criteria (paste-ready for next ACT picker)

When a future session claims this slug for Iter 5a-α:

| Criterion | Target |
|---|---|
| Docker build | `[N/N] Built Proofs.ChebyshevBoundsOQ04OQ01` (currently 7744; expect 7744 + small) |
| New theorem | `sum_log_sq_asymptotic : ∀ N ≥ 2, |Σ_{m ∈ Icc 1 N} (Real.log m)² − (N · (Real.log N)² − 2N · Real.log N + 2N)| ≤ C · (Real.log N)²` (witnessed `C` or as `IsBigO`) |
| File LOC delta | +60 to +90 |
| Theorem count | 16 → 17 (or 18 if a helper lemma is exposed) |
| Sorries | 0 → 0 (no new sorries) |
| Axioms | 0 → 0 (no new axioms) |
| Mathlib bearer | At least one of `sum_mul_eq_sub_integral_mul₀'` (preferred) or `MonotoneOn.integral_le_sum_Ico` (fallback) |

## §7 Iter 5a-β acceptance criteria (paste-ready for next ACT picker)

| Criterion | Target |
|---|---|
| Docker build | `[N/N] Built Proofs.ChebyshevBoundsOQ04OQ01` |
| New theorem | `abs_sum_moebius_div_le : ∀ N ≥ 1, |Σ_{d ∈ Icc 1 N} (ArithmeticFunction.moebius d : ℝ) / d| ≤ 1 + Real.log N` |
| File LOC delta | +50 to +80 |
| Sorries | 0 → 0 |
| Axioms | 0 → 0 |
| Mathlib bearer | `ArithmeticFunction.moebius` (already imported), `Int.abs_moebius_le_one` for the `|μ(d)| ≤ 1` step (verify pin: `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`), `sum_mul_eq_sub_integral_mul₀'` for Abel summation |

## §8 Iter 5a-γ acceptance criteria (paste-ready, requires 5a-α + 5a-β merged)

| Criterion | Target |
|---|---|
| Docker build | `[N/N] Built Proofs.ChebyshevBoundsOQ04OQ01` |
| New theorem | `selbergSum2_asymptotic : ∃ C : ℝ, ∀ N ≥ 2, |selbergSum2 N − 2 * (N : ℝ) * Real.log (N : ℝ)| ≤ C * (N : ℝ)` |
| File LOC delta | +40 to +60 |
| Sorries | 0 → 0 |
| Axioms | 0 → 0 |
| Bearer (from this slug) | `selbergLambda2_eq_moebius_log_sq` (Iter 4) + `sum_log_sq_asymptotic` (5a-α) + `abs_sum_moebius_div_le` (5a-β) |
| Honest scope statement | This **does not** discharge the parent's `chebyshevPsi_asymptotic` axiom — it only establishes the symmetry formula. The Tauberian/Erdős combinatorial finishing argument is Iter 6+. |

## §9 Risks & mitigations

| Risk | Mitigation |
|---|---|
| Integration-by-parts in Lean (5a-α) is delicate at `t = 1` (where `log 1 = 0` simplifies but `deriv` of `(log t)²` needs `t > 0`) | Restrict to `Set.Ioi 1` or `Set.Ici 2` and handle `N = 1` separately as a base case |
| `IsBigO` vs witnessed `C` (5a-α, 5a-γ) | **Recommend witnessed `C`** — explicit constants are easier to chain in 5a-γ; `IsBigO` introduces filter algebra that adds friction |
| Mertens M2 (`Σ (μ(d)/d) · log d = O(1)`) not in PREP scope | 5a-β proves only M1 (`Σ μ(d)/d = O(1)`); the sign-cancellation in 5a-γ may need M2. If so, add a 5a-δ for M2 (~30-50 LOC) before 5a-γ. Defer the call until 5a-γ session execution |
| Bearer drift between PREP and ACT | Mathlib pin has been stable since 2026-05-13 (4 days). Re-pin via `gh api ... ?ref=<lake-SHA>` at each sub-iter ACT start |
| Race with another researcher claiming the slug | This PREP doesn't lock the slug — it only stages the plan. The lock is the `research/claims/chebyshev-bounds-oq-04-oq-01.lock` directory, released by this session at end |

## §10 No Lean changes in this PREP

Per the §0 scope: **0 Lean changes**. This PREP only modifies:

1. `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-16-s6-prep-iter5a-symmetry-formula.md` (new — this file)
2. `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (head replacement + Iter 4 MERGED log entry + S6 PREP log entry; preserve historical tail)
3. `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` (phase/since/iteration/lastUpdate/focus/nextAction/attemptCounts refresh; `knowledge.insights` += 1, `knowledge.nextSteps` refresh)

**Not touched**:

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` — Lean source frozen at Iter 4 post-merge state
- `proofs/Proofs/ChebyshevBoundsOQ04.lean` — parent file unchanged
- `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json` — gallery meta frozen at Iter 4 post-merge state (lineCount 325, theoremCount 16)
- Any sibling slug's content
- Any Mathlib content
- Any Aristotle companion file (the slug doesn't have one; the Λ₂ work is open mathematics)

## §11 Race awareness

`gh pr list -R rjwalters/lean-genius --state open --limit 20` at session start: 20 PRs open across 18 slugs; **0 touch any chebyshev file or this slug**. Pre-push re-check will re-run this query immediately before `git push`.

## §12 Iteration tally (post-PREP)

| Iter | Date | PR | Status | Deliverable |
|---|---|---|---|---|
| 1 | 2026-05-09 | #17658 | merged | Selberg-Erdős scaffold (Λ₂, S₂ defs + 10 routine lemmas) |
| 2 | 2026-05-12 | #17690 | merged | Prime-value lemmas |
| 3 | 2026-05-14 | #19092 | merged | Selberg dual identity `Σ_{d∣n} Λ₂(d) = (log n)²` |
| 4 | 2026-05-16 | #19400 | merged 03:52Z | Literal Möbius–log form `Λ₂(n) = Σ_{d∣n} μ(d)·log²(n/d)` |
| **S6 PREP** | **this** | **TBD** | **open (this PR)** | **Iter 5a bearer manifest + scope honesty (doc-only)** |
| 5a-α | next | — | not yet attempted | `Σ_{m ≤ N} (log m)² = N(log N)² − 2N log N + 2N + O(log²N)` |
| 5a-β | future | — | not yet attempted | `\|Σ μ(d)/d\| ≤ 1 + log N` (weak Mertens M1) |
| 5a-γ | future | — | not yet attempted | Selberg symmetry formula assembly |
| 6 | future | — | not yet attempted | Tauberian inequality `V(x) log x ≤ (2/x) Σ V(x/n) Λ(n) + O(1)` |
| 7+ | future | — | not yet attempted | Erdős combinatorial finishing argument; discharges `chebyshevPsi_asymptotic` |

## §13 Pre-push re-check checklist

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:

- [x] `gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`: 0 OPEN PRs.
- [x] Bearer drift recheck via `gh api ... ?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: Iter 4's Moebius:240 + Divisors:543 stable.
- [x] All JSON files validate via `python3 -m json.tool`.
- [x] No `proofs/` touches (PREP is strictly doc-only).
- [x] Worktree absolute paths used for all Write/Edit (per `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`).
- [ ] `gh pr list` re-run immediately before `git push` (deferred to push step).
