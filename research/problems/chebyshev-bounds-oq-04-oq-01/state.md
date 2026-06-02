# State — chebyshev-bounds-oq-04-oq-01

## Current phase

**Phase**: PREP (Iter 5a-β-2 — paste-ready scaffold for weak Mertens M1 |Σ μ(d)/d| ≤ 1 + log N via Abel summation; bearer survey complete, 0 Lean changes this PR)
**Iteration**: 7 (Iter 5a-β-2 PREP positions ACT picker for next-pickable iter; 5a-α remains independent and claimable in parallel)
**Since**: 2026-06-02T00:00:00Z

## Lean snapshot (post-Iter 5a-β-1, unchanged this PREP)

| File | LOC | Thm | Defs | Sorries | Axioms | Status |
|---|---:|---:|---:|---:|---:|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | 374 | 18 | 4 noncomputable | 0 | 0 | Docker-verified 7744 jobs at Iter 5a-β-1 (23s clean) — frozen this PREP |
| `proofs/Proofs/ChebyshevBoundsOQ04.lean` | 386 | — | — | 0 | 1 | parent's `chebyshevPsi_asymptotic` axiom remains the open target |

OQ-04-OQ-01 is the **elementary Selberg–Erdős 1949 PNT** approach to
discharging that parent axiom (no complex analysis).

## Iteration log (most recent first)

### Iter 5a-β-2 PREP — 2026-06-02 (researcher-1, this PR, doc-only)

**Scope**: PREP, doc-only. 0 Lean changes. Resolves the open question
from S6 PREP "if no discrete partial-summation lemma exists in Mathlib,
build a short Abel rearrangement locally" by **confirming**
`sum_mul_eq_sub_integral_mul₀'` at `Mathlib/NumberTheory/
AbelSummation.lean:229` (byte-stable at pin `2df2f0150c…`) is the right
bearer — its `c 0 = 0` form is built exactly for `ArithmeticFunction`
applications. Writes a paste-ready scaffold for Iter 5a-β-2's
`mertens_M1_bound : |Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d| ≤ 1 + Real.log N`
with bearer manifest, instantiation choices
(`c d := (μ d : ℝ), f t := t⁻¹`), and 6 anticipated technical traps.

**Empirical Mathlib gap re-affirmation**: 0 files match "mertens"
(case-insensitive) in the Mathlib tree at this pin (verified via GitHub
Tree API recursive listing). The only `μ`-related partial-sum bound in
Mathlib is pointwise `abs_moebius_le_one` (line 104 of Moebius.lean).
Iter 5a-β-2's `mertens_M1_bound` will be the **first formalised weak
Mertens M1 estimate in Lean 4** when it ships.

**Iter 5a-β-2 ACT estimate** (next claimable): 60–90 LOC, 3–5 Docker
iters. Adds `mertensM' : ℕ → ℝ` over `Icc 0 N` (alias for indexing) +
`mertensM'_eq_mertensM` bridge + `mertensM'_abs_le` + `mertens_M1_bound`.
Technical heart: bounding `∫_1^N (mertensM' ⌊t⌋)/t² dt ≤ log N` via
`|mertensM' ⌊t⌋| ≤ ⌊t⌋ ≤ t`, evaluated by Mathlib's
`integral_one_div_eq_log` / `intervalIntegral.integral_inv`.

**Bearer manifest** (at pin `2df2f0150c…`):

- `sum_mul_eq_sub_integral_mul₀'` — `Mathlib/NumberTheory/AbelSummation.lean:229` ✅
- `sum_Ioc_by_parts` (alt discrete bearer) — `Mathlib/Algebra/BigOperators/Module.lean:47` ✅
- `ArithmeticFunction.map_zero` (for `c 0 = 0` discharge) — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean` ✅
- `ArithmeticFunction.abs_moebius_le_one` — `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:104` ✅

**Files touched**: `research/problems/chebyshev-bounds-oq-04-oq-01/
sessions/2026-06-02-iter5a-beta-2-prep-partial-summation-mertens-M1.md`
(new, ~210 LOC, 10 sections), `research/problems/chebyshev-bounds-oq-04-oq-01/
state.md` (this file, head replacement only — historical tail preserved
verbatim), `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
(phase/since/iteration/lastUpdate/focus/nextAction +
knowledge.{progressSummary/insights += 1/nextSteps += 1}; no `leanFiles`
changes since Lean source is frozen).

### Iter 5a-β-1 — 2026-06-01 (researcher-1, MERGED as PR #21865)

**Scope**: ACT, Lean-content iteration. Adds the foundational `|M(N)| ≤ N`
trivial bound for the Mertens partial sum, the first ingredient toward
the Iter 5a-β weak Mertens M1 estimate `|Σ μ(d)/d| ≤ 1 + log N`.

**Added** (`proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean`, +49 LOC, +2 thm, +1 def):

- `noncomputable def mertensM (N : ℕ) : ℝ := Σ_{d ∈ Finset.Icc 1 N} (μ d : ℝ)`
- `theorem mertensM_zero : mertensM 0 = 0` (via `Finset.Icc_eq_empty_of_lt`)
- `theorem mertensM_abs_le (N : ℕ) : |mertensM N| ≤ (N : ℝ)`

The bound uses a 4-step `calc` chain:

1. `Finset.abs_sum_le_sum_abs` (triangle inequality)
2. Pointwise `|(μ d : ℝ)| ≤ 1` via `Int.cast_abs` + `exact_mod_cast`
   of `ArithmeticFunction.abs_moebius_le_one` (which lives in ℤ)
3. `Finset.sum_const` (simp-tagged) closes `Σ_{d ∈ s} 1 = s.card • 1`
4. `Nat.card_Icc` + `Nat.add_sub_cancel` yields `(Icc 1 N).card = N`

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.ChebyshevBoundsOQ04OQ01` reports `[7744/7744] Built
Proofs.ChebyshevBoundsOQ04OQ01 (23s)` clean on first iteration at base
SHA `91e6cc5396a` against Mathlib v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Honest scope**: this is a *trivial* triangle-inequality bound, far from
optimal — the Riemann hypothesis is equivalent to
`|M(N)| = O(N^{1/2+ε})`. But the linear bound is exactly what
summation-by-parts will need in Iter 5a-β. Estimate was ≤25 LOC body;
actual is ~12 LOC of proof code + ~37 LOC of module-level docstrings,
def signatures, and Future-Work text updates.

**INFRA recovery** (vs S7 2026-05-16): G7 disk 56 Gi (was 3.2 Gi RED) ✅,
G8 Docker Server up 29.4.1 (was hung with empty Server section) ✅,
G9 `proofs/.lake` self-symlink persists in main repo but confirmed inert
per memory `feedback_g9_qualifier_masks_real_bugs` (Docker bind-mount
overrides). Mathlib pin unchanged for 16 days; Iter 4's bearer
(`Moebius.lean:240`) and Iter 5a-α target bearer
(`AbelSummation.lean:229`) remain byte-stable.

### S7 STATE-SYNC — 2026-05-16T20:15Z (researcher-6, MERGED as PR #19820)

**Researcher**: researcher-6. **Scope**: 0 Lean changes; absorb 3 RED
INFRA blockers on host + fix 3 stale "this PR" leftovers from S6 PREP's
JSON write + reaffirm S6's split-ACT plan + 2-bearer SHA-stability
spot-check + restate picker decision matrix.

**Trigger**: S6 PREP merged at 2026-05-16T08:55:05Z (T-11h20m). Since
then: (a) host disk `/dev/disk3s5` 6.5 Gi → 3.2 Gi (crossed AMBER→RED,
below same-day soft floors set by adjacent shannon 5.8 Gi + ballot
5.4 Gi); (b) Docker daemon hung (`docker info` returns Client block,
Server section empty — repeatable cross-slug pattern observed in
abel-ruffini S7 #19755, sqrt2-minpoly S6 #19760, binomial S18 #19740);
(c) `proofs/.lake` is a circular self-symlink (target equals link
path) — same pattern from abel-ruffini S6 PREP #19633. Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S6 PREP.

**JSON drift fixes** (this S7 discharges):

- `currentState.focus`: "(researcher-9, ..., this PR)" →
  "(researcher-9, ..., MERGED as PR #19455 at 08:55:05Z)"
- `knowledge.progressSummary`: "Iter 4 (..., this PR)" →
  "Iter 4 (..., MERGED as PR #19400 at 03:52:02Z)"
- `knowledge.insights[11]`: "S6 PREP ... (2026-05-16, this PR)" →
  "S6 PREP ... (MERGED as PR #19455 at 08:55:05Z)"

**Bearer spot-check** (2-of-N, SHA-pin transitivity covers the rest):

- `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240`
  `sum_eq_iff_sum_mul_moebius_eq` — byte-stable @ pin ✅ GREEN
- `Mathlib/NumberTheory/AbelSummation.lean:229`
  `sum_mul_eq_sub_integral_mul₀'` (Iter 5a-α target) — byte-stable @ pin ✅ GREEN

**Files touched**: `research/problems/chebyshev-bounds-oq-04-oq-01/
sessions/2026-05-16-s7-statesync-infra-red-postship-pivot.md` (new,
~280 LOC, 10 sections), `research/problems/chebyshev-bounds-oq-04-oq-01/
state.md` (this file, head prepend only — historical tail preserved
verbatim), `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
(currentState.{since/focus/nextAction/blockers} + knowledge.{
progressSummary/insights[11]/nextSteps} + lastUpdate; 11-field edit;
iteration unchanged at 5, attemptCounts.total unchanged at 4).

**Picker decision matrix** for S{8} (5-row, see §6 of session memo):
R1/R2 ACT 5a-α or 5a-β if G7 disk ≥6.0 Gi + G8 Docker up + G9 `.lake`
OK + Mathlib SHA unchanged. R3 ACT under `LEAN_MEMORY_LIMIT=8192` if
4.0–6.0 Gi. R4 doc-only iteration or release-without-PR if disk still
<4.0 Gi. R5 doc-only if G8 or G9 still RED. R6 first-action mandate
to pre-claim Docker baseline if Mathlib SHA changes.

### S6 PREP — 2026-05-16T04:37Z (this session, doc-only, PR pending)

**Researcher**: researcher-9. **Scope**: 0 Lean changes; STATE-SYNC of
Iter 4 merge + bearer manifest + scope honesty for Iter 5a.

This PREP does **not** ship Lean code. It (a) absorbs the Iter 4 merge
(PR #19400 at 2026-05-16T03:52:02Z) — Iter 4's iteration-log entry
below carried "this session, PR pending" notation written from
researcher-6's session perspective; PR is now MERGED; (b) catalogues
Mathlib bearers for Iter 5a's analytic infrastructure (Abel summation,
sum/integral comparisons, divisor sums) at the current pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — 0 drift from Iter 4's
cited lines; (c) flags two Mathlib gaps (Mertens M1 `Σ μ(d)/d = O(1)`
and `Σ (log m)² = N(log N)² − 2N log N + 2N + O(log²N)`) and proposes
to build the weak forms locally; (d) recommends **splitting Iter 5a**
into three sub-iters 5a-α / 5a-β / 5a-γ with a more honest total budget
of **150–230 LOC** (vs the Iter 4 session memo's 80–120 LOC estimate).

**Side-note discovery** (recorded in S6 PREP §4.5): Mathlib has
`Chebyshev.psi` and `Chebyshev.theta` natively (`Mathlib/NumberTheory/
Chebyshev.lean`, 272 LOC, upstreamed from PrimeNumberTheoremAnd) with
`psi_le_const_mul_self : ψ x ≤ (log 4 + 4) * x`. This is an upper
bound, **not** the asymptotic `ψ(x) ~ x` — so does not discharge the
parent's `chebyshevPsi_asymptotic` axiom. Implication: Iter 5a–7+ stays
on the Selberg–Erdős track; an Iter 7+ bridge to `Chebyshev.psi` is
viable for the Tauberian step but not strictly required.

**Files touched**: `research/problems/chebyshev-bounds-oq-04-oq-01/
sessions/2026-05-16-s6-prep-iter5a-symmetry-formula.md` (new),
`research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (this file,
head replacement only — historical tail preserved),
`src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
(phase/since/iteration/lastUpdate/focus/nextAction/attemptCounts +
knowledge.insights + knowledge.nextSteps refresh).

### Iter 4 — 2026-05-16 (MERGED as PR #19400 at 2026-05-16T03:52:02Z)

**Result**: Closes the literal Möbius–log form deferred from Iter 3:

```
Λ₂(n) = Σ_{d ∣ n} μ(d) · (Real.log (n/d : ℕ))²    (n > 0).
```

One new theorem (file grows 312 → 325 LOC, 15 → 16 theorems, 0 sorries,
0 axioms maintained):

- `selbergLambda2_eq_moebius_log_sq`: applies
  `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` (Mathlib v4.26.0
  `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240`) to Iter 3's
  `sum_divisors_selbergLambda2_eq_log_sq`, then re-indexes
  `divisorsAntidiagonal → divisors` via `Nat.sum_divisorsAntidiagonal`
  (`Mathlib/NumberTheory/Divisors.lean:543`). Proof body ~8 LOC.

**Build trap (worth recording for future Möbius-inversion lifts)**: the
lift `∀ m > 0, ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2`
must annotate `m : ℕ` explicitly. Without it, Lean infers `m : ℝ` from
`Real.log m` (which accepts `ℝ` directly), then fails on `m.divisors`
("Real.divisors" not found) and rejects
`sum_divisors_selbergLambda2_eq_log_sq hm` (expects `0 < ?m : ℕ`). Fix
is a single-token addition (`∀ m : ℕ, 0 < m → ...`). General pattern:
any iff-form Möbius-inversion lift in this file should type-annotate
the bound `ℕ` variable when the RHS coerces through `Real.log`.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.ChebyshevBoundsOQ04OQ01` reports clean
`[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (51s)` after 2 Docker
iterations on base SHA `8a3cda556b6` against Mathlib v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Iter 3 — 2026-05-14 (PR #19092 merged 2026-05-15T22:59:33Z)

**Result**: Closes the central algebraic step of the elementary PNT
strategy — Selberg's **dual identity**

```
Σ_{d ∣ n} Λ₂(d) = (Real.log n)²    (n > 0).
```

Three new theorems (file grows 230 → 312 LOC, 12 → 15 theorems, 0
sorries, 0 axioms maintained):

- `vonMangoldtConv_eq_mul`: bridge connecting this file's explicit
  divisor-sum definition `vonMangoldtConv n = Σ_{d ∈ n.divisors} Λ(d) · Λ(n/d)`
  to Mathlib's `ArithmeticFunction.mul` form
  `((vonMangoldt : ArithmeticFunction ℝ) * vonMangoldt) n =
   Σ_{x ∈ n.divisorsAntidiagonal} Λ(x.1) · Λ(x.2)`. Proof: 1 LOC after
  `Nat.map_div_right_divisors` + `Finset.sum_map` + `rfl`.
- `sum_divisors_vonMangoldtConv`: the convolution-in-sum identity
  `Σ_{d ∣ n} (Λ ∗ Λ)(d) = Σ_{d ∣ n} Λ(d) · log(n/d)` via
  `(Λ ∗ Λ) ∗ ζ = Λ ∗ (Λ ∗ ζ) = Λ ∗ log`
  (`ArithmeticFunction.vonMangoldt_mul_zeta` + `coe_mul_zeta_apply` +
  `mul_assoc`).
- `sum_divisors_selbergLambda2_eq_log_sq` (main deliverable): combines
  the above with `ArithmeticFunction.vonMangoldt_sum` (Σ Λ(d) = log n)
  and `Real.log_mul` applied to each divisor pair (d, n/d) — both
  positive because `d ∣ n` and `n > 0`.

The "original" Möbius-inversion form `Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)`
is one step away (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`)
and is deferred to Iter 4 (~15 LOC).

**Incidental parent-file fixes** (this PR bundles them to keep the
slug build-clean):

- `proofs/Proofs/ChebyshevBoundsOQ04.lean:298` — Mathlib v4.26.0 `ring`
  regression: `4^m = 2^(2*m)` no longer closes by `ring` (tactic treats
  `4` and `2` as distinct atoms; `ring_nf` suggestion does not help).
  Fix: `by ring` → `by rw [pow_mul]; rfl` (1 LOC).
- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean:191` — Mathlib v4.26.0
  rename `Nat.divisors_prime` → `Nat.Prime.divisors` (dot-method form).
  Fix: 1 LOC inline at `vonMangoldtConv_prime` (an Iter 2 lemma).

Both regressions surfaced because the slug had last been Docker-built
at Iter 2 merge (2026-05-12T00:48Z), and Mathlib's tracked revision
evolved in the intervening 2 days. Pattern: see MEMORY
`feedback_researcher_build_pending_slug_series_silent_parent_regression.md`.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.ChebyshevBoundsOQ04OQ01` reports clean
`[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (10s)` after 2 Docker
iterations (iter 1 surfaced the 3 errors above, iter 2 clean).

### Iter 2 — 2026-05-12 (PR #17690 merged)

**Result**: Closes the Iter 1 documented next-iteration deliverables
#1 and #2:

- `vonMangoldtConv_prime`: `(Λ ∗ Λ)(p) = 0` for prime `p`. Proof via
  `Nat.Prime.divisors` (formerly `Nat.divisors_prime`, see Iter 3 notes)
  + `Finset.sum_pair` + `vonMangoldt_apply_one`.
- `selbergLambda2_prime`: `Λ₂(p) = (log p)²` for prime `p`. Proof via
  `vonMangoldt_apply_prime`.

LOC delta: 206 → 230 (+24). Theorem count: 10 → 12. Sorries unchanged
(0). Axioms unchanged (0). PR #17690 also refreshed the gallery
`meta.json` description + `originalContributions` to mention Iter 2.

**Race note (post-merge cleanup deferred)**: PR #17689 ("Iter 2 —
prime values", different branch, OPEN+CONFLICTING since
2026-05-12T22:13Z) was a parallel attempt superseded by #17690 but
never closed. Decision to comment-close it deferred to maintainer.

### Iter 1 — 2026-05-09 (researcher-12, PR #17658 merged)

**Result**: OBSERVE-phase scaffold of the Selberg–Erdős strategy.

**Built** (`proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean`, 209 LOC):

- 3 noncomputable defs:
  - `vonMangoldtConv : ℕ → ℝ` — `Λ ∗ Λ` as a literal divisor sum
    (chosen over Mathlib's `ArithmeticFunction.mul` for cleaner
    algebraic rewrites downstream — VALIDATED by Iter 3's bridge).
  - `selbergLambda2 : ℕ → ℝ` — `Λ(n) · log n + (Λ ∗ Λ)(n)`.
  - `selbergSum2 : ℕ → ℝ` — `Σ_{n ≤ N} Λ₂(n)`.
- 10 routine theorems: zero-value, one-value, non-negativity,
  successor-recursion, monotonicity (one per def).
- 0 sorries, 0 axioms.

Gallery entry `chebyshev-bounds-oq-04-oq-01` created (status
`formalized`, badge `wip`). File roadmap + Future Work sections
document the downstream Selberg symmetry formula + Erdős finishing
argument; the parent's `chebyshevPsi_asymptotic` axiom remains the
open target.

## Blockers

None. Iter 5 (Selberg's symmetry formula
`Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`) is the next analytic step.
Requires either: (a) a Mathlib-internal summation-by-parts framework
specialised to `Λ`-weighted sums (Mathlib v4.26.0 has only
`Finset.sum_Ioc_consecutive` and `summation_by_parts` lemmas in
`Mathlib/Analysis/MeanInequalitiesPow.lean` — neither directly
applicable), or (b) a hand-rolled `Abel`-style derivation using
Iter 4's identity as the launching point. Recommended path is (b) for
Iter 5a (the leading-term `2N log N`) and a separate Iter 5b for the
`O(N)` error via the Möbius hyperbola bound.

## Next Action

**S6 PREP recommends splitting Iter 5a into three sub-iters** (see
`sessions/2026-05-16-s6-prep-iter5a-symmetry-formula.md` §5–§8 for the
full per-sub-iter acceptance criteria). Picker priority:

1. **Iter 5a-α** (independent, can be claimed first): prove

   ```
   ∃ C : ℝ, ∀ N ≥ 2,
     |Σ_{m ∈ Icc 1 N} (Real.log m)² − (N · (Real.log N)² − 2N · Real.log N + 2N)|
       ≤ C · (Real.log N)²
   ```

   via Abel summation against `f(t) = (log t)²` (Mathlib bearer
   `sum_mul_eq_sub_integral_mul₀'` at `Mathlib/NumberTheory/
   AbelSummation.lean:229`). Estimated **60–90 LOC**, 2–4 Docker iters.

2. **Iter 5a-β** (independent of 5a-α; can run in parallel): prove the
   weak Mertens M1 bound

   ```
   ∀ N ≥ 1, |Σ_{d ∈ Icc 1 N} (ArithmeticFunction.moebius d : ℝ) / d|
     ≤ 1 + Real.log N
   ```

   via summation by parts on `M(N) := Σ μ(d)` (use
   `|M(N)| ≤ N` from `abs_sum_le_sum_abs` + `Int.abs_moebius_le_one`).
   Estimated **50–80 LOC**, 2–3 Docker iters.

3. **Iter 5a-γ** (requires 5a-α + 5a-β merged): assemble Selberg's
   symmetry formula

   ```
   ∃ C : ℝ, ∀ N ≥ 2,
     |selbergSum2 N − 2 · (N : ℝ) · Real.log (N : ℝ)| ≤ C · (N : ℝ)
   ```

   via the Möbius hyperbola sum swap on Iter 4's
   `selbergLambda2_eq_moebius_log_sq`. May require an additional
   Iter 5a-δ for Mertens M2 (`Σ (μ(d)/d) · log d = O(1)`, ~30–50 LOC)
   depending on the sign-cancellation handling.
   Estimated **40–60 LOC**, 2–4 Docker iters.

**Total honest budget for Iter 5a**: **150–230 LOC**, **6–11 Docker
iters** across the three (potentially four) sub-iters. The Iter 4
session memo's estimate of 80–120 LOC was too optimistic by ~2×.

After Iter 5a, the remaining roadmap is:

- **Iter 5b**: optional sharpening of the `O(N)` error term via a
  detailed Möbius-hyperbola bound (only needed if downstream Iter 6
  requires a witnessed constant smaller than 5a-γ produces).
- **Iter 6**: Tauberian inequality
  `V(x) · log x ≤ (2/x) · Σ_{n ≤ x} V(x/n) · Λ(n) + O(1)`
  where `V(x) := |ψ(x) − x| / x`.
- **Iter 7+**: Erdős combinatorial finishing argument; discharges
  parent's `chebyshevPsi_asymptotic` axiom.

## Attempt Counts

- Total attempts: 4 (Iter 1, Iter 2, Iter 3, Iter 4); S6 PREP is
  bookkeeping, does not bump counter
- Current approach attempts: 4 (Selberg–Erdős elementary)
- Approaches tried: 1

## Blockers

None. Iter 5a is the next analytic step, decomposed into the three
(optionally four) sub-iters described above. The two Mathlib gaps
identified by S6 PREP §4.4 (`Σ (log m)²` asymptotic and weak Mertens
M1) are both buildable locally in 50–90 LOC each, so the slug is not
truly blocked — only awaiting the next ACT picker for sub-iter 5a-α
or 5a-β.

## Race awareness (this S6 PREP)

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`
at session start returned **0 OPEN PRs**:

- Iter 4 PR #19400 MERGED 2026-05-16T03:52:02Z
- S4 PREP #19171 MERGED 2026-05-15T22:56:46Z
- Iter 3 PR #19092 MERGED 2026-05-15T22:59:33Z
- Stale #17689 CLOSED (parallel Iter 2 attempt, superseded by #17690)

This S6 PREP touches:

- `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-16-s6-prep-iter5a-symmetry-formula.md`
  (new — comprehensive bearer manifest + scope honesty + split
  recommendation)
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (this file
  — head replacement only; historical iteration log preserved verbatim)
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
  (phase/since/iteration/lastUpdate/focus/nextAction/attemptCounts +
  knowledge.insights += 1 + knowledge.nextSteps refresh)

**Not touched**:

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` — Lean source frozen
  at Iter 4 post-merge state (325 LOC, 16 thm, 0 sorries, 0 axioms)
- `proofs/Proofs/ChebyshevBoundsOQ04.lean` — parent file unchanged
- `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json` — gallery
  meta frozen at Iter 4 post-merge state (lineCount 325, theoremCount
  16)
- No sibling slug content, no Mathlib content, no Aristotle companion
  (the slug doesn't have one — Λ₂ work is open mathematics)

Pre-push re-check (per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`):
will re-run `gh pr list` immediately before `git push`.
