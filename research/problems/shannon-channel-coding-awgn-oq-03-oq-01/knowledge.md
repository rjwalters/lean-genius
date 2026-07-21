## Session 2026-07-20 (researcher-1) — capacity CONCAVE in the scalar total power budget

New file `ShannonChannelCodingAWGNOQ03OQ01CapacityBudgetConcave.lean` (namespace
`ShannonWaterFilling`, imports `...Concave`). VERIFIED clean Docker build (v4.31.0);
both theorems depend only on `[propext, Classical.choice, Quot.sound]` (0 axioms / 0 sorries,
confirmed by `#print axioms`).

Fills the last easy gap in the concavity story. Prior files gave concavity in the power
VECTOR (`parallelRate_concaveOn_power`, `parallelRate_strictConcaveOn_power`), in the
BANDWIDTH/channel-count (`wideRate_strictConcaveOn`), and scalar-power concavity ONLY in the
degenerate equal-noise case (`EqualNoise.lean`). Missing was the general-profile macroscopic
law: the water-filling value function `C(P) = max{R(x) : x≥0, ∑xᵢ≤P}` is CONCAVE in the
scalar total power `P` — diminishing marginal capacity as the budget grows.

- `capacity_concave_budget` — `a·C(P₁) + b·C(P₂) ≤ C(a·P₁+b·P₂)`, parametrised by three water
  levels μ₁,μ₂,μ₃ with `g(μ₃)=a·g(μ₁)+b·g(μ₂)` (matches the file's existing water-level
  parametrisation convention, e.g. `capacity_mono_budget`). Proof: the convex combination
  `x = a•waterAlloc μ₁ N + b•waterAlloc μ₂ N` is feasible for budget `g(μ₃)` (nonneg;
  ∑x = a·g(μ₁)+b·g(μ₂) via `Finset.sum_add_distrib`+`Finset.mul_sum`), so `waterfilling_optimal`
  gives `R(x) ≤ R(waterAlloc μ₃ N)`; `parallelRate_concaveOn_power .2` gives
  `a·C(P₁)+b·C(P₂) ≤ R(x)`; `linarith` chains. NO envelope theorem needed.
- `capacity_midpoint_concave_budget` — `a=b=½` corollary: `(C(P₁)+C(P₂))/2 ≤ C((P₁+P₂)/2)`.

### Gotchas
- Corollary call `capacity_concave_budget N hN hμ₃ (a:=1/2)(b:=1/2) …` left the implicit
  `{μ₁ μ₂}` unpinned → Lean unified BOTH to μ₃ (hmain collapsed to `½C(μ₃)+½C(μ₃)≤C(μ₃)`),
  `linarith` failed. Fix: pass `(μ₁ := μ₁) (μ₂ := μ₂)` explicitly.
- `waterfilling_optimal` needs `0 < μ₃`; taken as an explicit hypothesis (auto-holds whenever
  the combined budget is positive, via `waterLevel_pos`).

INFRA NOTE: worktree `/Volumes/Stripe/lean-genius/researcher-1` was janitor-reaped mid first
Docker build (disk 10% — the fresh-no-commit-worktree reap, not disk-full). Recreated via
`git worktree add <path> <branch>` and committed the .lean file BEFORE rebuilding.

---

## Session 2026-07-20 (researcher-1) — wideband rate STRICT CONCAVITY in bandwidth (diminishing returns)

New file `ShannonChannelCodingAWGNOQ03OQ01WidebandConcave.lean` (namespace `ShannonWaterFilling`,
imports `...MonotoneCount`). VERIFIED clean Docker build; all 3 theorems depend only on
`[propext, Classical.choice, Quot.sound]` (0 axioms / 0 sorries).

Completes the qualitative *shape* of the wideband equal-noise capacity curve. Prior files gave:
strictly increasing (`rate_equalNoise_count_strictMonoOn`), bounded by `P/(2c)`, and `P/(2c)` the
exact supremum (`rate_equalNoise_iSup_eq_wideband`). This file adds the concavity — the curve rises
with **diminishing marginal returns**:

- `hasDerivAt_wideRate_deriv` — second derivative `g''(t) = -a²/(2 t (t+a)²) < 0` of
  `g(t)=(t/2)·log(1+a/t)` (`a=P/c`), built by differentiating the first derivative
  `g'(t)=½(log(1+a/t) − a/(t+a))` supplied by the reused `hasDerivAt_wideRate`.
- `wideRate_strictConcaveOn` — `g` is `StrictConcaveOn ℝ (Set.Ioi 0)` via
  `strictConcaveOn_of_deriv2_neg'`. The iterated `deriv^[2] g` is reduced to `deriv g'` by noting
  `deriv g =ᶠ[𝓝 x] g'` on the open set `Ioi 0`.
- `rate_equalNoise_count_diminishing` — discrete corollary: for `c>0, P>0, n≥1`,
  `R(n) + R(n+2) < 2·R(n+1)`, i.e. `R(n+1)−R(n) > R(n+2)−R(n+1)`. Each added equal-noise
  sub-channel raises the rate by strictly less than the previous. Obtained as the strict
  midpoint-concavity instance (weights 1/2,1/2) of `wideRate_strictConcaveOn` at abscissae n, n+2.

Distinct from `parallelRate_concaveOn_power` (Concave.lean), which is concavity in the POWER
allocation; this is concavity in the bandwidth / channel-count variable.

### Gotchas (v4.31)
- `HasDerivAt.div` / `HasDerivAt.sub` return `Pi.div`/`Pi.sub` function forms
  (`(fun _=>a)/(fun s=>s+a)`), so `convert … using 1` spawns a spurious
  `AddCommGroup` instance-equality goal (`Real.instAddCommGroup = Real.normedCommRing.toAddCommGroup`).
  Fix: annotate each intermediate `HasDerivAt` with the *pointwise lambda* type (forces defeq),
  then close the main goal by rewriting the target derivative value and `exact hhalf` — do not `convert`.
- `field_simp` makes **no progress** when a denominator is a bare SUM `1 + a/t` (cannot show a sum
  ≠ 0 structurally). Rewrite `1 + a/t = (t+a)/t` (`add_div` + `div_self`) first; only atomic
  denominators `t`, `t+a` remain, which `field_simp` discharges from context.

Depth-2 slug; problem was already COMPLETED — this is a structural extension of the verified OQ files.

---

## Session 2026-07-12 (researcher-6) — explicit least-upper-bound P/(2c) = ⨆ₙ Cₙ

Closed prior next-step #2 in `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean` (3 theorems,
0 axioms, 0 sorries):

- `rate_equalNoise_seq_le_wideband` — scalar-ℕ per-n ceiling (n/2)·log(1+P/(nc)) ≤ P/(2c) for
  EVERY n (incl. n=0 where the rate is 0). The ℕ-indexed counterpart of the existing
  Fintype-card `rate_equalNoise_le_wideband`, packaged for the range the sup runs over.
- `rate_equalNoise_wideband_isLUB` — IsLUB (range g) (P/(2c)), g(n)=(n/2)log(1+P/(nc)).
- `rate_equalNoise_iSup` — ⨆ₙ (n/2)log(1+P/(nc)) = P/(2c) (Shannon C_∞ as a closed-form sup).

KEY INSIGHT: the explicit LUB needs NO monotonicity of g. The "least" half is `le_of_tendsto'`
applied to the EXISTING `rate_equalNoise_tendsto_wideband` (any upper bound b dominates the limit
P/(2c) = lim g(n)); the "upper bound" half is the per-n ceiling. The prior next-step framing
("needs monotonicity of n↦(n/2)log(1+P/(nc))") over-specified the requirement — tendsto alone
suffices for the sup. Monotonicity in n remains a physically-meaningful (more-subchannels-is-
better) but strictly-stronger refinement, now demoted to an OPTIONAL next step.

`⨆` = `sSup ∘ Set.range` definitionally, so `IsLUB.csSup_eq` + `Set.range_nonempty` closes the
iSup equality in term mode.

BUILD: typechecked green via main-repo oleans (`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
<worktree-file>`) — 0 errors. Depth-2 slug. Remaining open: operational coding theorem (parent
oq-04) and continuous infinite-band integral capacity.

---

# Knowledge Base: shannon-channel-coding-awgn-oq-03-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-09 (Session 1) — Water-filling formalized (FRESH)

**Mode**: FRESH · **Outcome**: progress (all three open items formalized; build verification via decoupled self-contained file)

### What I did
- Created `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (namespace `ShannonWaterFilling`).
- Proved the full finite-dimensional water-filling theorem, all axiom-free / sorry-free:
  1. `add_waterAlloc`: `Nᵢ + (μ−Nᵢ)₊ = max μ Nᵢ` — the identity that drives everything.
  2. `perUseCapacity_sub_le`: per-channel tangent bound (first-order condition in elementary form).
  3. `waterfilling_optimal`: **KKT optimality** — `Pᵢ⋆ = (μ−Nᵢ)₊` maximises `∑ ½log(1+Pᵢ/Nᵢ)` over all feasible allocations.
  4. `waterAlloc_rate_closedForm`: `R(P⋆) = ∑ ½ log(max μ Nᵢ / Nᵢ)`.
  5. `exists_waterLevel` (IVT) + `waterLevel_unique` (strict monotonicity) + `continuous_/monotone_waterBudget`.

### Key findings
- **The optimality proof needs no calculus.** The first-order/KKT condition is replaced by the
  scalar tangent inequality `log u ≤ u − 1` (`Real.log_le_sub_one_of_pos`) applied per channel with
  `u = (Nᵢ+xᵢ)/(Nᵢ+Pᵢ⋆)`. Summing gives
  `R(x) − R(P⋆) ≤ ∑ (xᵢ−Pᵢ⋆)/(2·max(μ,Nᵢ)) ≤ (∑xᵢ − P)/(2μ) ≤ 0`.
- The denominator collapse `max(μ,Nᵢ) → μ` is a two-case split: **active** channels (`Nᵢ<μ`) give
  equality since `Nᵢ+Pᵢ⋆ = μ`; **inactive** channels (`Nᵢ≥μ`) have `Pᵢ⋆=0`, `xᵢ≥0`, so
  `xᵢ/Nᵢ ≤ xᵢ/μ` (`div_le_div_of_nonneg_left`). A naive termwise bound fails on inactive channels
  when `xᵢ<x⋆ᵢ`, so the case split is essential.
- Water level existence = IVT on continuous monotone `g(μ)=∑(μ−Nᵢ)₊` between `g(0)=0` and
  `g(N_{i₀}+P) ≥ P` (single active channel `i₀` already supplies `P`). Uniqueness (for `P>0`) = strict
  monotonicity of `g` wherever `g>0` (`Finset.sum_lt_sum` with one strictly-increasing active term).

### Infrastructure / environment
- `ShannonEntropyOQ01` (transitively imported by the parent `ShannonChannelCodingAWGN`) is currently
  **SIGBUS-135 crashing at olean-write** in the Docker build — a pre-existing/environmental crash, not
  a code error (PR #36590 built through the same chain earlier). To get independent verification I
  **decoupled**: inlined `perUseCapacity P N = ½ log(1+P/N)` (definitionally identical to the gallery
  `awgnCapacity`) so the file imports only `Mathlib`.

### Files modified
- `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (new)
- `src/data/research/problems/shannon-channel-coding-awgn-oq-03-oq-01.json` (knowledge)

### Next steps
- Operational coding theorem (random Gaussian codebooks) tying capacity to achievable rates (→ oq-04).
- Continuous infinite-band (integral) water-filling limit.
- Equal-noise corollary: `μ = (P + ∑Nᵢ)/n`, `C = (n/2) log(1 + P/∑Nᵢ)`.

## Session 2026-07-09 (researcher-3) — equal-noise closed form (VERIFIED)

New companion `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`
(namespace `ShannonWaterFilling`, imports the parent file). VERIFIED clean Docker
build `✔ [7744/7744] Built ... (3.9s)`, 0 axioms / 0 sorries. Addresses the
parent nextStep "explicit water level for the equal-noise case".

Delivered:
- `waterBudget_const`: constant noise ⟹ `g(μ) = n·(μ−c)₊` (`Finset.sum_const` +
  `nsmul_eq_mul`; `n = Fintype.card ι`).
- `waterLevel_equalNoise`: the level realising budget `P ≥ 0` is exactly
  `μ = c + P/n`; `waterLevel_equalNoise_unique` upgrades to uniqueness for `P>0`
  via the parent's `waterLevel_unique`.
- `waterAlloc_rate_equalNoise`: capacity collapses to `C = (n/2)·log(1 + P/(n·c))`.
- `parallelRate_le_equalNoise`: operational optimum — no feasible allocation beats
  `C`; the constrained capacity of `n` identical parallel Gaussian channels.

### Gotchas
- `heq : (c+P/n)/c = 1 + P/(n·c)` — `field_simp` **fully closes** this, so a
  trailing `; ring` throws "No goals to be solved" (a real code-1 error that the
  fleet SIGBUS-135 storm masked for ~8 builds). Deterministic fix:
  `rw [hμdef, add_div, div_self hcne, div_div]` (no field_simp/ring).
- Do NOT `set μ := c + P/n` in the operational lemma: the external
  `waterAlloc_rate_equalNoise` is stated with the raw expression, and `set`'s
  opaque local μ is not defeq to it, breaking the `calc`. Write the expression out.
- `div_mul_cancel₀ (a) (h : b ≠ 0) : a/b*b = a` confirmed @lean4.26.

## Session 2026-07-09 (researcher-2) — noise-antitonicity + wideband ceiling (UNVERIFIED, env SIGBUS)

Two new structural lemmas appended to `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`
(namespace `ShannonWaterFilling`), both elaborate clean; olean-write blocked by the
standing SIGBUS-135/139 storm (9 build runs, none reached a real error at my lines
140-200; one run additionally hit a transient corrupted `Centroid.olean.private`
mathlib-cache header). Shipped UNVERIFIED, matching prior sessions' env pattern.

Delivered:
- `rate_equalNoise_antitone_noise`: for fixed budget `P ≥ 0`, the equal-noise capacity
  `C(c) = (n/2)·log(1 + P/(n·c))` is **antitone in the noise floor** `c₁ ≤ c₂ ⟹ C(c₂) ≤ C(c₁)`.
  The noise-side dual of the merged `rate_equalNoise_mono_power`. Proof: `gcongr` for the
  argument inequality (`P/(n·c)` antitone in `c`), then `Real.log_le_log` +
  `mul_le_mul_of_nonneg_left`. Same recipe as the VERIFIED power-monotonicity lemma.
- `rate_equalNoise_le_wideband`: the **wideband ceiling** `(n/2)·log(1 + P/(n·c)) ≤ P/(2c)`,
  *independent of `n`* — the infinite-bandwidth capacity limit of the AWGN channel. Any
  split of total power `P` across identical parallel Gaussian sub-channels is capped at
  `P/(2c)` nats. Proof: tangent bound `Real.log_le_sub_one_of_pos` on `u = 1 + P/(n·c)`
  gives `log u ≤ P/(n·c)`, then `mul_le_mul_of_nonneg_left` and `field_simp; ring` collapse
  `(n/2)·(P/(n·c)) = P/(2c)` (the `n` cancels — this is why the ceiling is n-free).

### Next steps
- The wideband limit as a genuine `Tendsto`: `C(n) → P/(2c)` as `n → ∞` (needs
  `n·log(1 + a/n) → a`), upgrading the `≤ P/(2c)` bound to an attained supremum.
- Concavity of `C(P)` in the power budget (diminishing returns / `ConcaveOn`).

---

## Session 2026-07-09 (Session 2) — Capacity monotonicity layer (researcher-4)

**Mode**: SATURATED (problem COMPLETED) · **Outcome**: progress (new general structural layer)

### What I did
- Created `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01Monotone.lean` (namespace
  `ShannonWaterFilling`, imports the main OQ0301 file). Nine axiom-free / sorry-free
  lemmas giving the **general** (arbitrary noise profile) monotonicities of the
  water-filling capacity, complementing the equal-noise companion:
  1. `perUseCapacity_nonneg` / `perUseCapacity_mono` — a single AWGN sub-channel's
     rate is `≥ 0` and monotone in allotted power.
  2. `waterAlloc_mono_level` — the depth `(μ − Nᵢ)₊` is monotone in the water level.
  3. `rate_waterAlloc_nonneg` / `rate_waterAlloc_mono_level` — the water-filling
     rate is `≥ 0` and monotone in the water level `μ`.
  4. `waterBudget_nonneg`, `waterLevel_pos` (0 < P ⟹ 0 < μ),
     `rate_waterAlloc_eq_zero_of_budget_zero` (support lemmas).
  5. **`capacity_mono_budget`** (headline) — the constrained capacity `C(P)` is
     monotone in the total power budget `P`: more power never decreases the optimal
     achievable rate.

### Key finding
- `capacity_mono_budget` needs *no* new analysis: the water-filling allocation for a
  smaller budget `P₁` is a **feasible** allocation for a larger budget `P₂` (its total
  power is `P₁ ≤ P₂`), so `waterfilling_optimal` at `μ₂` immediately dominates it.
  The only wrinkle is the degenerate `P₂ = 0` case (forces `P₁ = 0`, both capacities
  `= 0`), dispatched via `rate_waterAlloc_eq_zero_of_budget_zero`. Positivity of the
  water level for a positive budget (`waterLevel_pos`) supplies the `0 < μ₂` premise.

### Infrastructure / environment
- **DOCKER INFRA DOWN**: `docker-build.sh` dies at image build with
  `containerd .../meta.db: input/output error` and `docker images` reports
  content-store blob I/O errors. Host disk fine (156Gi free). Operator-level
  containerd corruption; not self-fixable (won't prune shared caches). Shipped
  **UNVERIFIED** with careful manual review — every API call mirrors the already
  VERIFIED main + EqualNoise sibling files (`Real.log_le_log`,
  `mul_le_mul_of_nonneg_left`, `Finset.sum_nonneg`, `gcongr`, `waterfilling_optimal`).

### Files modified
- `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01Monotone.lean` (new)

## Session 2026-07-10 (researcher-1) — VERIFY standing-unverified file (no bug)

Prior session shipped work UNVERIFIED (manual review, docker down). `ShannonChannelCodingAWGNOQ03OQ01.lean`
(370 L, Mathlib-only) verified via lean-elab ([[reference-docker-down-lean-elab-verification-path]]):
EXIT 0, zero errors (2 benign warnings). Standing work confirmed correct (no bug). Marked completed.

## Session 2026-07-20 (researcher-1) — nextSteps reconciliation (COMPLETE for scope)

**Mode**: REVISIT (RICH re-serve) · **Outcome**: tracker reconciliation, no new theorems.

The problem was solved via PR #36621 (water-filling KKT optimality + wideband supremum
`rate_equalNoise_iSup_eq_wideband`). The tracker `nextSteps` still listed two "optional
refinements" as open, but **both are already proven in-tree**:
- **n-monotonicity** of the equal-noise rate sequence `n ↦ (n/2)·log(1+P/(nc))`:
  `rate_equalNoise_count_mono` (Monotone over all `n`) and
  `rate_equalNoise_count_strictMonoOn` (strict on `n ≥ 1`), in
  `ShannonChannelCodingAWGNOQ03OQ01MonotoneCount.lean`. Together with
  `rate_equalNoise_count_lt_wideband` this already pins the wideband capacity `P/(2c)` as a
  strictly-increasing limit, the sharpening the note asked for.
- **joint strict concavity** of `parallelRate` in the power vector:
  `rate_equalNoise_strictConcaveOn_power` in `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`.

Both companion files are 0-sorry / 0-axiom (grep-confirmed). Updated the tracker to record
these as DONE and mark the two remaining directions (operational coding theorem → parent
oq-04; continuous infinite-band integral capacity) as out-of-scope extensions. Set
`status: completed`. v4.31 verification is covered by the separate open PR #39278; no proof
files touched here. No new mathematics — the scope deliverable is saturated.

## Session 2026-07-20 (researcher-1) — tracker nextAction reconciliation (stale open→DONE)

**Mode**: REVISIT (RICH re-serve of a solved leaf) · **Outcome**: tracker accuracy fix, no new theorems.

On re-claim, the tracker `nextAction` still listed the two "optional refinements" as OPEN:
n-monotonicity of the equal-noise rate sequence, and joint strict concavity of `parallelRate`
in the power vector. **Both are already PROVEN 0-sorry/0-axiom on `main`** and were
misdirecting future sessions to re-prove them:
- `rate_equalNoise_count_mono` / `rate_equalNoise_count_strictMonoOn` in
  `ShannonChannelCodingAWGNOQ03OQ01MonotoneCount.lean` (Monotone over all `n`; strict on `n ≥ 1`).
- `rate_equalNoise_strictConcaveOn_power` in `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean:293`
  (unique water-filling maximizer).

An earlier 2026-07-20 note claimed to have reconciled this, but the edit never reached `main`
(no reconciliation PR landed; tracker still read `status: active` with the stale list). Corrected
here. The only genuinely-open directions are out-of-scope EXTENSIONS: (a) operational coding
theorem via random Gaussian codebooks (belongs on parent oq-04); (b) continuous infinite-band
integral capacity. This OQ leaf is saturated at its scope.
