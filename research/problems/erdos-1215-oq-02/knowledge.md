# Knowledge Base: erdos-1215-oq-02

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

## Session 2026-07-09 (researcher-4) - Cyclotomic lemniscate is bounded

**Mode**: FRESH
**Outcome**: progress (VERIFIED 0-sorry/0-axiom, docker `[7744/7744]` 4.6s)

### What I Did
- Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ01.lean` (7 decls, 0 sorry / 0 axiom).
- Proved the fundamental structural fact for the OQ-02 restriction: every cyclotomic
  level set `{z : |Φ_n(z)| < C}` is **bounded** (compact), with explicit radius
  `max 2 (C+1)`.

### Key Findings
- Mechanism: all roots of `Φ_n` lie on the unit circle, so
  `|Φ_n(z)| = ∏_{μ prim} ‖z-μ‖ ≥ (‖z‖-1)^{φ(n)} → ∞`.
- Consequence (`not_hasBoundedLevelPath_cyclotomic`): for cyclotomic polynomials the
  Erdős #1215 escape-to-∞ path obstruction is **unconditional** — it holds for every
  threshold `C`, not merely `C > 1`, because the lemniscate interior is compact. This
  is strictly simpler than (and independent of) the Mac Lane 1953 labyrinth mechanism,
  which is needed only for the general roots-on-circle class.
- Exact small-n geometry: `{|Φ_1|<1}=ball(1,1)`, `{|Φ_2|<1}=ball(-1,1)`.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ01.lean` (new)
- `src/data/research/problems/erdos-1215-oq-02.json` (knowledge)

### Next Steps
- Sharpen radius to `1 + C^{1/φ(n)}`.
- Component-count / path-length geometry for n=3,4,6 (the genuinely open driver;
  needs polynomial-lemniscate topology Mathlib currently lacks).

### Reusable Lean recipe
`cyclotomic_eq_prod_X_sub_primitiveRoots (isPrimitiveRoot_exp n hn)` factors `Φ_n`;
`norm_prod` turns `‖∏‖` into `∏‖‖`; `IsPrimitiveRoot.norm'_eq_one` + `norm_sub_norm_le`
give the per-factor bound `‖z-μ‖ ≥ ‖z‖-1`; `Finset.prod_le_prod` + `Finset.prod_const`
+ `card_primitiveRoots` assemble `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|`; `le_self_pow₀` collapses
the exponent for `‖z‖ ≥ 2`.

## Session 2026-07-09 (researcher-6) - Sharp two-sided radii

**Mode**: FRESH (built on researcher-4's OQ02OQ01)
**Outcome**: progress (VERIFIED 0-sorry/0-axiom, docker `[7745/7745]` build succeeded)

### What I Did
- Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ02.lean` (6 decls, 0 sorry / 0 axiom).
- Executed the first "Next Step" left by researcher-4: **sharpened the outer radius**
  of the cyclotomic level set from the crude `max 2 (C+1)` to `1 + C^{1/φ(n)}`, and
  added the complementary **inner ball containment**.

### Key Findings
- Mirror of the OQ01 lower bound: `‖z-μ‖ ≤ ‖z‖+1` per factor ⟹
  `|Φ_n(z)| ≤ (‖z‖+1)^{φ(n)}` (`norm_cyclotomic_eval_le`).
- Inner containment: `(‖z‖+1)^{φ(n)} < C ⟹ z ∈ {|Φ_n|<C}`, hence
  `closedBall(0,r) ⊆ {|Φ_n|<C}` when `(r+1)^{φ(n)} < C`.
- Sharp outer radius: taking `φ(n)`-th roots of `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)| < C`
  gives `‖z‖ < 1 + C^{1/φ(n)}` (`cyclotomic_sublevel_norm_lt_sharp`).
- Quantitative payoff (`sharp_radius_le_crude`): for `C ≥ 1`,
  `1 + C^{1/φ(n)} ≤ max 2 (C+1)`, and the sharp radius → 2 as `φ(n) → ∞`. So
  high-degree cyclotomic lemniscates hug the unit circle — the antithesis of the
  clustering freedom Mac Lane needs for a labyrinth.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ02.lean` (new)

### Next Steps
- Component-count / path-length geometry for n=3,4,6 (still the genuinely open driver;
  needs polynomial-lemniscate topology Mathlib currently lacks).
- Two-sided sandwich is now in place; a natural follow-up is the *area* of
  `{|Φ_n|<C}` squeezed between the two balls.

### Reusable Lean recipe
Take `k`-th roots of a natural-power bound `a^k < C` (with `a ≥ 0`, `k ≠ 0`):
`Real.rpow_lt_rpow (pow_nonneg ha _) hak hkpos` lifts to `(a^k)^{1/k} < C^{1/k}`, then
`Real.pow_rpow_inv_natCast ha hk0 : (a^k)^((k:ℝ)⁻¹) = a` collapses the LHS. Exponent
`1/φ(n) ≤ 1` via `inv_le_one_of_one_le₀`; `Real.rpow_le_rpow_of_exponent_le` compares
`C^{1/φ(n)} ≤ C^1 = C`. Upper factor bound uses `norm_sub_le` + `pow_le_pow_left₀`.

## Session 2026-07-09 (researcher-5) - Area of the level set (disc squeeze)

**Mode**: FRESH (built on researcher-6's OQ02OQ02 two-sided ball containment)
**Outcome**: progress (VERIFIED 0-sorry/0-axiom, docker `[7746/7746]` 3.9s)

### What I Did
- Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ03.lean` (4 decls, 0 sorry / 0 axiom).
- Executed the "area between the two balls" next-step: pushed the iter-3 two-sided
  ball containment through the planar Lebesgue measure on `ℂ ≅ ℝ²`.

### Key Findings
- `volume_levelSet_le`: `area {|Φ_n|<C} ≤ π·(1+C^{1/φ(n)})²` — `measure_mono` on the
  sharp outer containment `sublevel_subset_closedBall_sharp` + `Complex.volume_closedBall`.
- `le_volume_levelSet`: `π·r² ≤ area {|Φ_n|<C}` when `0≤r`, `(r+1)^{φ(n)}<C` — mirror
  via `closedBall_subset_levelSet_cyclotomic`.
- `volume_levelSet_sandwich`: both together → `π·r² ≤ area ≤ π·(1+C^{1/φ(n)})²`.
- `volume_levelSet_lt_top`: the level set has **finite** planar area (measure-theoretic
  strengthening of researcher-4's qualitative boundedness). For fixed `C>1` the outer
  disc area → `4π` as `φ(n)→∞`, so the region's measure stays uniformly controlled —
  the opposite of a Mac Lane labyrinth.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ03.lean` (new)

### Next Steps
- Small-n (n=3,4,6) explicit lemniscate boundary / component count — still the open
  driver (polynomial-lemniscate topology not in Mathlib). The ball squeeze cannot give
  the exact area, only two-sided bounds.

### Reusable Lean recipe
Turn a set-containment `A ⊆ closedBall 0 ρ` into an area bound: `measure_mono` gives
`volume A ≤ volume (closedBall 0 ρ)`, then `Complex.volume_closedBall a ρ :
volume (closedBall a ρ) = ENNReal.ofReal ρ ^ 2 * NNReal.pi` (`@[simp]`, ℂ≅ℝ² proper
space). Finiteness: `ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
ENNReal.coe_lt_top`. The `NNReal.pi` factor coerces silently into `ℝ≥0∞`.

## Session 2026-07-09 (researcher-3) — sharp outer radius shrinks to 2 with degree

**Mode**: REVISIT (built on OQ02OQ02's sharp radius). **Outcome**: progress (full
elaboration clean `[7746/7746]`; olean-write env-blocked SIGBUS-135 → UNVERIFIED;
0 sorry / 0 axiom).

### What I did
- Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ04.lean` (3 theorems). Turned
  the **prose observation** of OQ02OQ02 ("the sharp outer radius `1 + C^{1/φ(n)}`
  decreases to 2 as `φ(n) → ∞`") into theorems.
- `sharpRadius_antitone`: for `C ≥ 1`, `1 ≤ k ≤ k'` ⟹ `1 + C^{1/k'} ≤ 1 + C^{1/k}`
  (outer radius antitone in degree).
- `tendsto_sharpRadius`: for `C > 0`, `Tendsto (fun k => 1 + C^{1/k}) atTop (𝓝 2)`.
- `eventually_levelSet_subset_closedBall`: for `C ≥ 1`, `ε > 0`, ∃ degree threshold
  `K` s.t. EVERY cyclotomic level set `{|Φ_n|<C}` with `φ(n) ≥ K` fits in the one
  fixed disc `closedBall 0 (2+ε)` — uniform confinement of all high-degree
  cyclotomic lemniscates (antithesis of a Mac Lane labyrinth).

### Reusable Lean recipe
- Limit of `C^{1/k}` (`C>0`): rewrite `C^{1/k} = exp(log C · k⁻¹)` via
  `Real.rpow_def_of_pos hC`; `tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop`
  gives `k⁻¹ → 0`; `Tendsto.const_mul (Real.log C)` → arg `→ 0`;
  `(Real.continuous_exp.tendsto 0).comp` + `Real.exp_zero` → `C^{1/k} → 1`;
  `.const_add 1` → radius `→ 2`.
- Extract threshold: `(tendsto_order.1 htend).2 (2+ε) (by linarith)` →
  `∀ᶠ k, radius k < 2+ε`; `eventually_atTop.1` → `∃ K ∀ k ≥ K`.
- Nesting: `Metric.closedBall_subset_closedBall` composes with
  `OQ02OQ02.sublevel_subset_closedBall_sharp`.
- Antitone: `inv_le_inv_of_le hkpos hcast` + `Real.rpow_le_rpow_of_exponent_le`.

### Status / next
- The elementary quantitative side of OQ-02 is now essentially complete: bounded
  (OQ01) → sharp two-sided radii (OQ02) → area squeeze (OQ03) → radius→2 shrinkage
  (this). The genuinely-open driver (small-n `n=3,4,6` lemniscate component/path
  topology) still needs polynomial-lemniscate topology Mathlib lacks — unchanged.
- ★INFRA: worktree `.loom/worktrees/researcher-3` lost its `.git` link mid-session
  (worktree-eater) → `git checkout -b` accidentally switched the MAIN repo branch;
  recovered by copying the file to a fresh external worktree `/Users/rwalters/lg-r3-cyclo`
  off origin/main and restoring main. Elaboration errors ARE visible before the
  SIGBUS write, so correctness is verifiable even when the olean write fails.

## Session 2026-07-09 (researcher-2) — AXIOM ELIMINATION: discharge `maclane_1953` (parent 2→1 axioms)

**Mode**: AXIOM HUNT on the parent `Erdos1215Problem.lean` (score 15). **Outcome**: real axiom
elimination — VERIFIED axiom-free.

The parent file axiomatized `maclane_1953 : ∀ C>1, ∃ P unit-circle, ¬HasBoundedLevelPath P C`
under the label "Mac Lane's deep theorem". But the **literal escape-to-∞ formulation is
elementary**: the degree-one cyclotomic `P = X + 1` is a unit-circle polynomial (`P(0)=1`, sole
root `-1`) whose level set `{z : ‖z+1‖ < C}` is a bounded disc, so `‖z‖ ≤ ‖z+1‖+1 < C+1` there and
no path can escape to `∞`. Prior sessions proved this only in a companion
(`CyclotomicPolynomialsOQ02OQ05.erdos_1215_via_cyclotomic`) — they could NOT discharge the parent
axiom because the cyclotomic file *imports* the parent (circular). This session proves it **directly
and self-contained in the parent** with a short inline argument (no new imports, no cyclotomic
machinery), converting `axiom maclane_1953` → `theorem`. **axiomCount 2 → 1.**

Now `maclane_1953` and the headline `erdos_1215` both `#print axioms` = `[propext,
Classical.choice, Quot.sound]` only. The genuinely deep Mac Lane content — the labyrinth forcing
paths through neighbourhoods of `0` in the `C>1` regime — is the *strictly stronger*
`maclane_labyrinth`, which REMAINS axiomatized, so the entry correctly stays `status: axiomatized`,
`badge: axiom` (no overclaim). This is an integrity improvement: a mislabeled "deep" axiom (actually
elementary) is removed while the real depth stays honestly axiomatized.

**Proof mechanics (reusable).** No-escape contradiction: from `Tendsto (‖γ ·‖) atTop atTop` get
`htend.eventually_gt_atTop (C+1)` and `Filter.eventually_ge_atTop 0`; `(h1.and h2).exists` (atTop
NeBot) yields a `t ≥ 0` with `‖γ t‖ > C+1`, contradicting the level-set bound `‖γ t‖ < C+1`
(`norm_sub_norm_le (γ t) (γ t + 1)` with `γ t - (γ t + 1) = -1` by `ring`, `norm_neg`/`norm_one`).
Root on circle: `IsRoot.def, eval_add, eval_X, eval_one` → `z+1=0`, then
`eq_neg_of_add_eq_zero_left`. NOTE the `C>1` hypothesis is UNUSED (compactness needs no lower bound
on C) → binder renamed `_hC`.

**Verification (docker DOWN).** Containerd meta.db/blob `input/output error` at image build
(operator-level, NOT disk — 157Gi free). Verified by direct `lean` elaboration vs pinned Mathlib
v4.26.0 oleans (see [[reference-docker-down-lean-elab-verification-path]]): exit 0, `#print axioms`
clean. Metas synced: src/data/proofs/erdos-1215/meta.json (axiomCount 2→1, 70→100 lines, 1→2 thm,
assumptions text) + research json leanFiles.

## Session 2026-07-10 (researcher-3) — general degree obstruction (maclane_1953 becomes a corollary)

**Mode**: REVISIT. **Outcome**: progress (1 theorem, axiom-free), **VERIFIED-local**.

Generalized the escape-to-∞ half of `maclane_1953` from the single witness `X + 1` to *every*
positive-degree polynomial, isolating why the literal Erdős #1215 question is trivial:

- `no_bounded_level_path_of_degree_pos {P : ℂ[X]} (hP : 0 < P.degree) (C) : ¬ HasBoundedLevelPath P C`.
  For any non-constant `P`, `‖P(z)‖ → ∞` as `‖z‖ → ∞` (`Polynomial.tendsto_norm_atTop`), so a path
  `γ` with `‖γ t‖ → ∞` forces `‖P(γ t)‖ → ∞`, contradicting `‖P(γ t)‖ < C` on `t ≥ 0`. Proof:
  `P.tendsto_norm_atTop hP htend` then `eventually_gt_atTop C` ∧ `eventually_ge_atTop 0`, `.exists`,
  `linarith` against the level-set membership.

`maclane_1953` is now a corollary: witness `X + 1`, root on the circle as before, and the escape
clause is `no_bounded_level_path_of_degree_pos` with `0 < degree (X+1)` via
`rw [← C_1, degree_X_add_C]; exact WithBot.coe_lt_coe.mpr Nat.one_pos`. This removes the duplicated
13-line escape argument and demonstrates the new lemma strictly subsumes it.

### Key facts / gotchas
- `Polynomial.tendsto_norm_atTop (p) (h : 0 < degree p) (hz : Tendsto (‖z ·‖) l atTop) :
  Tendsto (‖p.eval (z ·)‖) l atTop` — the **norm** form (no cocompact/cobounded plumbing needed);
  lives in `Mathlib.Topology.Algebra.Polynomial` → **added that import** (the file's 3 specific
  imports did not transitively pull it; dot-notation errored "environment does not contain").
- `degree (X + 1) = 1`: `rw [← Polynomial.C_1, degree_X_add_C]`; then `0 < (1 : WithBot ℕ)` via
  `WithBot.coe_lt_coe.mpr Nat.one_pos`.

### Verification
VERIFIED-local (docker image layer down): elan lean v4.26.0 vs main-checkout Mathlib oleans →
exit 0, no warnings. `#print axioms no_bounded_level_path_of_degree_pos` and `#print axioms
erdos_1215` = `[propext, Classical.choice, Quot.sound]` — axiom-free (no `native_decide`, does NOT
touch `maclane_labyrinth`). File 100→113 lines, 2→3 theorems, axiomCount stays 1 (the deep
`maclane_labyrinth` labyrinth axiom, unused by the headline). Meta + research json synced.

### Still open (unchanged)
The genuinely deep Mac Lane labyrinth (`maclane_labyrinth` axiom): paths forced through
neighbourhoods of `0` in the `C > 1` regime — needs polynomial-lemniscate topology Mathlib lacks.

## Session 2026-07-19 (researcher-1) — FIRST admissible-path construction (convex degree-1 cyclotomics)

**Mode**: REVISIT (built on the OQ02OQ01–OQ07 containment/area/radius/symmetry pile).
**Outcome**: progress — VERIFIED axiom-free (`[propext,Classical.choice,Quot.sound]`,
host lean v4.31.0 vs prebuilt mathlib oleans, `lake env lean` exit 0, 0 sorry / 0 axiom).

### What I did
Observed that all six prior iterations prove only *facts about the shape* of the
sublevel set `{|Φ_n|<c}` (bounded, sharp two-sided radii, area squeeze, radius→2,
inner radius, reflection symmetry) — **none constructs the admissible PATH that OQ-02
literally asks for** (a bounded-length curve from 0 to the boundary, staying inside).
Created `proofs/Proofs/CyclotomicPolynomialsOQ02OQ08.lean` (6 decls) supplying that
missing piece for the cases where the sublevel set is convex, i.e. the degree-one
cyclotomics `Φ_1 = X-1`, `Φ_2 = X+1` (discs `ball(±1,c)`).

- `HasStraightEscape P c L`: ∃ ray `γ t = t•v` with `γ 0 = 0`, boundary hit
  `‖P.eval(t₁•v)‖ = c` at `t₁>0`, `‖P.eval(t•v)‖ ≤ c` on `[0,t₁]`, segment length
  `t₁·‖v‖ ≤ L`. **Key move**: use the straight-segment length `t₁·‖v‖` in place of a
  general rectifiable arc length — for a straight path they agree, so the missing
  arc-length infrastructure (the stated blocker of every prior iteration) is bypassed.
- `hasStraightEscape_linear_unitRoot {a} (‖a‖=1) {c} (1<c) : HasStraightEscape (X - C a) c (c-1)`.
  Witness ray `t•(-a)`; along it `‖(X-C a).eval(t•(-a))‖ = (t+1)·‖a‖ = t+1` (t≥0),
  hits `c` at `t₁ = c-1`, length `(c-1)·‖-a‖ = c-1`.
- `cyclotomic_one/two_hasStraightEscape`: instantiate `a=1` / `a=-1` via
  `cyclotomic_one : Φ_1 = X-1` and `cyclotomic_two : Φ_2 = X+1`.
- `cyclotomic_deg_one_hasStraightEscape_linear_bound (n=1∨n=2) (1<c) :
  HasStraightEscape (cyclotomic n ℂ) c (c*n)` — casts the `c-1` bound into the
  OQ-02 `length ≤ c·n` target form (`c-1 ≤ c·n` for `n≥1`).

### Key findings
- The convex (degree-1) cyclotomic case admits an **O(1)-length** admissible escape
  path (`c-1`), independent of `n` — far below the linear `c·n` OQ-02 target. So for
  `n∈{1,2}` cyclotomic geometry is emphatically tame in the strongest (actual-path)
  sense, not merely the containment sense of iters 2–6.
- The straight-ray trick is *exactly* what fails at `n≥3`: `Φ_3,Φ_4,Φ_6` are quadratic,
  their sublevel sets are non-convex lemniscates (can split into two components), so a
  ray from 0 need not stay inside and a genuine path through a possibly-disconnected
  region is required. That is the real open driver and needs Mathlib lemniscate
  topology + arc length — unchanged.

### Reusable Lean recipe
- Along a real-scaled ray `t • v` (`v:ℂ`, `t:ℝ`): `Complex.real_smul : t • v = ↑t * v`
  turns the smul into multiplication; then `eval_sub/eval_X/eval_C`, `ring` to
  `-(↑(t+1))*a`, `norm_neg`, `norm_mul`, `Complex.norm_real`, `Real.norm_eq_abs`,
  `abs_of_nonneg` collapse `‖·‖` to `(t+1)·‖a‖`.
- `cyclotomic_one`/`cyclotomic_two` (`= X-1` / `X+1`); rewrite `X±1 = X - C(±1)` via
  `map_one`/`map_neg` to match a `X - C a` lemma.
- Straight-segment length avoids arc-length infra entirely — the whole point.

### Files modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ08.lean` (new, 6 decls, 0 sorry / 0 axiom)
- `research/problems/erdos-1215-oq-02/{knowledge,state}.md`
- `src/data/research/problems/erdos-1215-oq-02.json`

### Next steps
- `n≥3`: non-convex lemniscate path construction — BLOCKED on Mathlib polynomial-
  lemniscate topology + rectifiable arc length. The elementary surface is now
  saturated (containment/area/radius/symmetry + convex-case path); do not add another
  elementary shape bound.
