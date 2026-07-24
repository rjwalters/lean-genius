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

## Session 2026-07-19 (researcher-1) — escape-region topology (new orthogonal layer)

**Mode**: ACT. **Outcome**: progress — 1 new file, 5 theorems, VERIFIED 0-axiom
(docker `[8579/8579]`, `[propext,Classical.choice,Quot.sound]`).

### What I did
New file `proofs/Proofs/CyclotomicPolynomialsOQ02OQ09.lean`. The 15 prior companions
pinned the **metric** geometry of the sublevel set (radius sandwich both sides sharp,
area sandwich, monotone/antitone, conjugation symmetry). This file adds the one **topological**
fact reachable with the existing sharp outer radius: the far field is a *single connected
escape region*.

- `isPathConnected_norm_gt (R) (hR : 0 ≤ R)` — **general, reusable**: the exterior
  `{z : ℂ | R < ‖z‖}` of a closed ball is path-connected. Proof: it is the continuous
  image of the punctured plane `{0}ᶜ` (path-connected since `dim_ℝ ℂ = 2 > 1`,
  `isPathConnected_compl_singleton_of_one_lt_rank`) under the radial rescaling
  `f w = (R + ‖w‖)‖w‖⁻¹ • w`, via `IsPathConnected.image'`. Avoids needing a product
  path-connectivity lemma (Mathlib has none).
- `not_isBounded_norm_gt` — the exterior is unbounded.
- `exterior_subset_cyclotomic_superlevel` — `{1+C^{1/φ(n)}<‖z‖} ⊆ {C≤|Φ_n(z)|}`
  (contrapositive of `OQ02OQ02.cyclotomic_sublevel_norm_lt_sharp`).
- `cyclotomic_superlevel_exterior_isPathConnected` and headline
  `cyclotomic_superlevel_has_connected_unbounded_subset`: `{C ≤ |Φ_n(z)|}` contains a
  path-connected, unbounded subset. So however intricate the bounded labyrinth `{|Φ_n|<C}`,
  there is exactly one connected way to escape to infinity.

### Key API / gotchas
- `Complex.rank_real_complex ▸ Nat.one_lt_ofNat : 1 < Module.rank ℝ ℂ` (rank = 2).
- The image set-equality is the fiddly part: for the reverse inclusion, the witness is
  `w = (‖z‖-R)‖z‖⁻¹ • z` (so `‖w‖ = ‖z‖-R`, direction of `z`), and `f w = z` closes by
  `smul_smul` + a `field_simp`-discharged scalar identity (`‖z‖-R ≠ 0`, `‖z‖ ≠ 0` in scope).
- Radius point for unboundedness must be provably `≥ 0`: use `M := |R|+|r|+1` (not
  `max R r + 1`, which `positivity` can't sign since `R,r` are arbitrary reals).
- Companion imports need `open Polynomial` for `cyclotomic n ℂ` (autoImplicit otherwise
  swallows `cyclotomic` as an implicit variable → "Function expected").

### Blocked driver (recorded as structured `currentState.blockers` entry)
The genuinely-open Mac Lane path-length driver — connected-**component count** of the
bounded sublevel labyrinth `{|Φ_n|<C}` — remains blocked: Mathlib lacks polynomial-
lemniscate topology / rectifiable-path arc length. The metric frontier (radius/area,
both sides sharp) and now the exterior escape-region topology are the reachable layers;
further sublevel-**component** work needs materially new Mathlib infrastructure.

## Session 2026-07-24 (researcher-3) — exit paths in EVERY direction (OQ08 → directional)

**Mode**: REVISIT (built on OQ02OQ08's first-crossing mechanism + OQ02OQ07's sharp inner ball).
**Outcome**: progress — 1 new file, 9 decls, VERIFIED 0-sorry/0-axiom (docker `[8580/8580]`,
all three headline theorems `[propext, Classical.choice, Quot.sound]`).

### What I did
New file `proofs/Proofs/CyclotomicPolynomialsOQ02OQ10.lean`. OQ02OQ08 exhibited ONE exit
ray (positive real axis); its recorded follow-up asked whether reachability extends beyond
that ray. This file settles the directional half completely:

- `ray_exit`: for EVERY unit direction `u`, the ray `t ↦ t·u` has a first level-`C`
  crossing `t*` with the **two-sided sharp bound** `C^{1/φ(n)} − 1 ≤ t* ≤ 1 + C^{1/φ(n)}`,
  the open segment `[0,t*)·u` staying strictly inside `{|Φ_n| < C}`. The sharp LOWER
  bound is new even for OQ08's `u = 1` case (OQ08 had only the upper bound).
- `levelCurve_meets_every_ray`: the level curve `{|Φ_n| = C}` meets every ray from the
  origin inside the sharp annulus — the boundary radially surrounds the origin with
  `n`-uniform distance (annulus radii → 0 and 2 as `φ(n) → ∞`).
- `ray_exit_pathLength`: explicit straight-segment packaging, Euclidean length
  `= t* ≤ 1 + C^{1/φ(n)}` in every direction.

### Mechanism (reusable)
Parameterized replay of OQ08's first-crossing argument: `rayNorm n u t = |Φ_n(t·u)|`
continuous; `‖t·u‖ = t` for `t ≥ 0`, `‖u‖ = 1` (`norm_ofReal_mul`: `norm_mul` + `hu` +
`Complex.norm_real` + `abs_of_nonneg`); OQ01 lower bound forces crossing at
`R = 1+C^{1/φ(n)}`; NEW ingredient vs OQ08 — OQ07's `ball_sharpInner_subset_levelSet`
forbids a crossing before `C^{1/φ(n)}−1` (by_contra + the inner-ball membership at `t*`),
giving the two-sided pin. First crossing = `sInf` of the closed crossing set
(`IsClosed.csInf_mem`), exactness on the boundary via `intermediate_value_Icc`.
v4.31 note: `push_neg` is deprecated → use `push Not at h`.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ10.lean` (new)
- `src/data/research/problems/erdos-1215-oq-02.json` (knowledge + leanFiles)

### Infra note
Worktree `/Volumes/Stripe/lean-genius/researcher-3` was reaped mid-session (janitor,
pre-commit) — only the freshly Written proof file survived. Recovery: back up file to
/tmp, `git worktree prune` + `git worktree add -B <branch> <path> origin/main`, restore,
commit+push IMMEDIATELY.

### Still open (unchanged)
The remaining half of the reachability refinement: whether every BOUNDARY POINT (not
just every direction's first crossing) is reachable by a bounded-length path inside the
set — that needs the labyrinth-free topology of the full lemniscate (connected-component
count of `{|Φ_n| < C}`), still beyond Mathlib. The directional question is now closed.

## Session 2026-07-24 (researcher-3) — OQ11: quadratic lemniscates DISCONNECT for small C

**Mode**: REVISIT (the recorded tractable layer: explicit small-n geometry, n = 3, 4, 6).
**Outcome**: progress — 1 new file, 26 thm + 4 def, VERIFIED 0-sorry/0-axiom (docker
`[8577/8577]`, clean build, no native_decide).

### What I did
New file `proofs/Proofs/CyclotomicPolynomialsOQ02OQ11.lean` — the FIRST component-topology
result for the family (all prior layers were shape sandwiches or positive path results):

- **General Cassini disconnection engine**: for foci `a, b` and `4C < ‖a−b‖²`, the
  quadratic lemniscate `{z : ‖(z−a)(z−b)‖ < C}` is not preconnected
  (`not_isPreconnected_quadratic_lemniscate`), hence not connected and not path-connected.
- **Instantiations** — `n = 3, 4, 6` are exactly the indices with `φ(n) = 2`:
  `{|Φ₃| < C}`, `{|Φ₆| < C}` disconnected for `0 < C < 3/4` (foci `√3` apart);
  `{|Φ₄| < C}` disconnected for `0 < C < 1` (foci `2` apart).
- **Mathlib-gap byproduct**: `cyclotomic_four : cyclotomic 4 ℂ = X² + 1` (Mathlib has
  `cyclotomic_one/_two/_three/_six` but not `_four`) via
  `cyclotomic_expand_eq_cyclotomic Nat.prime_two` from `Φ₂ = X + 1`.

### Mechanism (reusable)
Covering: a point at distance `≥ √C` from BOTH foci has factor product `≥ C`, so the
lemniscate sits inside `B(a,√C) ∪ B(b,√C)`. Separation: triangle inequality + squaring
makes the balls disjoint when `4C < ‖a−b‖²`. Each ball meets the set at its focus (a
root: `‖(a−a)(a−b)‖ = 0 < C`). Feed this open cover to the `IsPreconnected` definition —
the required point of `S ∩ (B_a ∩ B_b)` lands in the empty intersection. Foci algebra by
`linear_combination` off `a + b` / `a·b` (e.g. `z²+z+1 = (z−ω)(z−ω̄)` is
`linear_combination z*h_add − h_mul`), with `(√3:ℂ)² = 3` by `norm_cast; Real.sq_sqrt`.

### Perspective
- For `n = 1, 2` (`φ = 1`) the sets are exact disks (OQ01) — always connected;
  disconnection first appears exactly at degree `φ(n) = 2`, and OQ11 pins the regime.
- Disconnection regime (`C < 3/4` resp. `1`) and origin-interior regime (`C > 1`, OQ07)
  are disjoint — consistent with the classical Cassini threshold `(|a−b|/2)²`.
- v4.31 renames hit: `Set.eq_empty_iff_forall_not_mem` → `…_notMem`,
  `Set.not_mem_empty` → `Set.notMem_empty`. Also `cyclotomic_expand_eq_cyclotomic` is
  simp-tagged, so `norm_num at h` self-normalizes `expand 2 Φ₂` to `X²+1`.

### Files Modified
- `proofs/Proofs/CyclotomicPolynomialsOQ02OQ11.lean` (new)
- `research/problems/erdos-1215-oq-02/state.md`, `src/data/research/problems/erdos-1215-oq-02.json`

### Still open
- `C > 1` regime component count (the every-boundary-point reachability driver) — still
  needs lemniscate topology beyond Mathlib (blocked, unchanged).
- Small-n follow-ups: sharpness (connectivity for `C ≥ (|a−b|/2)²`), exact component
  count 2 (per-petal connectivity), quartic cases `n = 5, 8, 10, 12` (`φ(n) = 4`).
