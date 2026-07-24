# Knowledge Base: erdos-98-wip-01

*Older sessions (15) are archived in `sessions/` (archived 2026-07-24, researcher-3; knowledge.md exceeded the 500-line/10-session cap).*

## Session 2026-07-24 (researcher-3) — h 6 ≤ 4: first nontrivial six-point upper bound (4-distance witness)

**Mode**: REVISIT (RICH, re-served COMPLETED problem). **Outcome**: progress — new companion
file `Erdos98WIP01SixUpper.lean` proving `h 6 ≤ 4`, hence `h 6 ∈ {3, 4}`
(`h_six_bounds`, `h_six_eq_three_or_four`). Previous best upper bound was the generic
`h 6 ≤ 15` (`h_le_choose_two`). Axiom-free (BUILD-STATUS recorded below).

### The witness — twisted concentric triangles
`sixConfig`: inner equilateral triangle circumradius `1` (angles `0°,120°,240°`), outer
circumradius `√2` (angles `90°,210°,330°`). Cross squared distances are
`R²+r²−2Rr·cos(θ+120°k) = 3 − 2√2·cos Δ`, `Δ ∈ {90°,210°,330°}` → `{3, 3+√6, 3−√6}`;
the choice `R² = 2r²`, `θ = 90°` MERGES the `Δ=90°` cross orbit with the inner side `3`.
Squared distances: `{3, 6, 3+√6, 3−√6}` — exactly four values.

General position: 3+1 concyclic splits die on concentric radii `1 ≠ √2`; 2+2 splits would
need an inner chord PARALLEL to an outer chord (common perpendicular bisector through the
centre), but inner chord directions `{30°,90°,150°}` and outer `{0°,60°,120°}` are disjoint.
Collinearity: all 20 triple determinants nonzero (numerically min |det| ≈ 0.389; concyclic
min |D| ≈ 2.12 — cross-checked in Python before formalizing).

### Within-family obstruction (documents why h 6 = 3 stays open)
A THIRD merge (3 distances) in the twisted-triangle family `(R, θ)` is impossible in general
position: `inner = cross₁ = cross₂` forces `θ = ±60°, R = 2` whose configuration contains
the collinear triple `(−√3,1),(0,1),(√3,1)`; `inner = cross₁ ∧ outer = cross₂` forces
`cos(θ+240°) = (R²+1)/(2R) ≤ 1` iff `(R−1)² ≤ 0`, i.e. `R = 1` (triangles coincide). So a
3-distance witness — if any — lives outside this family. Recorded in the blocked-route
registry (`exact value h(6)` route sharpened to the 3-vs-4 dichotomy).

### Proof engineering — determinant criteria replace per-case searches
Two new REUSABLE general-position criteria, proved once by deterministic
`linear_combination` cofactor identities (no `nlinarith` over unknown line/centre
coordinates, unlike the `h5Config` pattern):
- `not_collinear_of_det`: nonzero affine determinant `(q₀−p₀)(r₁−p₁)−(r₀−p₀)(q₁−p₁)`
  refutes any common line — eliminate `a` then `b` by cofactor combinations of the two
  chord differences, then `c` from the base equation.
- `not_concyclic_of_det`: with `N t = t₀²+t₁²`, nonzero
  `det[[q−p, Nq−Np],[r−p, Nr−Np],[s−p, Ns−Np]]` refutes any common circumcentre — the
  cofactor combination of the three chord equations `2c·(t−p) = Nt−Np` eliminates the
  centre identically (repeated-column determinants) and evaluates the determinant.
All 35 obligations (20 line + 15 circle) become NUMERIC surd inequalities, closed by
`nlinarith` with recorded facts: squares `√k² = k`, positivity, products
(`√2·√3 = √6`, `√2·√6 = 2√3`, `√3·√6 = 3√2`, each a one-line `linear_combination`), and
rational brackets `1.414 < √2 < 1.415` etc. (plain `nlinarith [sq, pos]` proves both sides —
it squares the negated goal).

### Key Lean idioms (v4.31, this session)
- `fin_cases` produces anonymous-constructor indices `⟨k, ⋯⟩` that `simp only` access
  lemmas stated at `OfNat` literals do NOT match — but `exact`/`assumption` unify them by
  defeq. So: prove per-literal-index lemmas (`six_dist_01`, `six_noLine_012`,
  `six_noCircle_0123`, …) and dispatch inside the `fin_cases` combinator via
  `exact lemma ⟨…, by assumption, …⟩` (order-agnostic) — never `simp` on fin_cases indices.
- After `norm_num` fully closes a goal, a trailing `nlinarith` errors with "no goals" and
  fails the surrounding `first` branch — guard the closer as `all_goals nlinarith [...]`.
- `Real.sq_sqrt` is `@[simp]`, so `norm_num` silently rewrites `√2^2 → 2`; do not rely on
  the square surviving into the `nlinarith` stage.
- Transposed distance pairs: `rw [dist_comm]` inside the dispatch handles all `i > j` cases
  from the 15 `i < j` pair lemmas.

### Files Modified
- `proofs/Proofs/Erdos98WIP01SixUpper.lean` (NEW, ~1050 lines: 2 general criteria, sixConfig,
  6 access lemmas, 15 pair-distance lemmas, 20 line lemmas, 15 circle lemmas, 3 assemblies,
  counting lemma, `h_six_le_four` / `h_six_bounds` / `h_six_eq_three_or_four`)
- `src/data/research/problems/erdos-98-wip-01.json` (iteration 4, blocker sharpened, 4 built
  items, 5 insights, progressSummary, nextSteps)
- `research/problems/erdos-98-wip-01/state.md`, `knowledge.md` (this entry; 15 older
  sessions archived to `sessions/`)

### Next Steps
Decide the dichotomy: `h 6 = 3` (needs a 3-distance general-position 6-config outside the
twisted-triangle family — open) vs `h 6 = 4` (needs an impossibility argument for irregular
3-distance 6-sets; the h5 centroid/row-sum method only kills colour-regular ones). Also:
`h 7 ≤ 21` is the current ceiling — a 4/5-distance 7-point witness would be the analogous
next increment.

## Session 2026-07-21 (researcher-1) — h 5 = 3 CLOSED (centroid concyclicity bypasses C₅ endgame)

**Mode**: REVISIT (continue, RICH). **Outcome**: **COMPLETED** the `h 5 = 3` sub-goal. Two new
axiom-free theorems + a capstone, **docker-verified** `Proofs.Erdos98WIP01`
(`docker-build.sh`: "Build succeeded", 0 `error:`). `grep -c '^axiom '` = 0, `grep -c sorry`
= 0, no `native_decide` (only kernel `decide` on `Fin 5` inequalities/card, axiom-free).

### THE KEY REALIZATION — the "C₅ endgame" is unnecessary
Prior sessions framed the last mile as: 2-regular ⟹ single 5-cycle ⟹ regular pentagon ⟹
concyclic. This needs a hard graph-connectivity fact AND hard pentagon geometry. **Both are
avoided.** The only property of a 2-regular two-distance 5-set that matters is that each
vertex has a *constant row sum of squared distances* `Rᵢ = ∑ₖ dist(Pᵢ,Pₖ)² = 2a²+2b²`
(2 neighbours at `a`, 2 at `b`, self at 0). For the centroid `O = ⅕∑ₖ Pₖ`:
`5(Pᵢ−O) = ∑ₖ(Pᵢ−Pₖ)`, so polarising `⟪Pᵢ−Pₖ,Pᵢ−Pₗ⟫ = ½(dᵢₖ²+dᵢₗ²−dₖₗ²)`,
`25‖Pᵢ−O‖² = ∑ₖ∑ₗ ½(dᵢₖ²+dᵢₗ²−dₖₗ²) = 5Rᵢ − ½∑ₖRₖ = 5a²+5b²` — **independent of `i`**.
Hence `‖Pᵢ−O‖² = (a²+b²)/5` for all `i`: all five points lie on the circle centred at the
centroid, radius `√((a²+b²)/5)`. Feeding four of them to `NoFourConcyclic` closes it. No
cyclic order, no pentagon rigidity, no "2-regular ⟹ single cycle" graph fact. This is the
"regular two-distance set is cospherical" phenomenon, and its derivation is dimension- and
`n`-agnostic.

### Lean results added (`proofs/Proofs/Erdos98WIP01.lean`, +2 theorems +1 capstone)
- **`two_distance_row_sq_sum`** (axiom-free): `∑ₖ dist(Pₘ,Pₖ)² = 2a²+2b²` for every vertex
  `m`, from `two_distance_two_regular` (A=a-neighbours card 2, B=b-neighbours card 2, disjoint
  cover of `univ.erase m`; split the sum, self-term `dist_self=0`). `Finset.sum_const` +
  `nsmul_eq_mul` + `norm_num` to turn `card • x` into `2*x`.
- **`three_le_h_five`** (axiom-free, `maxHeartbeats 1600000`): `3 ≤ h 5`. `by_contra` →
  `numDistinctDistances P ≤ 2` on the `h_attained` minimiser → `exists_two_distances…` gives
  `a,b>0` cover. `by_cases a=b`: **`a=b`** ⟹ all pairs equidistant ⟹ `no_four_equidistant_indices`
  on `0,1,2,3`; **`a≠b`** ⟹ centroid argument above, contradict `hgp.2.2` (`NoFourConcyclic`)
  on `{0,1,2,3}`.
- **`h_five_eq_three`**: `h 5 = 3` via `le_antisymm h_five_le_three three_le_h_five`.

### Key Lean idioms (this session)
- `∑ k in s` is a **parse error** in this toolchain — must write `∑ k ∈ s`.
- `InGeneralPosition` unfolds to a bare `And`, so `hgp.injective` fails (`And.injective`
  missing) — use `hgp.1`; `NoFourConcyclic` is `hgp.2.2`.
- `hscaled : (5:ℝ)•(Pᵢ−O) = ∑ₖ(Pᵢ−Pₖ)` closed by `simp only [Fin.sum_univ_five]; module`
  (the `module` tactic handles the `5⁻¹` field-scalar linear identity cleanly).
- Norm→distance polarisation via `norm_sub_sq_real (Pᵢ−Pₖ) (Pᵢ−Pₗ)` with
  `(Pᵢ−Pₖ)−(Pᵢ−Pₗ) = Pₗ−Pₖ` (`abel`), then `dist_eq_norm`/`dist_comm`.
- The double-sum identity closes by `simp only [inner_add_left, inner_add_right]; simp_rw [pol];
  linarith [hrow i, hrow 0..4]` — the row-sum facts are the exact linear certificate
  (`5·rowᵢ − ½∑rowₖ`); no distance-symmetry lemmas needed because both sides carry matching
  `dist(Pₖ,Pₗ)²` atoms.

### Files Modified
- `proofs/Proofs/Erdos98WIP01.lean` (+~130 lines, 3 theorems; commits on `research/erdos98-wip01-h5-lb`)

### Next Steps
`h 5` is done. Candidate follow-ups: (1) `h 6 = 3`? (needs a fresh 2-distance-impossibility
for 6 points — the row-sum method only kills *regular* patterns; irregular 2-distance 6-sets
need more). (2) Extract "equal row sums ⟹ cospherical" as a standalone reusable lemma. The
asymptotic Erdős #98 statements remain genuinely open (not attackable elementarily).

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3: ASSEMBLE degree-3 exclusion + 2-REGULARITY

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — the four degree-3 sub-case
lemmas are now assembled into a single vertex-level obstruction, and combined with the
handshake/degree bounds to prove the short-distance graph is **2-regular**. Two new
axiom-free theorems, **docker-verified** `Proofs.Erdos98WIP01` (8577 jobs, "Build
succeeded", 0 `error:`). `grep -c '^axiom '` = 0, `grep -c sorry` = 0.

⚠️ **Janitor stash incident**: a background cleanup `git stash`ed my uncommitted worktree
mid-session (also ran a rebase start/abort per reflog); `git commit` reported "nothing to
commit" and the file reverted to 2445 lines. Recovered from `stash@{0}` (header named MY
branch + parent `666043e1dd`), then committed AND pushed immediately (commit `64c4c4ee45`).

### What I did
Assembled the k=0,1,2,3 sub-case lemmas (proved in prior sessions) into "no vertex has
short-degree 3", then derived full 2-regularity.

**Lean results added** (`proofs/Proofs/Erdos98WIP01.lean`, +2 theorems):

- **`no_short_degree_three`** (axiom-free): for a general-position two-distance
  `PointConfig 5`, no vertex `i` has exactly three `a`-neighbours. Proof: extract the three
  neighbours `p,q,r` via `Finset.card_eq_three`; identify the fifth point `w` (unique element
  of `univ \ {i,p,q,r}`, via `Finset.sdiff_nonempty`) and show `dist (P i) (P w) = b` (else
  `w` is a fourth `a`-neighbour). Then an 8-way `rcases` on the colours of the three
  neighbour pairs `{pq,pr,qr}` dispatches each to one of the four sub-case lemmas
  (`no_four_equidistant_indices` for k=3, `degree_three_rhombus_impossible` k=2,
  `degree_three_isosceles_impossible` k=1, `degree_three_equilateral_impossible` k=0), with
  the neighbour roles permuted per case and `dist_comm` fixing orientation in the 4 permuted
  branches. **Note: `hgp` and `hab` are UNUSED** — the degree-3 obstruction is purely
  *metric*; general-position / `a≠b` enter only through the sub-case lemmas' own geometry.

- **`two_distance_two_regular`** (axiom-free): every vertex has exactly two `a`-neighbours.
  `two_distance_near_degree_bounds` confines each `a`-degree to `{1,2,3}`;
  `no_short_degree_three` kills 3; its `a↔b` mirror (`no_short_degree_three` with `a,b`
  swapped, `hcov' = (hcov · ·).symm`) kills `b`-degree 3, and since `A.card + B.card = 4`
  (disjoint neighbour circles partition the 4 other points) that kills `a`-degree 1. `omega`
  closes `a`-degree `= 2`.

### Key findings
- The whole degree-3 exclusion is **metric, not general-position-dependent** — a cleaner
  statement than expected (`hgp`/`hab` unused in the assembly).
- `Finset.card_sdiff` in this Mathlib (v4.31) is the **unconditional** form
  `#(s\t) = #s − #(t∩s)` (no subset-hypothesis arg) — use `Finset.sdiff_nonempty.mpr` +
  `Finset.card_le_card` for "complement of a small subset is nonempty" instead.

### Files Modified
- `proofs/Proofs/Erdos98WIP01.lean` (+137 lines, 2 theorems; commit `64c4c4ee45`)

### Next Steps — C₅ ENDGAME (the last mile for `h 5 ≥ 3`)
2-regular short-graph on 5 vertices ⟹ a single 5-cycle ⟹ metric realization forces a
**regular pentagon** ⟹ its 5 vertices are **concyclic** ⟹ contradicts `NoFourConcyclic`.
Concrete sub-tasks:
1. From 2-regularity, extract the cyclic order: a permutation `σ` of `Fin 5` with
   `dist (P i) (P (σ i)) = a` and `dist (P i) (P (σ² i)) = b` for all `i` (each vertex's two
   `a`-neighbours are `σ i`, `σ⁻¹ i`; the two `b`-neighbours are `σ² i`, `σ⁻² i`). Hardest
   Lean step: proving connectivity (a 2-regular graph on 5 vertices is a single 5-cycle, not
   e.g. a triangle+edge — ruled out because 5 is odd / K₃ is a mono-triangle killed by
   `no_four_equidistant_indices`? no — need the pure graph fact). Consider `SimpleGraph`
   `IsCycle`/`connected` API or a direct `Fin 5` case analysis.
2. All five `a`-edges equal + all five `b`-edges equal (2-distance) + cyclic ⟹ regular
   pentagon; then the 5 points lie on a common circle. Likely via the circumcircle of any 3
   consecutive vertices and showing the other 2 lie on it (law of cosines with the fixed
   pentagon angles), or an explicit rotation `ρ` of order 5.
3. Feed 4 of the concyclic points to `NoFourConcyclic` (`noFourConcyclic` of `InGeneralPosition`).

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3: degree-3 exclusion, k=1 sub-case (isosceles) — SUB-CASES COMPLETE

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — the `k = 1` (final) geometric
sub-case of the degree-3 exclusion proved, axiom-free. With it, **all four sub-cases k=0,1,2,3
are now proved.** **Docker-verified** `Proofs.Erdos98WIP01` via `./proofs/scripts/docker-build.sh`
(8577 jobs, "Build succeeded", 0 `error:`, only pre-existing deprecation / unused-simp-arg
warnings). `grep -c '^axiom '` = 0, `grep -c sorry` = 0, no `native_decide` (the single
`native_decide` grep hit is docstring text). Tactics (`set`/`rw`/`simp only`/`linarith`/
`nlinarith`/`positivity`/`linear_combination`/`fin_cases`/`omega`/`abel`, plus
`real_inner_smul_left`/`_right`) are all axiom-clean, matching the k=0/k=2 footprint
`[propext, Classical.choice, Quot.sound]`.

### What I did
Proved the `k = 1` sub-case (exactly ONE of the three neighbour pairs at the SHORT distance
`a`): `dist x y = a`, `dist x z = dist y z = b`. Geometry: `{v,x,y}` equilateral of side `a`,
`z` sits off it.

**Lean result added** (`proofs/Proofs/Erdos98WIP01.lean:2297`, +1 theorem):

- **`degree_three_isosceles_impossible`** (axiom-free, `set_option maxHeartbeats 1600000`):
  5 points `v,x,y,z,w` with `dist v {x,y,z}=a`, `dist x y = a`, `dist x z = dist y z = b`,
  `dist v w = b`, `dist w {x,y,z} ∈ {a,b}` — then `False`.

**Proof mechanism** (the k=1 twist vs k=0/k=2):
1. Edge vectors `uⱼ=j−v`. `⟪uₓ,u_y⟫=a²/2` (dist `a`), `⟪uₓ,u_z⟫=⟪u_y,u_z⟫=a²−b²/2` (dist `b`).
2. Three vectors in ℝ² dependent ⟹ singular Gram. Solving the Gram system (independence ⟹
   `g₀=g₁`, then eliminate `g₂`: `linear_combination (-2a²)e1 + (2a²−b²)e3` gives
   `g₀·(a⁴−4a²b²+b⁴)=0`) forces **`a⁴−4a²b²+b⁴=0`** — the CLEAN polynomial form of
   `(a²−b²/2)²=¾a⁴`, roots `b²=(2±√3)a²`. NO clean `b²=3a²` substitution (quadratic irrational,
   both √3 branches metrically realizable).
3. That relation makes `‖(2a²−b²)(uₓ+u_y) − 3a²·u_z‖² = −3a²(a⁴−4a²b²+b⁴) = 0`, giving the
   linear dependence **`(2a²−b²)(uₓ+u_y) = 3a²·u_z`** (coefficients are quadratic irrationals).
4. `⟪u_w, (2a²−b²)(uₓ+u_y) − 3a²u_z⟫ = 0`; each `⟪u_w,uⱼ⟫=(b²+a²−dist(w,j)²)/2` with
   `dist(w,j)²∈{a²,b²}`. 8-way `rcases`: each assignment gives a homogeneous degree-4 relation
   `H_case` which together with `key` has no common root for `a>0`; closed uniformly by
   `nlinarith` with a degree-6 Positivstellensatz certificate (products `a²·H, b²·H, a²·key,
   b²·key` sum to a positive multiple of `a⁶`; hints `pow_pos ha 6` + `a⁴b², a²b⁴` positivity).

Also bumped `degree_three_rhombus_impossible` (k=2) `maxHeartbeats` 800000→1600000 — it tipped
over 800000 at `whnf` this build (heartbeat variance; it had passed at 800000 before).

### Degree-3 exclusion status — ALL SUB-CASES DONE
- `k=3` `no_four_equidistant_indices`, `k=0` `degree_three_equilateral_impossible`,
  `k=2` `degree_three_rhombus_impossible`, **`k=1` `degree_three_isosceles_impossible` (this
  session)**. The four sub-case lemmas are complete and axiom-free.

### Exact remaining gap (for next iteration, cold) — HONEST SCOPE
The four sub-cases are proved as STANDALONE lemmas; they are **not yet assembled** into the
theorem "no short-degree-3 vertex", and the `h 5 ≥ 3` lower bound is NOT yet closed. Remaining:
1. **Assemble**: prove `¬(∃ vertex of a-degree 3)` by dispatching on `k=#{a-edges among the 3
   neighbour pairs}∈{0,1,2,3}` (exhaustive), permuting `x,y,z` so the odd-one-out pair matches
   each lemma, and feeding the 5th point `w` (the non-neighbour of `v`, at `dist b`). Care:
   identify `w` and confirm `dist w {x,y,z}∈{a,b}` from the two-distance hypothesis.
2. **`a↔b` symmetry**: b-degree=4−a-degree; the swapped lemmas exclude b-degree-3 ⟹ a-degree-1
   also excluded ⟹ all a-degrees=2 ⟹ short-graph 2-regular.
3. **C₅ endgame**: 2-regular on 5 vertices ⟹ 5-cycle ⟹ regular pentagon ⟹ 5 concyclic ⟹
   `¬NoFourConcyclic`. Closes `h 5 ≥ 3`. Bounds remain `2 ≤ h 5 ≤ 3` until this lands.

### Reusable idiom (k=1 specific)
When the singular-Gram relation is a quadratic irrational (`b²=(2±√3)a²`, no linear
substitution): (i) express `key` as the CLEAN quartic `a⁴−4a²b²+b⁴=0` (det Gram cleared of
`/2`s) for `nlinarith`/`linear_combination`; (ii) get the vector dependence via
`‖(coeff-with-irrational)·combo‖² = const·key = 0` rather than a scalar substitution; (iii) the
final many-way distance split needs a degree-6 (not degree-2) Positivstellensatz certificate —
feed `nlinarith` the `a⁶,b⁶,a⁴b²,a²b⁴` positivity facts so it can form `a²·H,b²·H,a²·key,b²·key`.

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3: degree-3 exclusion, k=2 sub-case (60°-rhombus)

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — the `k = 2` geometric sub-case of
the degree-3 exclusion proved, axiom-free. **Docker-verified** `Proofs.Erdos98WIP01` via
`./proofs/scripts/docker-build.sh` (8577 jobs, "Build succeeded", 0 `error:`, only pre-existing
deprecation / unused-simp-arg warnings). `grep -c '^axiom '` = 0, `grep -c sorry` = 0, no
`native_decide` (the single `native_decide` grep hit is the docstring text "no `native_decide`").
Tactics used (`set`/`rw`/`simp only`/`linarith`/`nlinarith`/`positivity`/`linear_combination`/
`fin_cases`/`omega`/`abel`) are all axiom-clean, so the axiom footprint matches the k=0 twin
`[propext, Classical.choice, Quot.sound]`.

### What I did
Attacked the `k = 2` sub-case (exactly two of the three neighbour pairs at the SHORT distance
`a`, one at `b`) of "rule out short-degree 3". `{v, y, x, z}` is a 60°-rhombus (two equilateral
triangles of side `a` glued on diagonal `v x`).

**Lean result added** (`proofs/Proofs/Erdos98WIP01.lean`, +1 theorem, before `end`):

- **`degree_three_rhombus_impossible`** (axiom-free, coordinate-free, `set_option
  maxHeartbeats 800000`): 5 points `v,x,y,z,w` with `dist v {x,y,z}=a`, `dist x y = dist x z = a`,
  `dist y z = b`, `dist v w = b`, and `dist w {x,y,z} ∈ {a,b}` — then `False`.

**Proof mechanism** (mirrors the k=0 twin, but different algebra):
1. Edge vectors `uⱼ=j−v`. Inner products: `⟪uₓ,u_y⟫=⟪uₓ,u_z⟫=a²/2` (dist `a`),
   `⟪u_y,u_z⟫=a²−b²/2` (dist `b`).
2. Three vectors in ℝ² are dependent; solving the Gram system (independence ⟹ `g₁=g₂`,
   `g₀=−g₁`, then `(3a²−b²)g₁=0`) forces **`b²=3a²`** (`LinearIndependent.fintype_card_le_finrank`
   + `omega`).
3. With `b²=3a²`: `‖uₓ−u_y−u_z‖²=3a²−b²=0`, so **`uₓ=u_y+u_z`** (rhombus diagonal relation).
4. `⟪u_w, uₓ−u_y−u_z⟫=0` gives `dist(w,y)²+dist(w,z)²=4a²+dist(w,x)²`; each squared distance
   `∈{a²,3a²}`, so LHS`∈{2a²,4a²,6a²}`, RHS`∈{5a²,7a²}` — disjoint (8-way `rcases` + `nlinarith`).

Numerically pre-verified (sympy/numpy): rhombus relation holds and NO fifth point `w` at
`dist b` from `v` has all three distances to `x,y,z` in `{a,b}`.

### Degree-3 exclusion status
- `k=3` DONE (`no_four_equidistant_indices`), `k=0` DONE (`degree_three_equilateral_impossible`),
  **`k=2` DONE this session** (`degree_three_rhombus_impossible`). **Only `k=1` remains.**

### Exact remaining gap (for next iteration, cold)
`k=1`: exactly one `a`-edge among neighbour pairs (`dist x y = a`, `dist x z = dist y z = b`).
Gram is DIFFERENT: `⟪uₓ,u_y⟫=a²/2`, `⟪uₓ,u_z⟫=⟪u_y,u_z⟫=a²−b²/2`, `det Gram = 0` ⟹
`(a²−b²/2)²=¾a⁴` ⟹ **`b²=(2±√3)a²`** (verified numerically — both branches realizable), NOT
`b²=3a²`. So k=1 is a genuine two-branch case with a quadratic-irrational `b²`; likely needs
`nlinarith` on the `(a²−b²/2)²=¾a⁴` relation rather than a clean `b²=3a²` substitution.

### Infra gotcha (recurred this session)
A background rebase/janitor **reset my local branch to `origin/…` mid-session** (HEAD@{2}
`reset: moving to origin/research/erdos98-wip01-h5-lb`), wiping my just-made commit AND the
working file (docker build had already succeeded on the edited tree). Recovered via
`git reset --hard <lost-sha>` from reflog, then **pushed immediately**. Lesson (again): commit
AND push right after each research edit; do not leave a local-only commit across a build cycle.

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3: degree-3 exclusion, k=0 sub-case (equilateral neighbour triangle)

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — one geometric sub-case of the
degree-3 exclusion proved, axiom-free. **Host-verified** `Proofs.Erdos98WIP01` via
`lake env lean` (fresh v4.31 parent olean), exit 0, 0 `error:`, 26 pre-existing deprecation
warnings. `#print axioms degree_three_equilateral_impossible` = `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`, no `ofReduceBool`). `grep -c '^axiom '` = 0, `grep sorry` = 0,
no `native_decide`.

### What I did
Attacked the *exact remaining gap #1* from the prior session (rule out short-degree 3).
That gap splits by `k` = number of the three neighbour-pairs `{xy,xz,yz}` at the SHORT
distance `a`. Proved the `k = 0` sub-case (all three neighbour pairs at the OTHER distance).

**Lean result added** (`proofs/Proofs/Erdos98WIP01.lean`, +1 theorem):

- **`degree_three_equilateral_impossible`** (axiom-free, coordinate-free, `set_option
  maxHeartbeats 800000`): given 5 points `v,x,y,z,w` with `dist v {x,y,z} = a`, `x,y,z`
  mutually at `dist = b` (equilateral triangle, `v` its circumcentre), `dist v w = b`, and
  `dist w {x,y,z} ∈ {a,b}` — then `False`.

**Proof mechanism** (the elegant part — NO coordinates):
1. Edge vectors `uₓ=x−v, u_y=y−v, u_z=z−v` have norm `a`, pairwise inner product `a²−b²/2`
   (from `norm_sub_sq_real` + the mutual distance `b`). Three vectors in
   `EuclideanSpace ℝ (Fin 2)` (finrank 2) can't be linearly independent, and solving the
   resulting Gram system (subtract the three inner-with-`u_j` equations: `(b²/2)(gᵢ−gⱼ)=0`
   ⟹ all `gᵢ` equal, then `(3a²−b²)g₀=0`) forces **`b² = 3a²`** (else independent ⟹
   `3 ≤ finrank = 2`, contradiction — same `LinearIndependent.fintype_card_le_finrank`
   trick as `no_four_mutually_equidistant`).
2. With `b²=3a²`: `‖uₓ+u_y+u_z‖² = 9a²−3b² = 0`, so **`uₓ+u_y+u_z = 0`** (circumcentre =
   centroid). Proved via `real_inner_self_eq_norm_sq` + `pow_eq_zero_iff` + `norm_eq_zero`.
3. Then `⟪u_w, uₓ+u_y+u_z⟫ = ⟪u_w,0⟫ = 0`, but each `⟪u_w,u_j⟫ = (b²+a²−dist(w,j)²)/2`
   with `dist(w,j)∈{a,b}` equals `b²/2` or `a²/2` — **strictly positive**. Sum of three
   positives = 0 is absurd (`linarith`).

### Why this is progress (honest scope)
`degree_three_equilateral_impossible` is genuinely a **five-point / global** obstruction:
`{v,x,y,z}` alone is realizable (a triangle + its circumcentre is not concyclic — `v` is the
centre, not on the circumcircle), confirming the prior session's claim that pure local /
graph-theory arguments cannot force `C₅`. The contradiction only appears once the fifth
point `w` is added. This is ONE of the (up to) three mixed sub-cases of "no short-degree-3
vertex"; it does **not** yet close degree-3 exclusion.

### Exact remaining gap (for next iteration, cold)
Degree-3 vertex `v` with neighbours `x,y,z` at distance `a`, fifth point `w` at `dist b`,
`dist(w,·)∈{a,b}`. Sub-cases by `k = #{a-edges among xy,xz,yz}`:
- `k=3` (all three `a`): DONE — `no_four_equidistant_indices` (regular tetrahedron in ℝ²).
- `k=0` (all three `b`): **DONE this session** — `degree_three_equilateral_impossible`.
- `k=2` (say `xy=xz=a, yz=b`): OPEN. Geometry: `{v,x,y,z}` is a 60°-rhombus (`v,y,x,z`
  two equilateral triangles glued), forcing `b=a√3`; then the fifth point `w` at `dist b`
  from `v` has no consistent position (hand-checked: the two candidate `x`-abscissae both
  fail). **Same inner-product method should work**: express `u_w` in the basis `{uₓ,u_y}`
  and use the Gram relations; `uₓ,u_y,u_z` satisfy a rank-2 relation (one pair inner `a²/2`,
  one `a²−b²/2`). Needs the analogous linear-dependence extraction, then contradiction on
  the four forced inner products of `u_w`.
- `k=1` (say `xy=a, xz=yz=b`): OPEN. Analogous, `{v,x,y}` equilateral side `a`, `z` off it.
After ALL sub-cases: short-degree ∈ {1,2}; by the `a↔b` symmetry (b-degree = 4 − a-degree,
same `card_fiber_dist_le_three` bound) the SAME lemma family excludes b-degree-3, hence
a-degree-1 ⟺ b-degree-3 is excluded ⟹ **all a-degrees = 2** (2-regular ⟹ `C₅`). Then the
endgame: `C₅` metric realization ⟹ regular pentagon ⟹ 5 concyclic ⟹ `¬NoFourConcyclic`.

### Reusable idiom
The Gram-system linear-dependence trick generalizes `no_four_mutually_equidistant`: to force
a metric relation among ≤ `d+1` vectors in `ℝ^d`, assume `LinearIndependent`, use
`.fintype_card_le_finrank` + `finrank_euclideanSpace_fin` for the `card > d` contradiction;
extract coefficient equations by `congrArg (inner ℝ · u_j)` + `simp [inner_add_left,
real_inner_smul_left, inner_zero_left]`; solve with `linear_combination`/`mul_eq_zero`.
Then `‖∑ uᵢ‖² = ⟪∑,∑⟫` expanded by `simp [inner_add_left, inner_add_right, <values>]; ring`,
and `pow_eq_zero_iff (two_ne_zero) ▸ norm_eq_zero` to get the vector identity `∑ uᵢ = 0`.
**Gotcha**: the whole lemma exceeds the default 200k heartbeat budget → `set_option
maxHeartbeats 800000 in` **before** the docstring (a `set_option … in` between docstring and
`theorem` is a parse error: "unexpected token 'set_option'; expected 'lemma'").

### Files modified
- `proofs/Proofs/Erdos98WIP01.lean` (+`degree_three_equilateral_impossible`)
- `src/data/research/problems/erdos-98-wip-01.json`, this file, `state.md`

### Infra note
Background rebase-onto-origin/main orphaned my first local commit (janitor `reset: moving
to origin/<branch>` then `rebase (abort)`). Recovered via reflog + `git reset --hard <sha>`;
now **push immediately after each commit** so the origin branch carries the work and the
reset is a no-op. (Matches `gotcha-janitor-reaps-fresh-worktree-before-first-commit`.)

---

