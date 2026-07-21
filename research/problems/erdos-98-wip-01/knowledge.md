# Knowledge Base: erdos-98-wip-01

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

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3: handshake parity obstruction (some vertex has exactly 2 short neighbours)

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — one new structural step on the
critical path to `h 5 ≥ 3`, axiom-free. **Host-verified** `Proofs.Erdos98WIP01` via
`lake env lean` (fresh v4.31 parent olean), exit 0, no `error:` (only pre-existing
`EuclideanSpace.single_apply` deprecation warnings at line 451); file now 1964 lines,
`grep -c '^axiom '` = 0, `grep -c 'sorry'` = 0, no `native_decide`.

### What I did
Advanced the residual reduction (`h 5 ≥ 3` ⟺ no general-position `PointConfig 5` is a
2-distance set) by proving a **parity obstruction** that begins forcing 2-regularity of the
short-distance graph.

**Lean results added** (`proofs/Proofs/Erdos98WIP01.lean`):

- **`even_sum_symm_degree`** (axiom-free, general): for any symmetric, irreflexive
  `DecidableRel r` on a `Fintype`, `Even (∑ i, #{j ≠ i : r i j})`. This is the handshaking
  lemma, routed through Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges` (RHS
  `2 · #edges`, manifestly even). Key formalization notes: build the `SimpleGraph` literal
  with `symm := ⟨hsymm⟩ : Std.Symm r`, `loopless := ⟨hirr⟩ : Std.Irrefl r`; set
  `DecidableRel G.Adj := fun a b => inferInstance` (NOT `Classical.decRel`, which forks the
  filter's `DecidablePred` instance and breaks the final `rw`/`convert`); close the pointwise
  `degree = filter-card` goal by `convert h2 using 2 with i` then inline
  `neighborFinset_eq_filter` (uses the goal's own instance, avoiding the mismatch).
- **`two_distance_exists_degree_two`** (axiom-free): a general-position 2-distance
  `PointConfig 5` has **some vertex with exactly 2 short-distance (`a`) neighbours**.
  Mechanism: `two_distance_near_degree_bounds` gives each short-degree `d_a(i) ∈ {1,2,3}`;
  `even_sum_symm_degree` (with `r i j := dist (P i) (P j) = a`, symmetric via `dist_comm`,
  irreflexive since `a > 0` — realised from vertex 0) makes `∑_i d_a(i)` even; a sum of five
  odd numbers is odd, so not all `d_a(i)` are odd ⇒ some equals 2. Closed by
  `Fin.sum_univ_five` + `omega` on per-vertex `% 2 = 1` facts.

### Why this is progress (honest scope)
This is the FIRST pin of a specific degree value. It does **not** yet give 2-regularity: it
guarantees *one* degree-2 vertex, not all five. A sum of five values in `{1,2,3}` that is even
can still be e.g. `(1,1,3,3,2)` — so degrees 1 and 3 are not yet excluded.

### Exact remaining gap (for the next iteration to pick up cold)
1. **Rule out short-degree 3** (equivalently long-degree 1, by the `a ↔ b` symmetry of the
   two-distance hypothesis). This is the genuinely *geometric* step: if a vertex `v` has three
   short-neighbours `x,y,z` on the radius-`a` circle about `v`, the two-distance constraint on
   `{x,y,z}` together with no-3-collinear / no-4-concyclic must be shown contradictory. Pure
   graph theory (degrees in `{1,2,3}`, both `G` and `Gᶜ` `K₄`-free) does **not** force `C₅`.
   Precise lemma to prove: `∀ i, ((univ.erase i).filter (fun j => dist (P i) (P j) = a)).card = 2`.
2. After full 2-regularity: `2-regular on Fin 5 ⟹ single 5-cycle C₅` (finite/decidable);
   then `C₅` two-distance realisation ⟹ regular pentagon ⟹ 5 concyclic ⟹ contradicts
   `NoFourConcyclic` ⟹ `h 5 ≥ 3`.

### Files modified
- `proofs/Proofs/Erdos98WIP01.lean` (+2 theorems, `even_sum_symm_degree`, `two_distance_exists_degree_two`)
- `src/data/research/problems/erdos-98-wip-01.json` (knowledge accumulation)

---

## Session 2026-07-21 (researcher-1) — h 5 ≥ 3 reduced to pentagon rigidity: 2-distance reduction + degree structure

**Mode**: REVISIT (continue, RICH). **Outcome**: progress — rigorous reduction of the open
lower bound `h 5 ≥ 3`, all axiom-free. **docker-built** `Proofs.Erdos98WIP01` OK
(0 sorry / 0 axiom / no `native_decide`; new proofs use only standard Mathlib).

The residual frontier is `h 5 ≥ 3` ⟺ *no general-position `PointConfig 5` is a 2-distance
set*. This session pins that reduction down to its exact combinatorial/geometric frame and
proves everything on the combinatorial side.

**Lean results added** (`proofs/Proofs/Erdos98WIP01.lean`):

- **`exists_two_distances_of_numDistinct_le_two`** (axiom-free, all `n`): an injective
  `PointConfig` on `n ≥ 2` points with `numDistinctDistances ≤ 2` *is* a 2-distance set —
  `∃ a b > 0` covering every pairwise distance. Mechanism: all off-diagonal distances are
  positive (injectivity) hence lie in the counted finset `D`; `D.card ≤ 2` ⇒ `D ⊆ {a,b}` via
  `Finset.card_erase_of_mem` + `Finset.card_le_one`. This is the entry point of the reduction.
- **`two_distance_near_degree_bounds`** (axiom-free): in a **general-position** 2-distance
  `PointConfig 5`, every vertex has between `1` and `3` short-distance (`a`) neighbours.
  Mechanism: `card_fiber_dist_le_three` caps both the `a`-circle and the `b`-circle around a
  vertex at `3` (no-four-concyclic); the two neighbour-sets are disjoint (`a ≠ b`) and cover
  all `4` other points, so `card A + card B = 4` with each `≤ 3` ⇒ `1 ≤ card A ≤ 3`.

**The exact residual (documented, not proved).** Combining the degree bounds with the merged
`no_four_equidistant_indices` (no monochromatic `K₄`): the short-distance graph of any
hypothetical general-position 2-distance 5-set is a graph on 5 vertices with min-degree `≥ 1`,
max-degree `≤ 3`, and no `K₄` in the graph *or its complement*. **These purely combinatorial
constraints do not close** — `C₅` (the regular-pentagon pattern) satisfies all of them
(2-regular, `K₄`-free, self-complementary `α = 2 ≤ 3`). The single remaining fact is
**geometric**: an equilateral, equidiagonal pentagon (`C₅` realization) is regular, hence its
5 vertices are concyclic, contradicting `NoFourConcyclic`. Pigeonhole from a single vertex
also caps at `⌈4/3⌉ = 2`, so a multi-vertex/rigidity argument is genuinely required.

**Reusable notes.** `numDistinctDistances P = D.card` where `D` is the filtered image finset;
extracting the two distances is cleanest via erase + `Finset.card_le_one` rather than a
`card_le_two` witness lemma (which Mathlib does not expose in subset form). `Disjoint A B`
from `a ≠ b` via `Finset.disjoint_left` and `hjA.2.symm.trans hjB.2`; disjoint-union card via
`Finset.card_union_of_disjoint`.

**Honest delta**: did **not** prove `h 5 ≥ 3` (still open). +2 axiom-free theorems (2-distance
reduction + per-vertex degree structure), residual reduced to a single named geometric fact
(pentagon rigidity). Axiom count unchanged (0). Bounds remain `2 ≤ h 5 ≤ 3`. Phase `ACT`.

**Files modified**: `proofs/Proofs/Erdos98WIP01.lean`,
`src/data/research/problems/erdos-98-wip-01.json`, this file.

**Next**: prove pentagon rigidity (the `C₅`-realization ⇒ concyclic case) to close `h 5 ≥ 3`;
or abstract the equilateral-dimension bound.


## Session 2026-07-21 (researcher-1) — toward h 5 ≥ 3: no 4 coplanar points are mutually equidistant

**Mode**: REVISIT (continue). **Outcome**: progress — a reusable geometric lemma toward
`h 5 ≥ 3`, plus concrete unconditional lower-bound thresholds.
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
build "succeeded, 8577 jobs"). All new lemmas use only Mathlib + `linarith`/`omega`/
`linear_combination`, so foundational axioms only (`propext`/`Classical.choice`/`Quot.sound`).

### Why `h 5 ≥ 3` is not one line (correcting the prior docstring)
The `h_five_bounds` docstring claimed "the regular pentagon, the only planar 2-distance
5-set". That is **false**: the plane has several 5-point 2-distance sets (the pentagon is
only the concyclic one). So `h 5 ≥ 3` genuinely needs the structure of 2-distance sets,
not just "pentagon ⇒ concyclic ⇒ excluded". The new toward-`h 5 ≥ 3` section documents the
real reduction.

### The reduction (rigorous, and what remains)
Suppose a general-position 5-set uses only two distances `a < b`. By
`card_fiber_dist_le_three` (already in file), each point has `a`-degree and `b`-degree in
`{1,2,3}` (a 4th point at a common distance would be 4 concyclic). Case split on whether
some vertex has `a`-degree 3:
- **Degree-3 vertex `p`** with neighbours `X,Y,Z` at distance `a`. Sub-case "`X,Y,Z`
  pairwise `a`" makes `p,X,Y,Z` **four mutually equidistant** → **now excluded** by the new
  `no_four_mutually_equidistant`. Remaining degree-3 sub-cases (some `XY` or `XZ` = `b`)
  reduce to intersecting-circle distance equations (`|YZ| = a√3`, etc.) — **still open**,
  coordinate-heavy.
- **All degrees 2** (a-graph 2-regular on 5 vertices ⇒ `C₅`) is the pentagon-type case;
  metric realizability forces the concyclic regular pentagon — **still open** (needs
  "equilateral + equidiagonal convex pentagon ⇒ concyclic").

### Lean results added (`proofs/Proofs/Erdos98WIP01.lean`)
- **`no_four_mutually_equidistant`** (axiom-free): in `EuclideanSpace ℝ (Fin 2)` no four
  points have all six pairwise distances equal to a common `r > 0`. Proof: edge vectors
  `u=b-a, v=c-a, w=d-a` have `‖·‖²=r²`, pairwise inner product `r²/2` (from `‖u-v‖=r` via
  `norm_sub_sq_real`); the Gram system forces `LinearIndependent ℝ ![u,v,w]`, contradicting
  `finrank (EuclideanSpace ℝ (Fin 2)) = 2` (`LinearIndependent.fintype_card_le_finrank` +
  `finrank_euclideanSpace_fin`). This is the planar "regular `k`-simplex needs dim `k`".
- **`no_four_equidistant_indices`**: config-level specialization (no 4 indices mutually
  equidistant).
- **`three_le_h_of_eight_le`** (`n ≥ 8 → 3 ≤ h n`) and **`four_le_h_of_eleven_le`**
  (`n ≥ 11 → 4 ≤ h n`): immediate from `three_mul_h_ge` (`n-1 ≤ 3·h n`) — the first exact
  thresholds where the elementary bound alone certifies 3, resp. 4, distinct distances.

### Next steps
- Degree-3 remaining sub-cases: formalize "two circles of radius `a` at centre-distance `a`
  meet at points `a√3` apart" as reusable `EuclideanSpace ℝ (Fin 2)` algebra.
- All-degree-2 (`C₅`) case: "equilateral + equidiagonal convex pentagon is concyclic".
- Both are coordinate-geometry heavy; each is a standalone multi-session sub-target.

## Session 2026-07-21 (researcher-1) — h 5 ≤ 3 via explicit 3-distance general-position 5-witness

**Mode**: FRESH (continue). **Outcome**: progress — `h 5 ≤ 3`, so `2 ≤ h 5 ≤ 3`.
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
`#print axioms Erdos98WIP01.h_five_le_three` = `[propext, Classical.choice, Quot.sound]` only).

Continued the pinned-values line past `h 4 = 2`. The lower-bound side of `h 5` is hard, so
this session establishes the **upper bound** with a fully machine-checked explicit witness.

**The witness `h5Config : PointConfig 5`.** Found by continuous optimization (minimize
within-cluster spread of the 10 pairwise distances subject to general-position penalties,
including a no-4-concyclic determinant penalty — omitting it first produced the degenerate
"centre + 4 on a circle"), then rationalized and **sympy-verified exactly**:

    A=(0,0), B=(1,0), C=(−√3⁄2,−½), D=(½,√3⁄2), E=(½,−(2+√3)⁄2)

- **Exactly three distinct distances** `1`, `√(2+√3)`, `1+√3` (squared: `1`, `2+√3`,
  `(1+√3)²=4+2√3`). Multiplicities `1`: AB,AC,AD,BD; `√(2+√3)`: AE,BC,BE,CD,CE; `1+√3`: DE.
- **No 3 collinear**: all 10 triangle areas ≠ 0. **No 4 concyclic**: the 5 circumscribed-
  circle determinants are `1+√3⁄2`, `2+√3`, `5⁄2+3√3⁄2` (all ≠ 0).

**Lean results added** (`proofs/Proofs/Erdos98WIP01.lean`, item 18):
`h5Config`, `h5Config_dist_sq`, `h5Config_dist_mem` (dist ∈ {1,√(2+√3),1+√3}),
`h5Config_injective`, `noThreeCollinear_h5Config`, `noFourConcyclic_h5Config` (dispatched
to five per-quadruple `h5_not_equidistant_*` helpers), `inGeneralPosition_h5Config`,
`numDistinctDistances_h5Config_le` (≤ 3), `h_five_le_three` (`h 5 ≤ 3`),
`h_five_ge_two` (`2 ≤ h 5`, from `h_four_ge_two` + `h_mono`), `h_five_bounds`.

**Why not `h 5 = 3`.** Both natural lower-bound routes give only `h 5 ≥ 2`
(`three_mul_h_ge 5` = `⌈4/3⌉ = 2`; `h_mono` from `h 4 = 2`). Pinning `h 5 = 3` needs
`h 5 ≥ 3`: no general-position 5-set has ≤ 2 distances. The regular pentagon (the only
planar 2-distance 5-set) is concyclic, so this reduces to the **classification of planar
2-distance sets** (max 5, the pentagon) or the **Larman–Rogers–Seidel** linear-algebra
bound (a 2-distance set in ℝ² has ≤ 6 points) refined by no-4-concyclic to ≤ 4. Left open.

**Reusable tactic notes.** `!₂[·]` coordinate accessors reduce under `norm_num`, not by
`simp only [Matrix.cons_val_*]` alone — the distance-value lemma needs
`rw [EuclideanSpace.dist_sq_eq]; … simp only […]; norm_num [hs2] <;> nlinarith [hs2]`
(bare `nlinarith` after `simp` fails on the value-1 √3 pairs). The no-4-concyclic proof
for 5 points is cheap when factored as one `not_equidistant` helper per unordered quadruple
(5 total `nlinarith` calls) with `noFourConcyclic` doing `fin_cases … <;> first | … | exact
h5_not_equidistant_XYZW center r (by assumption) …`.

**Files modified**: `proofs/Proofs/Erdos98WIP01.lean` (+~180 lines),
`src/data/research/problems/erdos-98-wip-01.json`, this file.

**Next**: prove `h 5 ≥ 3` (2-distance-set classification); abstract "1-distance set in ℝ^d
has ≤ d+1 points"; sharpen the general `(n−1)/3` lower bound.


## Session 2026-07-21 (researcher-1) — pinned value h 4 = 2 (first value of h exceeding 1)

**Mode**: FRESH (continue). **Outcome**: progress — `h 4 = 2` pinned exactly.
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
`#print axioms Erdos98WIP01.h_four` = `[propext, Classical.choice, Quot.sound]` only).

Executed the recorded next step (extend the pinned values beyond `h 3`). Both bounds are new.

**Upper bound `h 4 ≤ 2`** (`h_four_le_two`).
- The classical minimum-distance witness for 4 points, the **square**, is *disqualified*:
  its 4 vertices are concyclic, and general position forbids 4 concyclic points. So the
  square is not a witness for `h 4`.
- `centeredTriangleConfig : PointConfig 4` — the equilateral triangle
  `(1,0), (−½,√3⁄2), (−½,−√3⁄2)` together with its **centroid** `(0,0)`: a 2-distance set
  (circumradius `1`, side `√3`) that survives both nondegeneracy constraints.
- `centeredTriangleConfig_dist_mem` — every pairwise distance is `1` or `√3` (dist² is `1`
  or `3`; nonnegative sqrt). Key tactic fix: `!₂[…]` coordinate accessors are reduced by
  **`norm_num`**, not by `simp only [Matrix.cons_val_*]` (those args are flagged *unused*);
  mirror `equilateral_dist_off`'s `simp only [cfg, Fin.sum_univ_two, Real.dist_eq, sq_abs]`
  then `norm_num [hs2] <;> nlinarith [hs2]` (fallback for the `√3²=3` arithmetic).
- `noThreeCollinear`/`noFourConcyclic_centeredTriangleConfig` — the centroid is interior
  (no 3 collinear); the only point equidistant from the 3 vertices is the circumcenter =
  centroid, at distance `0 ≠ 1` from itself, so no 4 concyclic. Both needed
  `set_option maxHeartbeats 1000000 in` (64 / 256 `fin_cases` branches, √3 arithmetic).
  NB: `set_option … in` goes **before** the docstring, not between docstring and theorem.
- `numDistinctDistances_centeredTriangleConfig_le` — positive distances ⊆ `{1,√3}`, card ≤ 2.

**Lower bound `h 4 ≥ 2`** (`h_four_ge_two`), the harder half — pins the exact value.
- `not_four_equidistant` — four pairwise-equidistant points are impossible in `ℝ²`. Take
  difference vectors `vₖ = p_{k+1} − p₀` (`k : Fin 3`). Equidistance gives the Gram matrix
  `⟪vᵢ,vᵢ⟫ = r²`, `⟪vᵢ,vⱼ⟫ = r²/2` (`i≠j`) via `real_inner_self_eq_norm_sq` and
  `norm_sub_sq_real`. `Fintype.linearIndependent_iff` + `sum_inner` + `real_inner_smul_left`
  turn `∑ gₖ•vₖ = 0` into the 3×3 system `r²·½(I+J)·g = 0`; cancel `r² ≠ 0`
  (`linear_combination` + `mul_eq_zero`) to get `g = 0`. Then
  `LinearIndependent.fintype_card_le_finrank` vs `finrank_euclideanSpace_fin` gives `3 ≤ 2`,
  contradiction. **First use of the ambient dimension** (all earlier bounds are metric/comb.)
- `two_le_numDistinctDistances_four` — a 1-distance 4-config would force all six distances
  equal (`Finset.card_eq_one` on the positive-distance set), i.e. four equidistant points.
- `h_four : h 4 = 2 := le_antisymm h_four_le_two h_four_ge_two`.

**Reusable idiom** (recorded for `h 5`+): a 1-distance set in `ℝ^d` has `≤ d+1` points via
the Gram/linear-independence route above. The whole lower-bound block compiled first try.

**Next**: pin `h 5` (regular pentagon is concyclic → disqualified; need a non-concyclic
5-point 2/3-distance set, or show `h 5 ≥ 3`); abstract the equidistant⟹independent lemma.

## Session 2026-07-21 (researcher-1) — pinned value h 3 = 1 via explicit equilateral triangle

**Mode**: FRESH (continue). **Outcome**: progress — 6 axiom-free declarations,
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
`#print axioms h_three` = `[propext, Classical.choice, Quot.sound]` only).

Executed the recorded next step: pin `h 3` exactly.

- `equilateralConfig : PointConfig 3` — the unit equilateral triangle
  `(0,0), (1,0), (½, √3⁄2)`.
- `equilateralConfig_injective` — the three abscissae `0, 1, ½` already differ, so the
  `x`-coordinate alone separates every pair (`norm_num [equilateralConfig]` on the 0-th
  coordinate).
- `noThreeCollinear_equilateralConfig` — a line through all three forces `c = 0`, then
  `a = 0`, then `b·(√3⁄2) = 0`; `√3 > 0` gives `b = 0`. The `√3` coefficient makes this
  genuinely **nonlinear** (unlike the right-triangle case), needing `nlinarith [hs, …]`
  with `hs : 0 < √3` (the negated-goal × `hs` product certificate).
- `noFourConcyclic_equilateralConfig` — vacuous (`noFourConcyclic_of_le_three`).
- `inGeneralPosition_equilateralConfig` — the triangle is in general position.
- `equilateral_dist_off {i j} (hij : i ≠ j) : dist (equ i) (equ j) = 1` — every side has
  length 1: `∑ (Δcoord)² = 1` via `(√3)² = 3`, then `EuclideanSpace.dist_eq` + `Real.sqrt_one`.
- `numDistinctDistances_equilateralConfig = 1` — **first exact computation** of
  `numDistinctDistances` for an explicit config: positive distances = `{1}` (diagonal
  pairs give 0, filtered out).
- `h_three : h 3 = 1` — equilateral witness ⟹ `h 3 ≤ 1`; `h_mono` + `h_two` ⟹
  `1 = h 2 ≤ h 3`. Squeeze ⟹ `h 2 = h 3 = 1`.

**Key Lean lesson.** `EuclideanSpace.dist_sq_eq` rewrites `dist x y ^ 2` into a sum over
`x.ofLp i` coordinate accesses that `Matrix.cons_val_*` do NOT reduce (they stay
`(![…] ⟨0,⋯⟩).ofLp 0`). Use `EuclideanSpace.dist_eq` instead — its `x i` is direct
function application, reduced by `simp only [equilateralConfig] ; norm_num`. Leftover
`1/4 + (√3/2)² = 1` closes with `nlinarith [hs]` (`hs : √3² = 3`); `norm_num` alone does
NOT expand `(√3/2)²` against `hs`.

**Honesty.** Parent Erdős #98 (`h(n)/n → ∞`) remains **OPEN**; only the conjectured rate
is the open piece. The elementary envelope gives only `1 ≤ h 3 ≤ 3` — the exact value
needs the equilateral witness. PR: extends #40147.

### Next Steps
- Improve the lower-bound constant beyond `/3` toward `(n−1)/2` or `≥ n`.
- Pin `h 4`: is it `1` (needs an impossible single-distance 4-config?) or `2`?
- Attack the conjectured rate `h n / n → ∞`.

## Session 2026-07-20 (researcher-1) — MONOTONICITY of h + pinned value h 2 = 1

**Mode**: FRESH (continue) — build on the linear lower bound. **Outcome**: progress
— 5 axiom-free declarations, **docker-built** `Proofs.Erdos98WIP01` OK (8577 jobs,
0 sorry / 0 axiom / no native_decide).

Proved the first **structural comparison across cardinalities** and the first
exactly-pinned value of `h`:

- `card_triple_image` / `card_quad_image` — injective-image cardinality helpers
  (`card {e i,e j,e k} = card {i,j,k}`) via `Finset.card_image_of_injective`.
- `inGeneralPosition_comp` — a sub-configuration `P ∘ e` chosen by an **injective**
  index map `e : Fin m → Fin n` inherits general position: injectivity composes, and
  any collinear/concyclic degeneracy of `P ∘ e` transports through `e` (which preserves
  the `card = 3` / `card = 4` distinctness) to a degeneracy of `P`, contradicting `hP`.
- `numDistinctDistances_comp_le` — `numDistinctDistances (P ∘ e) ≤ numDistinctDistances P`
  (every positive sub-config distance is realized by the image pair `(e p.1, e p.2)`).
- `h_mono : Monotone h` — delete the last point (`Fin.castSucc`) of the `h_attained`
  minimizer of `h (n+1)`; the restriction is general position with `≤` distinct distances,
  so `h n ≤ numDistinctDistances ≤ h (n+1)`. Via `monotone_nat_of_le_succ`.
- `h_two : h 2 = 1` — squeeze `1 ≤ 3·h 2` (`three_mul_h_ge 2`) against
  `h 2 ≤ (2 choose 2) = 1` (`h_le_choose_two 2`); `omega` closes. First exact value,
  no explicit distance computation.

**Why this is progress**: monotonicity is a genuine structural fact none of the
pointwise bounds provides; `h_two` demonstrates the lower/upper envelope is tight at
`n = 2`. At `n = 3` the same squeeze gives only `1 ≤ h 3 ≤ 3` (pinning `h 3 = 1` needs
an explicit equilateral-triangle witness — next step).

### Next
- Pin `h 3 = 1` via an explicit equilateral triangle (numDistinctDistances = 1); with
  `h_mono` this gives `h 2 = h 3 = 1`.
- Improve the lower-bound constant beyond `/3` (combine no-3-collinear + no-4-concyclic,
  or count from two base points) toward `h n ≥ (n-1)/2` / the conjectured `≥ n`.
- The conjectured RATE `h n / n → ∞` (Erdős #98 itself) is the sole remaining open piece;
  divergence `h n → ∞` is already elementary (`tendsto_h_atTop`).

## Session 2026-07-21 (researcher-1) — ELEMENTARY LINEAR LOWER BOUND n−1 ≤ 3·h n + unconditional h(n)→∞

**Mode**: FRESH build on the now-closed existence tower. **Outcome**: progress — first
lower bound on `h n` that **grows with n**, and an **unconditional** proof of `h(n)→∞`.
Docker-built `Proofs.Erdos98WIP01` (Build succeeded, 8577 jobs); 0 sorry / 0 axiom / no
native_decide.

**The idea (elementary, uses no-4-concyclic).** Fix a base point `P b`. Any circle centred
at `P b` meets the other `n−1` points in **at most three** of them — a fourth would be four
points equidistant from `P b`, i.e. four concyclic points (centre `P b`), which
`NoFourConcyclic` forbids. So the `n−1` distances `dist (P b) (P i)` (`i ≠ b`) take at least
`(n−1)/3` distinct values, each a genuine distinct distance. Hence
`n−1 ≤ 3·numDistinctDistances P` for **every** general-position `P`, so `n−1 ≤ 3·h n`.

**Added declarations** (all in `Erdos98WIP01.lean`, results #10–12 in the header):
- `card_fiber_dist_le_three (hgp)(b)(v)` — the fibre of `i ↦ dist (P b)(P i)` over `v`,
  restricted to `i ≠ b`, has `card ≤ 3`. Crux.
- `numDistinctDistances_lower (hgp)(0<n) : n−1 ≤ 3·numDistinctDistances P` — the per-config
  pigeonhole bound.
- `three_mul_h_ge (n) : n−1 ≤ 3·h n` — same bound for the extremal quantity, via `h_attained`.
- `tendsto_h_atTop : Tendsto h atTop atTop` — **h(n)→∞ UNCONDITIONALLY**, no imported theorem.
- helper `card_quad_of_pairwise_ne` (converse of `card_quad_pairwise_ne`, via `Finset.card_eq_four`).

**Why this matters.** `tendsto_h_atTop` strictly sharpens the earlier `guthKatz_imp_tendsto`
(which assumed the imported Guth–Katz `Ω(n/log n)` baseline) and `weak_imp_tendsto` (which
assumed the *open* weak conjecture): the divergence of `h` is now an **elementary theorem**.
Only the conjectured *rate* `h(n)/n→∞` (Erdős #98) stays open — and even the linear order here
is `/3` of the conjectured `n`, so this is honestly a weak-but-real lower bound, not the target.

**Reusable Lean recipe (pigeonhole distinct-distance lower bound):**
- `Finset.card_le_mul_card_image (f := …) s k hfib : s.card ≤ k · (s.image f).card` — supply
  `hfib : ∀ v ∈ s.image f, (s.filter (f · = v)).card ≤ k`. Here `s = univ.erase b`, `k = 3`.
- Extract the `k+1` colliding elements from `¬(card ≤ k)` via `Finset.three_lt_card.mp
  (not_le.mp hlt)` (gives `∃ a∈s ∃ b∈s ∃ c∈s ∃ d∈s, pairwise ≠`); rebuild the 4-set cardinality
  with `Finset.card_eq_four.mpr`.
- `s.card = n−1` via `Finset.card_erase_of_mem (mem_univ _)` + `card_univ`/`Fintype.card_fin`.
- Positivity/subset: distances from `P b` land in the `numDistinctDistances` filtered image
  (each `>0` by injectivity `hib` since `i ≠ b`); `card_le_card` on the subset.
- Descent to `h`: `three_mul_h_ge` applies `numDistinctDistances_lower` to the `h_attained`
  minimiser; the `n = 0` case is `simp`. `tendsto_h_atTop` = `Filter.tendsto_atTop.mpr` +
  `filter_upwards [eventually_ge_atTop (3M+1)]` + `omega` on `n−1 ≤ 3·h n`.

### Next (genuinely remaining — the parent is OPEN)
- Monotonicity `h n ≤ h (n+1)`: a subconfiguration of a general-position config is general
  position (Injective / NoThreeCollinear / NoFourConcyclic all inherit under restriction
  `Fin n ↪ Fin (n+1)`); pair with the extremal witness.
- Sharpen the `/3` constant, or a per-basepoint-pair refinement.
- Parent Erdős #98 `h(n)/n→∞` (and even weak `h(n)≥n`) remains OPEN; not reachable by the /3
  bound.

## Session 2026-07-21 (researcher-1) — general-position existence for ALL n (parabola, positive abscissae)

**Mode**: FRESH build on the n≤4 tower. **Outcome**: progress — **resolved the "deep
constructive piece"** that every prior session flagged as open. Docker-built
`Proofs.Erdos98WIP01` (Build succeeded, 8577 jobs); 0 sorry / 0 axiom / no native_decide.

**The key realization that unblocked it.** Prior sessions dismissed the parabola construction
`(t, t²)` because "any 4 parabola points with abscissae summing to 0 are concyclic". True, but
the fix is trivial: **make all abscissae positive**. Four parabola points are concyclic *iff*
their abscissae sum to `0` (Vieta: the 4 abscissae are the roots of the monic quartic
`x⁴ + (1−2c₁)x² − 2c₀x + s` cut by a circle, whose `x³`-coeff is `0`). Positive abscissae ⟹
every 4-subset sum `≥ 4 > 0` ⟹ no four concyclic. And on `y = x²` **no three points are ever
collinear** (strict convexity). So the config `parabolaConfig n : i ↦ (i+1, (i+1)²)` — abscissae
`1,…,n` — is in general position for **every** `n`. The genericity/perturbation argument the
earlier notes proposed is NOT needed; this is fully elementary.

**Added declarations** (all in `Erdos98WIP01.lean`):
- `parabolaConfig n` (def) + `parabolaConfig_zero/one` (coordinate simp lemmas via `simp [parabolaConfig]`).
- `parabolaConfig_injective`, `noThreeCollinear_parabolaConfig`, `noFourConcyclic_parabolaConfig`.
- `exists_inGeneralPosition (n) : ∃ P, InGeneralPosition P` — **for all n** (supersedes `_of_le_four`).
- `h_attained (n) : ∃ P, InGeneralPosition P ∧ numDistinctDistances P = h n` — via `Nat.sInf_mem`,
  so `h n` is a genuine attained minimum for EVERY n, never the `sInf ∅ = 0` junk value. This
  removes the honesty caveat on `h_le_choose_two` (its nonempty branch is now unconditional).

**Reusable Lean recipe (elementary algebraic general-position, no measure theory):**
- Distinctness helpers `card_triple_pairwise_ne` / `card_quad_pairwise_ne`: from `card = k` derive
  pairwise `≠` via `Finset.insert_eq_self.mpr` (collapse a duplicate) + `Finset.card_insert_of_notMem`
  (NB: `notMem`, not `not_mem` — renamed in v4.31) + `card_insert_le`, closed by `omega`.
- No-3-collinear as abstract real lemma `parabola_collinear_trivial`: from `a·xₜ+b·xₜ²+c=0` at 3
  distinct abscissae, cancel `(xᵢ-xⱼ)` via `mul_eq_zero` + `sub_eq_zero.mp` to get `a+b(xᵢ+xⱼ)=0`,
  hence `b=0,a=0,c=0`. Each cancellation step is `linear_combination hi - hj` producing the factored
  product, then `rcases mul_eq_zero`.
- No-4-concyclic as abstract real lemma `parabola_concyclic_sum_zero`: THREE rounds of
  difference-and-cancel (`M(t,u)` linear-in-centre → `N(u,v)` symmetric-quadratic → abscissa sum),
  each round `linear_combination (prev diff)` + `mul_eq_zero`/`sub_eq_zero`. Gives `w+x+y+z=0`;
  `positivity` on the (all-≥1) sum + `linarith` closes.
- Bridge metric→squared: `dist center (P t) = r` ⟹ `(c₀-xₜ)²+(c₁-xₜ²)² = r²` via
  `simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, <coord lemmas>, Real.dist_eq, sq_abs]`
  then `linear_combination`.

### Next (genuinely remaining — the parent is OPEN)
- The constructive existence question is now CLOSED. What remains is purely the parent Erdős #98
  quantitative content: `h(n)/n → ∞` (strong) and even `h(n) ≥ n` (weak) — both OPEN in mathematics,
  not attackable by construction. A tractable formal increment would be a concrete lower bound like
  `2 ≤ h n` for `n ≥ 3` (distinct-distance counting on a general-position witness), or monotonicity
  `h n ≤ h (n+1)` (subconfiguration of general position is general position). No further "existence"
  work is needed.

## Session 2026-07-20 (researcher-1) — n=4 general-position existence (first non-vacuous concyclic case)

**Mode**: build on the n=3 triangle. **Outcome**: progress — 6 axiom-free declarations
(1 def + 5 theorems), host-verified v4.31 (`lake env lean` exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`; no sorry/native_decide).

Discharged general-position existence for `n = 4` — the first case where **no-four-concyclic**
is a genuine constraint. Config `(0,0),(1,0),(0,1),(1,-1)`:
- `fourConfig` (uses `!₂[·,·]` Euclidean notation; the 4th vertex isn't an axis point so not a
  `single`), `fourConfig_injective`, `noThreeCollinear_fourConfig` (4 triples, triangle recipe).
- `fourConfig_not_equidistant` (crux): no centre equidistant from all four. The three squared
  equalities `‖c-P₀‖²=‖c-Pᵢ‖²` reduce (via `EuclideanSpace.dist_sq_eq`) to linear constraints
  forcing `c₀=½, c₁=½, c₀-c₁=1` — contradiction by `nlinarith`.
- `noFourConcyclic_fourConfig`, `exists_inGeneralPosition_four`, `exists_inGeneralPosition_of_le_four`.

**Reusable Lean recipe (metric general-position in EuclideanSpace ℝ (Fin 2)):**
- `EuclideanSpace.dist_sq_eq : dist x y ^2 = ∑ i, dist (x i)(y i)^2` — AVOIDS manual sqrt.
  Then `Fin.sum_univ_two`, `Real.dist_eq`, `sq_abs` → `(x0-y0)^2+(x1-y1)^2`. The `c₀²,c₁²`
  terms cancel across the equidistance equalities, so `nlinarith` finishes.
- `!₂[a,b]` = Euclidean vector; coordinate access `!₂[a,b] i` reduces via `Matrix.cons_val_*`
  (`cons_val_three` EXISTS; no `cons_val_four`). `PiLp.toLp_apply` is the raw coord lemma but
  usually unneeded (simp reduces through it).
- Concyclic quantifies `∀ a b c d, card=4 → ...`: prove an order-independent helper
  `..._not_equidistant center r h0 h1 h2 h3`, then `fin_cases a<;>b<;>c<;>d`, kill card≠4 by
  `decide`, close each of the 24 perms with `exact helper center r (by assumption) ×4` (the
  `by assumption` picks the hyp matching each expected `dist center (P i)=r` type — uniform!).

### Next
- **n=5** or **general n**: failure locus `(3-collinear ∪ 4-concyclic)` is a finite union of
  proper algebraic subvarieties of `(ℝ²)ⁿ`; complement nonempty by a dimension/genericity
  argument (the deep constructive piece). Parent Erdős #98 (`h(n)/n → ∞`) remains OPEN.

## Session 2026-07-20 (researcher-1) — general-position existence for n ≤ 2 + vacuity lemmas

Added to `Erdos98WIP01.lean` (host-verified, parent `Erdos98Problem` is
Mathlib-only; all three depend only on `[propext, Classical.choice, Quot.sound]`,
0 sorry / 0 axiom):

- `noThreeCollinear_of_le_two (P) (n ≤ 2) : NoThreeCollinear P` — vacuous:
  `card {i,j,k} = 3` is impossible among `n ≤ 2` points
  (`Finset.card_le_card (subset_univ ..)` + `card_univ`/`Fintype.card_fin`, `omega`).
- `noFourConcyclic_of_le_three (P) (n ≤ 3) : NoFourConcyclic P` — vacuous:
  `card {a,b,c,d} = 4` impossible among `n ≤ 3` points.
- `exists_inGeneralPosition_of_le_two (n ≤ 2) : ∃ P, InGeneralPosition P` — the
  injective embedding `i ↦ EuclideanSpace.single 0 (i:ℝ)` (distinct first
  coordinates) is general-position since both nondegeneracy conditions are
  vacuous. **Consequence:** the defining set of `h n` is nonempty for `n ≤ 2`, so
  `h n` is an *attained* minimum there, not the `sInf ∅ = 0` junk value that the
  empty branch of `h_le_choose_two` falls back to.

### Key obstruction (negative knowledge)
The natural **parabola** construction `(t, t²)` does NOT give general position:
- No 3 collinear ✓ (a line meets `y = x²` in ≤ 2 points).
- No 4 concyclic ✗ — a circle meets `y = x²` in the quartic
  `x⁴ + (1−2q)x² − 2px + (p²+q²−r²) = 0`, whose **cubic coefficient is 0**, so the
  4 roots sum to `0`. Hence any 4 parabola points with `x`-coordinates summing to
  `0` (e.g. `x = −3,−1,1,3`) ARE concyclic. Full GP existence needs a
  genericity/perturbation argument (config space minus finitely many proper
  algebraic subvarieties), not a single explicit algebraic curve.

### v4.31 gotcha
`EuclideanSpace.single_apply` is deprecated → use `PiLp.single_apply`. Extract a
coordinate from an equality of `EuclideanSpace` points via
`congrArg (fun f => f 0) hij` then `simpa [PiLp.single_apply]`.

### Next
- `n = 3` (first non-vacuous no-3-collinear case): explicit triangle
  `(0,0),(1,0),(0,1)`, needing the 6-permutation collinearity computation.
- Full GP existence for all `n` via genericity (deep constructive piece).

## Session 2026-07-20 (researcher-1) — h(n)→∞ is UNCONDITIONAL (Guth–Katz baseline)

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound):

- `tendsto_const_mul_div_log_atTop` — `c·n/log n → ∞` for `c>0`. Path: `Real.isLittleO_log_id_atTop`
  ∘ `tendsto_natCast_atTop_atTop` ⟹ `log n =o n` ⟹ `log n / n → 0` (`IsLittleO.tendsto_div_nhds_zero`);
  eventually positive (`Real.log_pos`, n≥2) ⟹ `→ 𝓝[>]0` ⟹ reciprocal `→ atTop`
  (`Filter.Tendsto.inv_tendsto_nhdsGT_zero`); `inv_div` + `const_mul_atTop`.
- `guthKatz_imp_tendsto` — `GuthKatzBaseline ⟹ Tendsto h atTop atTop`. The imported (proven)
  Ω(n/log n) lower bound `c·n/log n ≤ h(n)` + the divergence above ⟹ `(h n:ℝ)→∞`
  (`tendsto_atTop_mono'`), then descend to ℕ (`Filter.tendsto_atTop.mpr` + `exact_mod_cast`).

KEY POINT: this sharpens the existing `weak_imp_tendsto`, which derived the SAME divergence
`h(n)→∞` from the OPEN weak conjecture. In fact the divergence is a THEOREM (unconditional,
from Guth–Katz). What genuinely remains open is only the RATE — `h(n)/n→∞` (strong) and
`h(n)≥n` (weak).

### Remaining open
- `h n ≤ n.choose 2` needs a general-position existence witness for all n (constructive, missing).
- Parent Erdős #98 (`h(n)/n→∞`) remains OPEN in mathematics.

## Session 2026-07-21 (researcher-1) — unconditional upper bound h(n) ≤ n.choose 2

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (theoremCount 10→12, host-verified
v4.31 via fresh parent olean + `lake env lean`, exit 0; `#print axioms` =
propext/Classical.choice/Quot.sound on both):

- `h_le_choose_two (n) : h n ≤ n.choose 2` — **resolves the open item** flagged last
  session ("`h n ≤ n.choose 2` needs a general-position existence witness"). The witness
  is *not* needed: split on whether the defining set
  `{numDistinctDistances P | InGeneralPosition P}` is empty. Nonempty ⟹
  `h n ≤ numDistinctDistances P ≤ n.choose 2` (`h_le_of_inGeneralPosition` +
  `numDistinctDistances_le_choose_two`). Empty ⟹ `h n = sInf ∅ = 0 ≤ n.choose 2`
  (`Nat.sInf_empty`). Combined with the unconditional divergence `guthKatz_imp_tendsto`,
  the minimum is now sandwiched: `h n → ∞` yet `h n ≤ n.choose 2` for every n.
- `h_eq_zero_of_le_one (n≤1) : h n = 0` — concrete degenerate values, since
  `n.choose 2 = 0` there (`Nat.choose_eq_zero_of_lt`) caps `h n` at 0.

### Note on honesty
`h_le_choose_two` is vacuous in the (believed-impossible for ℝ²) empty regime; its real
content is the nonempty branch. Proving general-position configs exist for all n
(`Injective ∧ NoThreeCollinear ∧ NoFourConcyclic`) remains the missing constructive piece
and the genuine next target — it would make `h n` a true minimum over a nonempty set.

### Remaining open (UNCHANGED)
Existence of general-position configurations for all n (constructive); parent Erdős #98
(`h(n)/n → ∞`, and even the weak `h(n) ≥ n`) remains OPEN in mathematics.

## Session 2026-07-20 (researcher-1) — n=3 general-position existence (explicit triangle)

**Mode**: build on the n≤2 vacuity result. **Outcome**: progress — 5 axiom-free
declarations (1 def + 4 theorems), **host-verified v4.31** (`lake env lean` exit 0;
`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no sorry/native_decide).

Discharged general-position existence for `n = 3` — the first case where no-three-collinear
is a genuine (non-vacuous) constraint:

- `triangleConfig` — the right triangle `(0,0), (1,0), (0,1)`, each vertex built with
  `EuclideanSpace.single` for uniform `single_apply` coordinate access.
- `triangleConfig_injective`, `noThreeCollinear_triangleConfig` (the crux),
  `noFourConcyclic_triangleConfig` (vacuous via `noFourConcyclic_of_le_three`).
- `exists_inGeneralPosition_three` and `exists_inGeneralPosition_of_le_three`: GP configs
  exist for all `n ≤ 3`, so `h n` is a genuine attained minimum (not `sInf ∅`) through `n=3`
  (previously only `n ≤ 2`).

**Proof technique** (no-3-collinear): a line `a·x+b·y+c=0` through all three vertices
forces `c=0` (origin), `a=0` ((1,0)), `b=0` ((0,1)). Formalized by `fin_cases` over the 27
index triples `(i,j,k)`: the degenerate (repeated-index) triples are killed by
`exact absurd hcard (by decide)` on `card{i,j,k}=3`; the 6 genuine permutations reduce via
`simp only [Matrix.cons_val_zero/one/two, head_cons, tail_cons, EuclideanSpace.single_apply]`
then `norm_num` (decides the `ite` conditions + arithmetic), closed by `linarith` on the
three linear facts. Injectivity: `fin_cases` + full `simp` closes the false coordinate
equalities.

### Next
- **n=4** (first non-vacuous no-4-concyclic case): analog of this step for concyclicity —
  needs the four-points-on-a-circle determinant computation over `EuclideanSpace`.
- **All n**: failure locus `(3-collinear ∪ 4-concyclic)` is a finite union of proper
  algebraic subvarieties of `(ℝ²)ⁿ`; complement nonempty by a dimension/genericity argument
  (the deep constructive piece). Parent Erdős #98 (`h(n)/n → ∞`) remains OPEN.
