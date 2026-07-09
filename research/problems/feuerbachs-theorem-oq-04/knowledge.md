# feuerbachs-theorem-oq-04 — Feuerbach's Theorem in Non-Euclidean Geometry

## Session 2026-07-07 (researcher-2): spherical side-midpoints + nine-point circle existence [VERIFIED — 0 sorry, 0 axiom]

**Mode**: ACT (CONTINUE). Frontier item #1 across every prior session was "side-midpoints
(`sMidpoint`), in-flight on `research/feuerbach-oq04-midpoint` (DRAFT PR #32127)" — but that
branch **never merged** and `grep -r sMidpoint proofs/` returns nothing on `main`. Meanwhile
researcher-4 landed the circumcircle primitive `sphericalCircumcircle_exists`
(`FeuerbachsTheoremOQ04Circumcircle.lean`, merged). The one missing ingredient for the
spherical nine-point circle (= circumcircle of the medial triangle) was therefore a genuine
**midpoint** of a spherical side. This session supplies it in a fresh collision-free companion
file and derives nine-point-circle existence.

**Outcome**: COMPLETED (**machine-verified**, 0 sorry / 0 axiom) — new file
`proofs/Proofs/FeuerbachsTheoremOQ04Midpoint.lean` (7 declarations, ~110 L).
`docker-build.sh Proofs.FeuerbachsTheoremOQ04Midpoint` now returns **`=== Build succeeded ===`**.
The prior UNVERIFIED status (2026-07-07 first pass) was a transient shared-Mathlib-volume
corruption on the build host, not a proof error: this session's retries progressively
self-healed the cache — first two corrupt `.ltar` files auto-purged, then a corrupt `.ir`
(`Groupoid.ir`, "invalid header") cleared, and the full 7745-target build then went green
with my file reached and elaborated. Committed on branch
`research/feuerbach-oq04-midpoint-v2`; PR #35206 promoted from DRAFT to ready.

### What was written (`proofs/Proofs/FeuerbachsTheoremOQ04Midpoint.lean`)
- **`sMidpoint A B := ‖A + B‖⁻¹ • (A + B)`** — the spherical midpoint (normalised sum).
- **`sMidpoint_comm`** — symmetry `sMidpoint A B = sMidpoint B A`.
- **`onSphere_sMidpoint`** — for non-antipodal `A,B` (`A + B ≠ 0`) the midpoint is a model
  point (`norm_smul`/`norm_inv`/`norm_norm` + `inv_mul_cancel₀`). The `A+B≠0` hypothesis is
  genuine spherical nondegeneracy: antipodal points have no unique midpoint.
- **`inner_sMidpoint_sub`** — `⟪M, A − B⟫ = 0`: `M` lies on the perpendicular-bisector great
  circle of `AB` (the pole is `A − B`), dual to researcher-4's `inner_sub_eq_zero_iff_scos_eq`.
  Algebra: `⟪A+B, A−B⟫ = ‖A‖² − ‖B‖² = 0`.
- **`scos_sMidpoint_eq` / `sdist_sMidpoint_eq`** — the midpoint is spherically equidistant from
  both endpoints (`scos A M = ‖A+B‖⁻¹(1 + ⟪A,B⟫) = scos B M`, then `sdist = arccos ∘ scos`).
- **`sphericalNinePointCircle_exists`** (headline) — the three side-midpoints
  `sMidpoint B C`, `sMidpoint A C`, `sMidpoint A B` of a non-degenerate spherical triangle
  lie on a common spherical circle, by feeding the medial triangle to the merged
  `sphericalCircumcircle_exists`. This is the spherical nine-point circle's existence.

### Verification note
All proofs are elementary real-inner-product algebra (`real_inner_smul_{left,right}`,
`inner_add_{left,right}`, `real_inner_self_eq_norm_sq`, `real_inner_comm`, `ring`) plus one
direct application of the merged `sphericalCircumcircle_exists`. Machine-verified:
`docker-build.sh Proofs.FeuerbachsTheoremOQ04Midpoint` → `=== Build succeeded ===`, 0 sorry,
0 axiom, 0 `native_decide`. Build-host note for future sessions: transient corrupt-cache
failures (`.ltar`/`.ir` "invalid header", or OOM during `cache get` under fleet contention)
are cleared by plain retries — each run auto-purges the offending file and re-fetches it; do
not touch the code and do not nuke the shared volumes while other `lean-build-*` containers run.

### Frontier UPDATED
1. ~~Side-midpoints (`sMidpoint`)~~ — **DONE this session, machine-verified**.
2. **The Feuerbach tangency** (spherical nine-point circle internally tangent to the incircle,
   externally to the three excircles). Still genuinely hard; not attempted. This is now the
   sole remaining frontier item — the full tritangent family, circumcircle, and medial-triangle
   nine-point circle existence are all in place and machine-verified.

## Session 2026-07-02 (researcher-4): the spherical circumcircle — existence primitive for the nine-point circle [VERIFIED]

**Mode**: ACT (CONTINUE). The four tritangent circles (incircle + 3 excircles) and their
full pairwise-distinctness matrix are on `main`; the tangent-point and common-perpendicular
machinery merged; side-midpoints (`sMidpoint`) are in-flight on
`research/feuerbach-oq04-midpoint`. The nine-point circle of a spherical triangle is the
**circumcircle of its medial triangle**, so the missing existence primitive was: *any three
model points lie on a common spherical circle*. This session supplies exactly that, in a
collision-free companion file. **Outcome**: PROGRESS — new file
`FeuerbachsTheoremOQ04Circumcircle.lean` (3 theorems, ~90 L). **Docker build VERIFIED**
(`docker-build.sh Proofs.FeuerbachsTheoremOQ04Circumcircle`, `✔ [7744/7744] Built`, exit 0);
**0-sorry, 0-axiom**, no native_decide (only `rw`, `unfold`, `real_inner_comm`, `cos_sdist`,
`greatCircles_inter`).

### What was delivered (`proofs/Proofs/FeuerbachsTheoremOQ04Circumcircle.lean`)
- **`inner_sub_eq_zero_iff_scos_eq`** (perpendicular-bisector characterisation): `⟪O, A−B⟫ = 0
  ↔ scos A O = scos B O`. The model points equidistant from `A` and `B` form the great circle
  with pole `A − B` — the spherical perpendicular bisector of `AB`. Dual to the *side-pole*
  bisector `equidistant_two_sides_iff` already on main (vertices here, not sides).
- **`sphericalCircumcircle_exists`** (headline): for any three model points `A,B,C` on a
  sphere of dim `> 2`, `∃ O ρ, OnSphere O ∧ A,B,C ∈ sCircle O ρ`. Construction mirrors
  `sphericalIncircle_exists`: intersect the two perpendicular-bisector great circles (poles
  `A−B`, `B−C`) via `greatCircles_inter` → `scos A O = scos B O = scos C O`; take `ρ = sdist
  A O` and use `cos_sdist` to match `cos ρ`.
- **`sphericalCircumcircle_equidistant`**: the circumcentre is spherically equidistant,
  `sdist A O = sdist B O = sdist C O` — immediate from equal `scos` since `sdist · O = arccos
  (scos · O)`.

### Why this matters
This is the dual of the incenter existence lemma (side-poles → vertices) and the direct
existence primitive under the spherical nine-point circle: applying it to the three
side-midpoints (`sMidpoint`, in-flight) yields the nine-point *circle* as their circumcircle.
It is unconditional (no non-degeneracy hypothesis): even collinear points get a common
`sCircle` (possibly a great circle). Collision-free — new file, auto-discovered by lake globs
(no `Proofs.lean` edit), builds only on merged main API.

### Frontier UNCHANGED (genuinely hard)
1. **Side-midpoints** (`sMidpoint`) — in-flight `research/feuerbach-oq04-midpoint`; combine
   with `sphericalCircumcircle_exists` to *define* the spherical nine-point circle.
2. **The Feuerbach tangency** (nine-point circle tangent to all four tritangent circles).
   Genuinely hard; not attempted.


## Session 2026-07-01 (researcher-7): completed the pairwise-distinctness matrix [VERIFIED]

**Mode**: ACT (CONTINUE). The prior session (researcher-1) proved only `incircle_excircleAB_distinct`
— 1 of the 6 pairs of the four tritangent circles (incircle + 3 excircles). Feuerbach's "tangent to
all four" presupposes ALL four are pairwise distinct (6 pairs). **Outcome**: PROGRESS — completed the
matrix: +5 theorems (~75 L) to `FeuerbachsTheoremOQ04.lean`. **Docker build VERIFIED**
(`docker-build.sh Proofs.FeuerbachsTheoremOQ04`, `✔ [7743/7743] Built`, exit 0); **0-sorry, 0-axiom**,
no native_decide (only `linarith`, existing signs-exclusivity engines, `Real.sin_pos_of_pos_of_lt_pi`,
`lt_irrefl`).

### Sign patterns (sᵢ = ⟪O,Nᵢ⟫, |sₐ|=|s_b|=|s_c|=sin ρ), from the existence theorems
- incircle: sₐ=s_b, s_b=s_c (EEE on a-b/b-c/a-c) ; excircle A: sₐ=-s_b, s_b=s_c (OEO) ;
  excircle B: sₐ=-s_b, sₐ=s_c (OOE) ; excircle C: sₐ=s_b, s_b=-s_c (EOO). Every pair differs.

### What was delivered (appended after `incircle_excircleAB_distinct`)
- **`incircle_excircle_ac_signs_exclusive`** (new engine): a-c analogue of the existing a-b/b-c
  sign-exclusivity lemmas — `⟪O,Na⟫=⟪O,Nc⟫` ∧ `⟪O,Na⟫=-⟪O,Nc⟫` ⟹ sin ρ=0 (via `hinc.2.2`).
- **`incircle_excircleC_distinct`** (I vs C, b-c pair): the missing b-c mirror of AB_distinct.
- **`excircleA_excircleB_distinct`** (A vs B): both flip a-b, so distinguished on b-c — B's pair
  `sₐ=-s_b, sₐ=s_c` forces `s_b=-s_c` (linarith), conflicts with A's `s_b=s_c`.
- **`excircleA_excircleC_distinct`** (A vs C, a-b pair): A flips a-b, C keeps it equal — direct.
- **`excircleB_excircleC_distinct`** (B vs C): agree on b-c, distinguished on a-c — C's pair forces
  `sₐ=-s_c` (linarith), conflicts with B's `sₐ=s_c`; uses the new a-c engine.

### Why this matters
All four tritangent circles share the predicate `SphericalIncircle`; distinctness is not automatic
and is a stated prerequisite for spherical Feuerbach. The matrix is now complete: all 6 pairs are
certified different on any nondegenerate radius (`0<ρ<π`).

### Frontier UNCHANGED (genuinely hard, not attempted)
1. **Spherical nine-point circle** (needs side midpoints — in-flight DRAFT PR #32127
   `research/feuerbach-oq04-midpoint`). Did NOT touch to avoid collision.
2. **The Feuerbach tangency** (nine-point circle tangent to all four). Genuinely hard.

## Session 2026-07-01 (researcher-1): the four tritangent circles are genuinely distinct [VERIFIED]

**Mode**: ACT (CONTINUE). researcher-7 (same day) produced all four tritangent circles
(incircle + 3 excircles) via `sphericalIncircle_exists` / `sphericalExcircle{A,B,C}_exists`,
all satisfying the single predicate `SphericalIncircle`, distinguished only by the returned
sign relations `⟪O,Nᵢ⟫ = ±⟪O,Nⱼ⟫`. **Missing structural fact**: Feuerbach asserts the
nine-point circle is tangent to *all four* — meaningful only if the four are genuinely
DISTINCT circles. This session proves exactly that. **Outcome**: PROGRESS — added a "The four
tritangent circles are genuinely distinct" section (+4 theorems, ~55 L) to
`FeuerbachsTheoremOQ04.lean`. **Docker build VERIFIED** (`docker-build.sh
Proofs.FeuerbachsTheoremOQ04`, `✔ [7743/7743] Built`, exit 0); **0-sorry, 0-axiom**, no
native_decide (proofs use only `linarith`, `abs_zero`, `Real.sin_pos_of_pos_of_lt_pi`,
`lt_irrefl`).

### What was delivered (appended after `sphericalExcircleC_exists`)
- **`tangent_signs_opposite_imp_sin_zero`** (core) : for a centre tangent to the side with
  pole `Y` (`|⟪O,Y⟫| = sin ρ`), holding both `⟪O,X⟫ = ⟪O,Y⟫` and `⟪O,X⟫ = -⟪O,Y⟫` forces
  `sin ρ = 0` (add the two ⟹ `⟪O,Y⟫ = 0`, then tangency). The one content-bearing lemma; the
  rest are instantiations.
- **`incircle_excircleAB_signs_exclusive`** : incircle relation `⟪O,Na⟫ = ⟪O,Nb⟫` + the
  excircle-A/B flip `⟪O,Na⟫ = -⟪O,Nb⟫` ⟹ `sin ρ = 0` (uses `hinc.2.1`, tangency to `Nb`).
- **`incircle_excircleC_signs_exclusive`** : incircle `⟪O,Nb⟫ = ⟪O,Nc⟫` + excircle-C flip
  `⟪O,Nb⟫ = -⟪O,Nc⟫` ⟹ `sin ρ = 0` (uses `hinc.2.2`, tangency to `Nc`).
- **`incircle_excircleAB_distinct`** (headline) : for a nondegenerate radius `0 < ρ < π`
  (`sin ρ > 0`) NO centre satisfies both the incircle and excircle-A/B sign relations —
  `False`. Certifies the incircle and the excircles are genuinely different circles.

### Why this matters
The four tritangent circles all share the predicate `SphericalIncircle`; distinctness is
NOT automatic and Feuerbach's "tangent to all four" presupposes it. This session pins the
sign patterns (incircle = all-equal, each excircle = one flip) as mutually exclusive on any
nondegenerate radius. Structural prerequisite for stating spherical Feuerbach.

### Frontier UNCHANGED (the genuinely hard steps, per researcher-7)
1. **Spherical nine-point circle** (needs side midpoints — in-flight branch
   `research/feuerbach-oq04-midpoint`).
2. **The Feuerbach tangency itself**: nine-point circle internally tangent to incircle,
   externally to the three excircles. Genuinely hard; not attempted.

### Process notes
- Concurrency hazard (shared-worktree `reset --hard`) — this session committed to a fresh
  branch `feature/researcher-1-feuerbach-oq04-distinct` PRE-BUILD to protect edits, then
  built. Base = `origin/main` (includes researcher-7's merged excircles).
- Docker host UP; build clean, no warnings.

## Session 2026-07-01 (researcher-7): spherical excircles — the other three tritangent circles [VERIFIED]

**Mode**: ACT (CONTINUE). `sphericalIncircle_exists` (already on main) produced *one*
tritangent circle from intersecting the two internal angle bisectors. Feuerbach's theorem
requires the nine-point circle to be tangent to the incircle **and the three excircles**, so
the missing existence ingredient was the other three tritangent circles. **Outcome**:
PROGRESS — added 4 declarations (~70 L) to `FeuerbachsTheoremOQ04.lean`. **Docker build
VERIFIED** (`docker-build.sh Proofs.FeuerbachsTheoremOQ04`, `✔ [7743/7743]`); **0-sorry,
0-axiom**, no native_decide.

### What was delivered (appended after `sphericalIncircle_exists`)
- **`sphericalIncircle_of_abs_eq`** (shared tail) : a unit centre `O` with `|⟪O,Na⟫| =
  |⟪O,Nb⟫| = |⟪O,Nc⟫|` gives a circle `sCircle O (arcsin|⟪O,Na⟫|)` tangent to all three sides.
  Factors the common end of the incircle/excircle proofs (`Real.sin_arcsin` + the
  Cauchy–Schwarz bound `|⟪O,Na⟫| ≤ 1`).
- **`sphericalExcircleA_exists`** : excircle opposite the first vertex, from
  `greatCircles_inter (Na + Nb) (Nb − Nc)` — external bisector of `(Na,Nb)` × internal
  bisector of `(Nb,Nc)`. Returns `⟪O,Na⟫ = −⟪O,Nb⟫ = −⟪O,Nc⟫` (sign of pole a flipped).
- **`sphericalExcircleB_exists`** : from `greatCircles_inter (Na + Nb) (Na − Nc)`, returns
  `⟪O,Na⟫ = −⟪O,Nb⟫`, `⟪O,Na⟫ = ⟪O,Nc⟫` (pole b flipped).
- **`sphericalExcircleC_exists`** : from `greatCircles_inter (Na − Nb) (Nb + Nc)`, returns
  `⟪O,Na⟫ = ⟪O,Nb⟫`, `⟪O,Nb⟫ = −⟪O,Nc⟫` (pole c flipped).

Together with the incircle (all-same-sign), this establishes existence of the full family of
**four tritangent circles** of a spherical triangle — exactly the circles the spherical
nine-point circle must touch in Feuerbach's theorem. The tangency criterion `|⟪O,N⟫| = sin ρ`
is sign-insensitive, so all four satisfy the single `SphericalIncircle` predicate; the
returned sign relations `⟪O,Nᵢ⟫ = ±⟪O,Nⱼ⟫` are what distinguish the four.

GOTCHA: `greatCircles_inter` returns membership `⟪O, N⟫ = 0` for the *pole* `N` (robust to the
`P` vs `−P` antipodal ambiguity — both give inner product `0`), so the sign *relations*
between `⟪O,Na⟫, ⟪O,Nb⟫, ⟪O,Nc⟫` are well-defined and provable; the individual signs are not
(they flip under `O ↦ −O`). Excircle vs incircle is therefore characterised by relative signs.

### Next steps (unchanged direction)
1. **Spherical nine-point circle** for a spherical triangle (needs side midpoints — see the
   in-flight midpoint arc-bisection work, branch `research/feuerbach-oq04-midpoint`).
2. The Feuerbach tangency itself: nine-point circle internally tangent to the incircle and
   externally tangent to the three excircles. This is the genuinely hard remaining step.

## Session 2026-06-28 (researcher-4): antipodal-pole layer — two-pole description of a spherical circle [BUILD-PENDING: Docker outage]

**Mode**: ACT (CONTINUE). The metric layer (`sdist_isMetric`, point separation, triangle
inequality) is **merged to main** (PR #31462). Tangent-point existence
(`sphere_slerp_common_point`, external + internal) is **owned by researcher-3** on branch
`research/feuerbachs-theorem-oq-04-tangent-point` (PR #31452, OPEN, already rebased onto
current main in researcher-3's worktree). To avoid clobbering that in-flight work on the
shared `FeuerbachsTheoremOQ04.lean`, this session adds a **collision-free companion file**
`FeuerbachsTheoremOQ04Antipode.lean` building only on the *merged* API.

**Outcome**: PROGRESS (code complete, build verification blocked). New companion file with 4
elementary lemmas (~25 L), branch `research/feuerbachs-theorem-oq-04-antipodal-pole`.

### What was delivered (`proofs/Proofs/FeuerbachsTheoremOQ04Antipode.lean`, registered in `Proofs.lean`)
- **`onSphere_neg`** : the antipode `−P` of a model point is a model point (`norm_neg`).
- **`scos_neg_right`/`scos_neg_left`** : the spherical cosine flips sign under antipode
  (`⟪P,−Q⟫ = −⟪P,Q⟫`), via `inner_neg_right`/`inner_neg_left`.
- **`sdist_antipode`** : a model point and its antipode are at maximal spherical distance `π`
  (`⟪P,−P⟫ = −‖P‖² = −1`, `Real.arccos_neg_one`).
- **`sCircle_neg_centre`** (headline) : the **two-pole identity**
  `sCircle O ρ = sCircle (−O) (π − ρ)` — a spherical circle is centred on *either* pole with
  complementary angular radius. Proof: `ext` + `simp only [sCircle, Set.mem_setOf_eq,
  scos_neg_right, Real.cos_pi_sub, neg_inj]` collapses both membership conditions to
  `scos P O = cos ρ`. This is the redundancy a spherical incircle/nine-point construction
  must track (each configuration-circle centre comes with an antipodal twin).

### BUILD STATUS — verification blocked by Docker outage (NOT a code error)
First `docker-build.sh Proofs.FeuerbachsTheoremOQ04Antipode` reached **`[7743/7744]` with
zero Lean errors**; it failed only on a filesystem `failed to write ...
FeuerbachsTheoremOQ04.olean: input/output error`. Subsequent retries fail at the
image-build stage: `write /var/lib/desktop-containerd/.../meta.db: input/output error`, and
`docker images | grep lean` lists nothing — Docker Desktop's containerd storage is corrupted.
10+ other `lean-build-*` containers are running, so a Docker restart (the likely fix) would
kill concurrent agents' builds — NOT done unilaterally. The code is elementary (norm_neg /
inner_neg_{right,left} / arccos_neg_one / Set.ext+simp) and is highly likely correct, but per
integrity policy it is **NOT claimed VERIFIED**. Pushed as a **DRAFT** PR; re-run the docker
build once Docker recovers, then flip to ready/VERIFIED.

### Next steps (unchanged direction, after tangent-point #31452 merges)
1. Re-verify this file once Docker is healthy; mark PR ready.
2. **Tangent-point uniqueness** (circles meet in exactly ONE point) — strengthens "tangent";
   needs the geodesic-uniqueness argument. Belongs in the shared file → sequence AFTER #31452.
3. Spherical incircle + nine-point circle; attempt the spherical Feuerbach tangency.

## Session 2026-06-28 (researcher-4): point separation — sdist is a genuine metric [BUILD]

**Mode**: ACT (CONTINUE). The metric foundations + spherical-circle/tangency layers were
already verified on `main`; the one property still missing for `sdist` to be a genuine
metric (besides the hard spherical triangle inequality) was **point separation** — that
`sdist P Q = 0` forces `P = Q`. `main` only had the trivial forward direction
(`sdist_eq_zero_of_eq`). **Outcome**: PROGRESS — added 3 verified declarations
(~30 L). **Docker build VERIFIED** (`docker-build.sh Proofs.FeuerbachsTheoremOQ04`,
`✔ [7743/7743]`); **0-sorry, 0-axiom**, no native_decide.

### What was delivered (appended after `sdist_comm` in `FeuerbachsTheoremOQ04.lean`)
- **`scos_eq_one_iff`** (algebraic core) : for unit `P,Q`, `scos P Q = 1 ↔ P = Q`. Forward
  via `chord_sq` — `‖P−Q‖² = 2 − 2·scos P Q = 0`, so `‖P−Q‖ = 0` (norm nonneg + `nlinarith`)
  and `sub_eq_zero`; backward is `scos_self`.
- **`sdist_eq_zero_iff`** (headline) : for unit `P,Q`, `sdist P Q = 0 ↔ P = Q`. Uses
  `Real.arccos_eq_zero` (`arccos x = 0 ↔ 1 ≤ x`); for unit vectors `scos P Q ≤ 1`, so
  `1 ≤ scos P Q` forces `scos P Q = 1`, then `scos_eq_one_iff`.
- **`sdist_pos`** : distinct model points are at strictly positive spherical distance
  (`lt_of_le_of_ne` on `sdist_nonneg` + `sdist_eq_zero_iff`).

Together with `sdist_self`, `sdist_nonneg`, and `sdist_comm` (all already on `main`), this
makes `sdist` **separate points** — so `(Sⁿ, sdist)` is a genuine metric on the spherical
model *modulo* the spherical triangle inequality (the only remaining axiom of a metric).

GOTCHA: `Real.arccos_eq_zero` is stated as `arccos x = 0 ↔ 1 ≤ x` (a one-sided bound, not
`x = 1`); the `scos P Q ≤ 1` bound is what upgrades `1 ≤ scos` to the equality. For
`‖P−Q‖² = 0 ⇒ ‖P−Q‖ = 0`, `le_antisymm` of a `nlinarith`-proved `≤ 0` with `norm_nonneg`
is robust (avoids guessing the exact `pow_eq_zero_iff` argument form).

### Next steps (unchanged direction)
1. **Spherical triangle inequality** `sdist P R ≤ sdist P Q + sdist Q R` would complete
   `(Sⁿ, sdist)` as a `MetricSpace`. This is the genuinely hard analytic step (arccos
   subadditivity / spherical law of cosines); check `InnerProductGeometry.angle` lemmas
   in Mathlib first — for unit vectors `sdist = InnerProductGeometry.angle`.
2. **Tangent-point existence** for tangent circles (construction-heavy slerp midpoint).
3. Spherical incircle + nine-point circle; attempt the spherical Feuerbach tangency.

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

## Session 2026-06-28 (researcher-1): spherical circles + tangency layer [BUILD]

**Mode**: ACT (CONTINUE — executed researcher-2's next-steps 1 & 2: "define spherical
circle as level set of scos" and "spherical tangency relations"). **Outcome**: PROGRESS
— extended `FeuerbachsTheoremOQ04.lean` (+8 decls, ~70 L) with the spherical-circle and
tangency layer on top of the existing metric foundations. **Docker build VERIFIED**
(`docker-build.sh Proofs.FeuerbachsTheoremOQ04`); **0-sorry, 0-axiom**, no native_decide
(only `Real.cos_arccos`/`Real.arccos_cos`, `real_inner_comm`, `abs_sub_comm` etc.).

### What was delivered (appended to `FeuerbachsTheoremOQ04.lean`)
- **`sdist_comm`** : `sdist P Q = sdist Q P` (via `real_inner_comm`).
- **`cos_sdist`** : `Real.cos (sdist P Q) = scos P Q` for unit `P,Q` — the bridge between
  the metric (`sdist`) and algebraic (`scos`/inner product) descriptions, from
  `Real.cos_arccos` + the `[-1,1]` bounds.
- **`def sCircle (O ρ) := {P | OnSphere P ∧ scos P O = Real.cos ρ}`** — spherical circle
  as a level set of the spherical cosine.
- **`mem_sCircle_iff_sdist`** (headline) : for `O` on the sphere and `ρ ∈ [0,π]`,
  `P ∈ sCircle O ρ ↔ (OnSphere P ∧ sdist P O = ρ)`. Identifies the algebraic level-set
  circle with the metric "points at spherical distance ρ", so tangency calculations can
  switch freely between the two views. Proof: `Real.arccos_cos` (fwd) / `cos_sdist` (bwd).
- **`def InternallyTangent`** (`sdist O₁ O₂ = |ρ₁−ρ₂|`) and **`def ExternallyTangent`**
  (`sdist O₁ O₂ = ρ₁+ρ₂`) — the non-Euclidean tangency relations.
- **`internallyTangent_comm`**, **`externallyTangent_comm`** : both tangency relations are
  symmetric in the two circles (via `sdist_comm` + `abs_sub_comm`/`add_comm`).

### Next steps (unchanged direction)
1. **Tangent-point existence**: for externally/internally tangent circles, exhibit the
   unique common point on the geodesic between centres (spherical slerp
   `P = cos ρ₁ · O₁ + …`) and prove it lies on both `sCircle`s — this is the genuinely
   harder, construction-heavy step (needs unit-norm + level-set verification).
2. Build the spherical incircle and nine-point circle for a spherical triangle.
3. Attempt the spherical Feuerbach tangency itself.

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

## Session 2026-06-28 (researcher-2): spherical model foundations [SURVEY + BUILD]

Fresh stub: `problemStatement.formal` was literally "(formal statement to be added)",
no dedicated Lean file. Gave it a concrete formal grounding and a verified metric
foundation layer.

### Model choice
Mathlib has **no developed hyperbolic-geometry metric** (no hyperboloid / Poincaré-disk
distance), so an axiom-free hyperbolic Feuerbach would require building the model first.
The **spherical** model is free: a point of Sⁿ is a unit vector of any real
`InnerProductSpace ℝ E`, and the geodesic distance is `arccos ⟪P,Q⟫`. Anchored the
problem there.

### New file `proofs/Proofs/FeuerbachsTheoremOQ04.lean` (0-axiom, 0-sorry; docker-build clean)
Primitives: `OnSphere P := ‖P‖=1`, `scos P Q := ⟪P,Q⟫`, `sdist P Q := arccos ⟪P,Q⟫`.
Verified lemmas (foundational axioms only — propext/Classical.choice/Quot.sound, no
Lean.ofReduceBool):
- **chord_sq** (headline): unit vectors ⇒ `‖P-Q‖² = 2 - 2·scos P Q`. The chord–cosine
  bridge that turns spherical tangency into an inner-product equation.
- abs_scos_le_one / scos_le_one / neg_one_le_scos: spherical cosine ∈ [-1,1]
  (Cauchy–Schwarz `abs_real_inner_le_norm` on unit vectors).
- scos_self, sdist_self, sdist_nonneg (arccos_nonneg), sdist_le_pi (arccos_le_pi),
  sdist_eq_zero_of_eq: `sdist` is a well-defined [0,π] angle vanishing on the diagonal.

GOTCHA: under `open scoped RealInnerProductSpace` the notation is plain `⟪x,y⟫` (real
inner product); the `⟪x,y⟫_ℝ` subscript form does NOT parse there (it gets read as a
type ascription `(⟪…⟫ : ℝ)`). chord_sq proved by expanding ⟪P-Q,P-Q⟫ via inner_sub_left/
inner_sub_right + real_inner_self_eq_norm_sq + real_inner_comm, then `ring`.

### Formal statement target (documented, not yet proved)
Spherical circle (O,ρ) := {P : OnSphere P ∧ scos P O = cos ρ}. Two circles internally
tangent iff `sdist O₁ O₂ = |ρ₁−ρ₂|`, externally iff `sdist O₁ O₂ = ρ₁+ρ₂` (non-Euclidean
analog of the Euclidean d=|r₁−r₂| / r₁+r₂ used in the verified Euclidean Feuerbach files).
Spherical Feuerbach: spherical nine-point circle tangent to incircle + 3 excircles.

### Next steps
1. Define spherical circle as a level set of scos; prove membership/tangency algebra via chord_sq.
2. Prove the spherical tangency criterion (sdist of centres = |ρ₁−ρ₂| / ρ₁+ρ₂).
3. Build spherical incircle + nine-point circle for a spherical triangle; attempt tangency.

BLOCKER (hyperbolic side): no Mathlib hyperbolic metric — deferred until spherical case lands.

## Session 2026-06-28 (researcher-3): tangent-point existence (external case) [ACT/DEEP DIVE]

**Mode**: ACT (CONTINUE — executed the standing next-step "tangent-point existence:
exhibit the common point on the geodesic between centres"). **Outcome**: PROGRESS —
added the construction-heavy crux lemma. `FeuerbachsTheoremOQ04.lean` 182→267 lines,
**0 sorry / 0 axiom** (`#print axioms externallyTangent_has_common_point` =
propext/Classical.choice/Quot.sound only; no native_decide). Verified single-file:
`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/FeuerbachsTheoremOQ04.lean` exit 0.

### Delivered
- **`externallyTangent_has_common_point`** (headline): for externally tangent spherical
  circles (O₁,ρ₁),(O₂,ρ₂) with `0 < ρ₁+ρ₂ < π`, the circles share a point — the
  spherical-interpolation (slerp) point
  `P = cos ρ₁ • O₁ + (sin ρ₁ / sin(ρ₁+ρ₂)) • (O₂ − cos(ρ₁+ρ₂) • O₁)`,
  proved to be a model point on BOTH `sCircle`s.
  - `OnSphere P`: ⟪P,P⟫ = cos²ρ₁ + (sinρ₁/s)²·s² = 1 (the tangent vector W = O₂−c•O₁ is
    ⊥ O₁ with ⟪W,W⟫ = s² = 1−c²).
  - `scos P O₁ = cos ρ₁`: ⟪P,O₁⟫ = cos ρ₁ (W ⊥ O₁ kills the second term).
  - `scos P O₂ = cos ρ₂`: ⟪P,O₂⟫ = cos ρ₁ cos(ρ₁+ρ₂) + sin ρ₁ sin(ρ₁+ρ₂) = cos ρ₂ by
    `Real.cos_sub` (angle subtraction (ρ₁+ρ₂)−ρ₁ = ρ₂).

### GOTCHAs
- `real_inner_comm a b : ⟪b,a⟫ = ⟪a,b⟫` (NOT ⟪a,b⟫=⟪b,a⟫). To fold ⟪O₂,O₁⟫→c (with
  c := ⟪O₁,O₂⟫ via `set`) use `(real_inner_comm O₂ O₁).symm`. A bare `simp [real_inner_comm O₂ O₁]`
  inside the proof did NOT fold the term reliably; pass an explicit commuted `have`.
- Use `real_inner_smul_left/right` (real inner) to avoid the `conj` from generic
  `inner_smul_left`.
- `field_simp` on `sinρ₁/s * s^2 = sinρ₁*s` CLOSES the goal — a trailing `; ring` then
  errors "No goals to be solved". Make it a standalone `have hsimp := by field_simp` and
  `ring` only the final (non-division) goal.
- **Capturing build exit code**: `lake … | tail -n; echo $?` reports TAIL's exit, not
  lean's — a false "exit 0". Redirect to a file (`> out 2>&1; echo exit=$?`) to read the
  real status.

### Next steps (unchanged direction)
1. Internal-tangency common point (d = |ρ₁−ρ₂|; analogous slerp, sign care).
2. Uniqueness of the tangent point (it is the ONLY common point).
3. Spherical incircle / nine-point circle constructions, then the Feuerbach tangency.

### Addendum (same session): refactor to shared core + internal-tangency case
Refactored the construction into a single engine **`sphere_slerp_common_point`**
(parameterized by d = sdist O₁ O₂ with the spherical angle relation
`cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d` as a hypothesis), then derived BOTH:
- `externallyTangent_has_common_point` (d = ρ₁+ρ₂; angle relation via cos(ρ₁-(ρ₁+ρ₂))=cos(-ρ₂)).
- `internallyTangent_has_common_point` (d = |ρ₁-ρ₂|, smaller circle inside; angle relation
  via cos(ρ₁-(ρ₁-ρ₂))=cos ρ₂).
File 267→293 lines, all three 0-axiom (verified). EXTRA GOTCHA: a `set c := ⟪O₁,O₂⟫`
(inner product) does NOT let `ring`/`linear_combination` equate a *freshly* rewrite-produced
`⟪O₁,O₂⟫` with `c` (atom mismatch). Fix: set `c := Real.cos d` (a plain real) and rewrite
every inner product to it via an explicit `hcio : ⟪O₁,O₂⟫ = c` (one `rw [hcio]` rewrites all
occurrences). Then the spherical angle hypothesis `hangle`, stated in `cos d`/`sin d`, is
auto-folded to `c`/`s` by `set` and closes hPO₂ with `linear_combination -hangle`.

## Session 2026-06-28 (researcher-3): tangent-point UNIQUENESS [ACT/DEEP DIVE]

**Mode**: ACT (CONTINUE — executed the standing next-step "uniqueness of the tangent
point: it is the ONLY common point"). **Outcome**: PROGRESS — upgraded tangent-point
existence to genuine tangency. `FeuerbachsTheoremOQ04.lean` +94 L (now 486), **0 sorry /
0 axiom** (`#print axioms` on all three new theorems = propext/Classical.choice/Quot.sound
only; no native_decide). Single-file verified: `LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/FeuerbachsTheoremOQ04.lean` exit 0.

### Delivered
- **`sphere_slerp_inter_eq_singleton`** (headline): under the same hypotheses as the
  existence core (`sdist O₁ O₂ = d ∈ (0,π)`, angle relation
  `cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d`), the *whole* intersection
  `sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {Pₛ}` is the singleton at the slerp point. Mechanism:
  any common point `Q` has `⟪Q,Pₛ⟫ = cos²ρ₁ + sin²ρ₁ = 1` (the angle relation supplies the
  cross term `cos ρ₂ − cos d cos ρ₁ = sin ρ₁ sin d`), so
  `⟪Q−Pₛ,Q−Pₛ⟫ = ⟪Q,Q⟫ − 2⟪Q,Pₛ⟫ + ⟪Pₛ,Pₛ⟫ = 1 − 2 + 1 = 0` ⇒ `Q = Pₛ` via
  `inner_self_eq_zero`. NB this is NOT automatic from the metric data: in dim ≥ 3 two
  generic spherical circles meet in an `(n−3)`-sphere; the angle/tangency relation is
  exactly what collapses it to one point.
- **`externallyTangent_unique_common_point`** / **`internallyTangent_unique_common_point`**:
  the singleton-intersection corollaries (same angle-relation discharge as the existence
  versions). These strengthen `..._has_common_point` from "∃ a common point" to "= {P}".

### GOTCHAs
- `real_inner_comm a b : ⟪b,a⟫ = ⟪a,b⟫` (RHS = `⟪a,b⟫`). To rewrite a `⟪P,Q⟫` *into*
  `⟪Q,P⟫` (to then fold with `hQP : ⟪Q,P⟫ = 1`) use `real_inner_comm Q P` (= `⟪P,Q⟫=⟪Q,P⟫`),
  NOT `real_inner_comm P Q` (which targets `⟪Q,P⟫` and so doesn't fire). First attempt with
  `P Q` left goal `1 - 1 - (⟪P,Q⟫ - 1) = 0` unsolved.
- `simpa [scos] using hQO₁` cleanly turns the `sCircle` membership component
  `scos Q O₁ = cos ρ₁` into the inner-product form `⟪Q,O₁⟫ = cos ρ₁` (scos is a def).
- `Set.eq_singleton_iff_unique_mem.mpr ⟨mem, uniq⟩` is the clean way to prove `s = {P}`;
  the membership proof reuses the existence half (hP_sphere/hPO₁/hPO₂) verbatim, so the
  singleton theorem subsumes existence (the `_has_common_point` lemmas are kept as the
  weaker public API).
- The `set c := Real.cos d` / `set s := Real.sin d` discipline from the existence core
  carries over unchanged; `field_simp` (with `hsne : s ≠ 0` in context) closes the
  `sin ρ₁/s * (sin ρ₁ * s) = sin ρ₁^2` cancellation directly.

### Note on rebase
Branch was rebased onto fresh origin/main mid-session (commit hashes changed; the worktree
file jumped to include researcher-4's already-merged point-separation + triangle-inequality
lemmas). No conflict — my additions append after `internallyTangent_has_common_point`.

### Next steps (unchanged direction)
1. Spherical incircle / nine-point circle constructions for a spherical triangle.
2. Attempt the spherical Feuerbach tangency itself, using existence+uniqueness.
3. Optional: tangent-line characterization (common tangent geodesic at Pₛ ⊥ centre geodesic).

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

## Session 2026-06-28 (researcher-3): tangent point on the LINE OF CENTRES + full spec [ACT/CONTINUE]

**Mode**: ACT (CONTINUE — executed standing next-step #3 "tangent-line / collinearity
characterization"). **Outcome**: PROGRESS. `FeuerbachsTheoremOQ04.lean` 486→548 L,
**0 sorry / 0 axiom** (`#print axioms` on all five touched theorems =
propext/Classical.choice/Quot.sound only; no native_decide / Lean.ofReduceBool). Verified
single-file: `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/FeuerbachsTheoremOQ04.lean` exit 0.

### Delivered
- Strengthened **`sphere_slerp_inter_eq_singleton`** to also conclude the unique contact
  point `P ∈ Submodule.span ℝ {O₁, O₂}` — the geodesic (great circle) through the two
  centres, i.e. the spherical "line of centres". Proof: `P` is literally
  `cos ρ₁ • O₁ + (sin ρ₁/sin d) • (O₂ − cos d • O₁)`, so span membership is
  `Submodule.add_mem/smul_mem/sub_mem` over `Submodule.subset_span` on `{O₁,O₂}`.
- Threaded the span conjunct through **`externallyTangent_unique_common_point`** /
  **`internallyTangent_unique_common_point`** (pure pass-through, statements strengthened).
- **`sphere_slerp_tangent_point_spec`** (full characterization core): unique point, on the
  line of centres, AND `sdist P O₁ = ρ₁`, `sdist P O₂ = ρ₂`. Radii via `Real.arccos_cos`
  (needs `ρᵢ ∈ [0,π]`): the witness `P ∈ {P}` is a member of the intersection, so
  `scos P Oᵢ = cos ρᵢ`; `sdist P Oᵢ = arccos⟪P,Oᵢ⟫ = arccos(cos ρᵢ) = ρᵢ`.
- **`externallyTangent_tangent_point_spec`**: external-case corollary (`ρᵢ ≤ π` auto from
  `ρ₁+ρ₂ < π` + nonnegativity via linarith).

### GOTCHAs
- The singleton theorem hides its witness `P` behind `∃`. To extract membership facts for
  the spec, recover `P ∈ inter` from `inter = {P}` via `rw [hsing]; rfl` (`rfl : P ∈ {P}`),
  then destructure to get `scos P Oᵢ = cos ρᵢ`.
- `Real.arccos_cos : 0 ≤ x → x ≤ π → arccos (cos x) = x`. Drive `sdist P Oᵢ = ρᵢ` by
  `rw [sdist, show (⟪P,Oᵢ⟫:ℝ) = Real.cos ρᵢ from hsc, Real.arccos_cos h0 hpi]` (sdist unfolds
  to `arccos ⟪P,Oᵢ⟫`; scos = ⟪⟫ is definitional so the membership component `hsc` fits the
  `show`).
- External `hdpos : 0 < ρ₁+ρ₂` is NOT derivable from `0≤ρ₁, 0≤ρ₂` alone — keep it as an
  explicit hypothesis; only the upper bounds `ρᵢ ≤ π` come free from `ρ₁+ρ₂<π`.

### Branch/merge note (recurring)
On reclaim, origin/main already had the EXISTENCE work (`sphere_slerp_common_point`,
`externallyTangent/internallyTangent_has_common_point`, 373 L) squash-merged, but NOT the
uniqueness commit. `git rebase origin/main` conflicted on my own already-squashed existence
commit. Recovery: `rebase --abort` → fresh branch off origin/main → drop in my HEAD file
(its 1–372 prefix is byte-identical to origin/main; everything new is a pure append) →
single commit. knowledge.md likewise a clean superset (append-only).

### Next steps (unchanged direction)
1. Spherical incircle / nine-point circle constructions for a spherical triangle.
2. Attempt the spherical Feuerbach tangency itself, using existence+uniqueness+line-of-centres.
3. Optional: tangent geodesic at P is ⊥ the centre geodesic (the metric "tangent line" fact).

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

## Session 2026-06-30 (researcher-2): internal-tangency full tangent-point spec [VERIFIED, 0-axiom]

The metric layer is COMPLETE (`sdist_isMetric` at line ~195 now on main — the once-"hard frontier"
spherical triangle inequality is done via Mathlib's `InnerProductGeometry.angle_le_angle_add_angle`,
transported by `sdist_eq_angle`). Tangent-point theory has external+internal existence and uniqueness,
plus the FULL external spec (`externallyTangent_tangent_point_spec`: contact point on the geodesic
through the centres, at spherical distances ρ₁,ρ₂). The internal case stopped at
`internallyTangent_unique_common_point` — no full spec. **Filled that symmetry gap.**

- `internallyTangent_tangent_point_spec` (VERIFIED, docker `[7744/7744]`, `#print axioms` =
  [propext,Classical.choice,Quot.sound], 0-axiom). Specializes `sphere_slerp_tangent_point_spec`
  with d = ρ₁−ρ₂ (internal tangency ⟹ centres at spherical distance ρ₁−ρ₂ via `abs_of_pos`); the
  addition law `cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d` degenerates because ρ₁−(ρ₁−ρ₂)=ρ₂
  (`rw [← Real.cos_sub, show ρ₁-(ρ₁-ρ₂)=ρ₂ from by ring]`, no `Real.cos_neg` unlike external's
  ρ₁+ρ₂ case). Range bounds 0≤ρ₁ and ρ₂≤π auto from 0<ρ₁−ρ₂, ρ₁≤π via `linarith`.
  Signature: `(hρ₂0 : 0≤ρ₂) (hρ₁pi : ρ₁≤π) (hpos : 0<ρ₁−ρ₂) (hlt : ρ₁−ρ₂<π)`.

File now 568L/29thm/6def, 0-sorry/0-axiom. Shipped as PR (no gallery entry exists for this OQ-child;
tracked via research json + this knowledge.md). GOTCHA: fresh /tmp worktree's `proofs/` got WIPED
mid-session (empty dir, likely infra/concurrent cleanup after a failed git-128 mathlib-clone) losing an
uncommitted edit — recreate worktree + COMMIT before building.

### Next steps (unchanged, all hard/construction-heavy)
1. Tangent-point uniqueness geodesic argument refinements.
2. Spherical incircle + nine-point circle constructions, then the spherical Feuerbach tangency (the
   genuine open target — multi-session).

## Session 2026-07-01 (researcher-1): circle-to-great-circle tangency (incircle↔side primitive) [VERIFIED, 0-axiom]

**Mode**: ACT (CONTINUE — executed standing next-step "spherical incircle construction",
building the missing tangency primitive it needs). Prior work had the full **circle-circle**
tangency theory (existence/uniqueness/spec, common perpendicular tangent). The spherical
incircle is tangent to the triangle's **sides**, which are arcs of *great circles*, not
other circles — so circle-circle tangency does not directly apply. Filled that gap.

**Outcome**: PROGRESS. `FeuerbachsTheoremOQ04.lean` 724→856L, **0 sorry / 0 axiom**, docker
`✔ [7743/7743]`, no warnings, no native_decide (only ring/linarith/nlinarith/field_simp/simp
+ `Real.cos_pos_of_mem_Ioo`, `Real.sin_sq_add_cos_sq`, `sq_abs`, reused `scos_eq_one_iff`,
`mem_sCircle_iff_sdist`).

### Delivered
- **`sGreatCircle N := {P | OnSphere P ∧ ⟪P,N⟫ = 0}`** — great circle = geodesic = triangle
  side (unit pole `N`).
- **`greatCircleFoot O N ρ := (cos ρ)⁻¹ • (O − ⟪O,N⟫ • N)`** — explicit contact point (the
  renormalised orthogonal projection of the centre onto the great circle).
- **`TangentToGreatCircle O ρ N := |⟪O,N⟫| = sin ρ`** — tangency criterion (distance from
  centre to the side = radius; the distance is `arcsin|⟪O,N⟫|`).
- **`inner_orthoComp_self` / `inner_orthoComp_left`** — helper: `⟪O⊥,O⊥⟫ = ⟪O⊥,O⟫ =
  1 − ⟪O,N⟫²` (spherical Pythagoras for the projection; `inner_orthoComp_left` needs only
  `OnSphere O`, not `hN`).
- **`greatCircleFoot_mem`** (existence): under `0≤ρ<π/2` + criterion, the foot is a model
  point on BOTH `sCircle O ρ` and `sGreatCircle N`. All three checks are pure inner-product
  algebra: `⟪F,N⟫=0`, `⟪F,O⟫=cos ρ`, `‖F‖²=(cos ρ)⁻²·(1−⟪O,N⟫²)=(cos ρ)⁻²·cos²ρ=1`.
- **`circle_tangent_greatCircle_inter`** (headline): the intersection is the **singleton**
  `{greatCircleFoot O N ρ}` — genuine tangency (one contact point). Uniqueness: any common
  `Q` has `⟪Q,F⟫ = (cos ρ)⁻¹(⟪Q,O⟫ − ⟪O,N⟫·⟪Q,N⟫) = (cos ρ)⁻¹(cos ρ − 0) = 1`, so `Q=F`
  by `scos_eq_one_iff`.
- **`sdist_greatCircleFoot_center`** : `sdist (foot) O = ρ` (via `mem_sCircle_iff_sdist`).

### Why this matters
This is the **incircle-to-side tangency primitive**, consumed three times (once per side)
in any spherical incircle/excircle construction. It bridges the existing circle-circle
tangency theory to an actual spherical incircle → the genuine open target (spherical
Feuerbach). Kept the criterion in the clean geometric form `|⟪O,N⟫| = sin ρ`; internally
squared it (`sq_abs`) to `⟪O,N⟫² = sin²ρ`, then `1 − sin²ρ = cos²ρ` via
`Real.sin_sq_add_cos_sq`.

### GOTCHAs
- `scos Q O` is definitionally `⟪Q,O⟫` but `rw` needs a syntactic match: extract
  `hQO' : (⟪Q,O⟫:ℝ) = cos ρ := hQO` (defeq `have`), then `rw [hQO']`.
- To turn `|⟪O,N⟫| = sin ρ` into `⟪O,N⟫² = sin²ρ`: `rw [← sq_abs, htan]` (sq_abs: `|a|²=a²`).
- OnSphere-from-inner-1 idiom (reused from `sphere_slerp_common_point`): `‖F‖²=1` →
  `(‖F‖−1)(‖F‖+1)=0` via `nlinarith` → `mul_eq_zero` → exclude the negative root by
  `norm_nonneg` + `positivity`.
- Don't `set` the inner product `⟪O,N⟫` (ring atom-mismatch trap from prior sessions);
  keep it explicit and let `ring` treat it as an atom.

### Next steps (unchanged direction, still multi-session)
1. Define a spherical triangle (3 model points) and its three side great circles (poles =
   normalised cross-products / the geodesic normals); state the spherical incircle as the
   circle tangent to all three sides via `TangentToGreatCircle`.
2. Existence/uniqueness of the incenter (equidistant-from-sides point) — likely the hard
   step; may need a spherical angle-bisector argument.
3. Spherical nine-point circle, then the spherical Feuerbach tangency itself.

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

### Addendum (same session, researcher-1): great-circle unification + spherical incircle scaffolding [VERIFIED, 0-axiom]

Stacked on the tangency-primitive commit (856→894L, docker `✔ [7743/7743]`, 0-axiom/0-sorry).

- **`sGreatCircle_eq_sCircle`** : `sGreatCircle N = sCircle N (π/2)` — great circles ARE the
  radius-`π/2` spherical circles (`cos(π/2)=0`; one-line `simp only [sGreatCircle, sCircle,
  scos, Real.cos_pi_div_two]`). Unifies great-circle tangency with the earlier circle-circle
  tangency: a side is just a special circle.
- **`SphericalIncircle Na Nb Nc O ρ`** := tangent to all three side poles (three
  `TangentToGreatCircle`s).
- **`sphericalIncircle_contact_points`** : an incircle (`0≤ρ<π/2`) meets each of the three
  sides in exactly one point — the three feet — via three applications of
  `circle_tangent_greatCircle_inter`. This is the spherical "incircle tangent to all three
  sides", the first Feuerbach ingredient, with explicit contact points.

REMAINING HARD STEP (unchanged): existence/uniqueness of the incenter `O` for a *given*
triangle (spherical angle-bisector / equidistant-locus argument) — not asserted here. Then
spherical nine-point circle + the Feuerbach tangency.

### Addendum (same session, researcher-1): spherical angle bisectors + incenter-on-bisectors [VERIFIED, 0-axiom]

Attacks the "remaining hard step" above — the equidistant-locus / angle-bisector mechanism
that pins the incenter. Three new theorems (894→953L, docker `✔ [7743/7743]`, 0-axiom/0-sorry),
PR #32087, branch `research/feuerbach-oq04-bisectors`.

Key idea: the spherical distance from `O` to the side with unit pole `N` is `arcsin |⟪O,N⟫|`,
so `O` is equidistant from sides `Na, Nb` iff `|⟪O,Na⟫| = |⟪O,Nb⟫|`. By `abs_eq_abs` this
splits into the two bisectors `⟪O, Na∓Nb⟫ = 0`.

- **`bisector_poles_orthogonal`** : `⟪Na−Nb, Na+Nb⟫ = ‖Na‖²−‖Nb‖² = 0` for unit poles — the
  internal and external bisectors are perpendicular great circles (Euclidean picture carries
  over). Proof: expand `inner_sub_left`/`inner_add_right`, `real_inner_self_eq_norm_sq`, `ring`.
- **`equidistant_two_sides_iff`** : `|⟪O,Na⟫| = |⟪O,Nb⟫| ↔ ⟪O,Na−Nb⟫=0 ∨ ⟪O,Na+Nb⟫=0`.
  Pure sign analysis: `rw [inner_sub_right, inner_add_right, abs_eq_abs]` then `linarith` both ways.
- **`sphericalIncircle_center_on_bisectors`** : an incircle centre lies on a bisector of each
  of the three pairs — the structural characterisation of the incenter as an intersection of
  angle bisectors. Proof: destructure the three `TangentToGreatCircle`s, chain `ta.trans tb.symm`.

### Addendum (same session, researcher-1): INCENTER EXISTENCE [VERIFIED, 0-axiom]

Closes the "remaining hard step" — the incenter now provably EXISTS. (953→1020L, docker
`✔ [7743/7743]`, 0-axiom/0-sorry, same PR #32087.) Two new theorems:

- **`greatCircles_inter`** [`FiniteDimensional ℝ E`, `finrank > 2`] : the two great circles
  with poles `Na, Nb` meet in an antipodal pair `±P` (unit, `P ≠ −P`, both on both circles).
  KEY REUSE: the already-merged `exists_common_perp_tangent` gives a nonzero `T ⊥ Na, Nb`
  (its span has finrank ≤2, so `Kᗮ` is nontrivial when finrank>2); normalise `P = ‖T‖⁻¹•T`.
  `P ≠ −P` via `two_smul`+`smul_eq_zero`. NO pole-independence hypothesis needed (span≤2 always).
- **`sphericalIncircle_exists`** [`finrank > 2`] : for ANY three unit poles `Na, Nb, Nc`,
  ∃ O ρ, `SphericalIncircle Na Nb Nc O ρ`. Construct O = intersection of the two INTERNAL
  bisectors (poles `Na−Nb`, `Nb−Nc`) via `greatCircles_inter`; `inner_sub_right` on the two
  membership eqns forces `⟪O,Na⟫=⟪O,Nb⟫=⟪O,Nc⟫`; set `ρ = arcsin|⟪O,Na⟫|`, with
  `Real.sin_arcsin` (bound via `abs_real_inner_le_norm`, unit norms) closing all three
  `TangentToGreatCircle` = `|⟪O,N⟫| = sin ρ` goals. Only `hNa : OnSphere Na` needed (Nb,Nc
  norms unused since equal-inner + arcsin handles them).

Note: uses INTERNAL bisectors → equal SIGNED inner products (stronger than the abs-equal locus),
which is exactly what a single radius ρ needs. Incircle here is the tangent-to-3-great-circles
notion; centre may or may not be interior — a genuine incenter (interior) needs a sign/hemisphere
refinement.

REMAINING: (1) uniqueness / interior-incenter refinement; (2) spherical nine-point circle;
(3) the Feuerbach tangency itself (nine-point circle tangent to the incircle). The hard
existence-of-incenter obstacle is now cleared.

## Session 2026-07-08 (researcher-2): inner-product form of the tangency criteria [VERIFIED — 0 sorry, 0 axiom]

**Mode:** ACT (add a bounded, reusable ingredient toward the sole frontier item — the
Feuerbach tangency capstone). The full tritangent family, incircle/excircle existence,
nine-point circle, and abstract tangent-point specs are all in place; the missing bridge
is turning the *distance* tangency predicates into the *inner-product* equations one
actually computes from coordinates.

**Added to `FeuerbachsTheoremOQ04.lean`** (2 theorems, +~46 L, docker `✔ [7743/7743]`,
first try, 0 sorry / 0 axiom / 0 native_decide):
- **`externallyTangent_iff_scos`** (`0 ≤ ρ₁+ρ₂ ≤ π`):
  `ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ scos O₁ O₂ = cos (ρ₁+ρ₂)`.
- **`internallyTangent_iff_scos`** (`|ρ₁−ρ₂| ≤ π`):
  `InternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ scos O₁ O₂ = cos (ρ₁−ρ₂)`.

Proof pattern (both): `unfold` the tangency def, `rw [← cos_sdist O₁ O₂ h₁ h₂]` to turn the
RHS `scos` into `cos (sdist …)`; forward = `rw [h]`; backward = `Real.injOn_cos` on
`Set.Icc 0 π` (memberships from `sdist_nonneg`/`sdist_le_pi` and the radius-range hyps).
Internal case first rewrites `← Real.cos_abs (ρ₁−ρ₂)` so the target reads `cos |ρ₁−ρ₂|`,
matching the `InternallyTangent` definition `sdist = |ρ₁−ρ₂|`.

**Why this matters:** the final Feuerbach tangency ("nine-point circle internally tangent to
the incircle") now reduces to a *single inner-product identity* `⟪O₉, O_in⟫ = cos(ρ₉ − ρ_in)`
between the two explicit centres — exactly the coordinate-level target the remaining work
must hit. This is the criterion, not the identity itself (still the hard capstone).

**Metadata:** reconciled badly-stale `leanFiles` entry for this file (568→1310 lines,
29→65 theorems; prior sessions grew it far past the recorded numbers).

**Frontier unchanged:** the tangency identity between the concrete nine-point and incircle
centres remains the sole hard open item.

## Session 2026-07-08 (researcher-1): the spherical midpoint bisects the arc [VERIFIED — 0 sorry, 0 axiom]

**Mode:** ACT (add a bounded, reusable ingredient). The nine-point circle exists
(`sphericalNinePointCircle_exists`) and the tangency *criterion* is in place; the remaining
frontier is the hard tangency capstone. A clean gap elsewhere: `sMidpoint` was proven
*equidistant* from its endpoints (`sdist_sMidpoint_eq`) but never proven to actually **bisect
the arc** — a point equidistant from `A, B` need not be their midpoint (the antipode of the
true midpoint is equidistant too).

**Added to `FeuerbachsTheoremOQ04Midpoint.lean`** (3 theorems, 119→199 L, docker `Built`,
0 sorry / 0 axiom / 0 native_decide):
- **`norm_add_sq_unit`** — `‖A+B‖² = 2 + 2⟪A,B⟫` (polarisation with unit norms).
- **`scos_sMidpoint_left`** — explicit vertex-to-midpoint spherical cosine
  `scos A (sMidpoint A B) = ‖A+B‖⁻¹(1+⟪A,B⟫)`.
- **`sdist_sMidpoint_half`** — `sdist A (sMidpoint A B) = ½·sdist A B`, the arc-bisection
  fact that justifies the name.

**Proof pattern (reusable):** to prove `sdist A M = sdist A B / 2` avoid half-angle lemmas —
instead prove `2·sdist A M = sdist A B` via `Real.injOn_cos` on `[0,π]`:
- `scos A M = ‖A+B‖⁻¹(1+⟪A,B⟫) ≥ 0`, so `sdist A M = arccos(scos A M) ≤ π/2`
  (`Real.arccos_le_pi_div_two.mpr`), giving `2·sdist A M ∈ [0,π]`.
- double angle `Real.cos_two_mul`: `cos(2·sdist A M) = 2·(scos A M)² − 1`; with
  `(scos A M)² = (1+⟪A,B⟫)/2` (from `‖A+B‖²=2+2⟪A,B⟫`) this collapses to `⟪A,B⟫ = cos(sdist A B)`.
- `Real.injOn_cos` closes `2·sdist A M = sdist A B`.
Developed first in a Mathlib-only scratch file (host `lake env lean`, fast) replicating the
primitives, then ported — the companion imports local `Proofs.*` modules so it only builds
under the docker wrapper.

**Frontier unchanged:** the Feuerbach tangency capstone (concrete nine-point vs incircle
centre, the identity `⟪O₉,O_in⟫ = cos(ρ₉−ρ_in)`) remains the sole hard open item.
