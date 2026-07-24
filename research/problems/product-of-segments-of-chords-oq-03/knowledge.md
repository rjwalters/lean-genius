# Knowledge Base: product-of-segments-of-chords-oq-03

## S1 OBSERVE (researcher-11, 2026-05-12)

Initial survey of the power-of-a-point ↔ four-point concyclicity determinant bridge.
Goal: discharge `converse_product_implies_concyclic_axiom` in the parent file by a
linear-algebra route (the implicit-circle equation $x^2 + y^2 + Dx + Ey + F = 0$
together with Cramer's rule).

## Mathematical Background

### The implicit-circle equation

Every circle in $\mathbb{R}^2$ admits the implicit form
$$
x^2 + y^2 + D x + E y + F = 0,
$$
with centre $(-D/2, -E/2)$ and radius $\sqrt{D^2/4 + E^2/4 - F}$ (assuming the radicand
is positive). The map (circle) ↔ (D, E, F) is a bijection onto its image; degenerate
choices (radicand $= 0$ a single point; radicand $< 0$ empty) need to be handled.

Four points $P_i = (x_i, y_i)$ satisfy a common circle equation iff the linear system
$$
\begin{pmatrix}
x_1 & y_1 & 1 \\
x_2 & y_2 & 1 \\
x_3 & y_3 & 1 \\
x_4 & y_4 & 1
\end{pmatrix}
\begin{pmatrix} D \\ E \\ F \end{pmatrix}
=
- \begin{pmatrix} x_1^2 + y_1^2 \\ x_2^2 + y_2^2 \\ x_3^2 + y_3^2 \\ x_4^2 + y_4^2 \end{pmatrix}
$$
has a solution. This $4 \times 3$ system is solvable iff the augmented $4 \times 4$ has
rank 3 — equivalently iff the concyclicity determinant
$$
\Delta = \det
\begin{pmatrix}
x_1^2 + y_1^2 & x_1 & y_1 & 1 \\
x_2^2 + y_2^2 & x_2 & y_2 & 1 \\
x_3^2 + y_3^2 & x_3 & y_3 & 1 \\
x_4^2 + y_4^2 & x_4 & y_4 & 1
\end{pmatrix}
$$
vanishes.

### Why this works

Expand $\Delta$ along the first row using `Matrix.det_succ_row_zero` (or directly via
`Matrix.det_fin_four`). The four cofactors are $3 \times 3$ determinants in $(x, y, 1)$
which encode (a) the squared circumradius of any three of the four points, and (b) the
signed area of the triangle they form. Vanishing of $\Delta$ is the algebraic shadow of
the geometric fact that the fourth point lies on the circle through the other three.

### Power of a point connection

If $A, B, C, D$ are concyclic and two chords $AB$, $CD$ meet at $P$, the parent file's
`power_of_point_product` (line 250) gives
$$
\|P - A\| \cdot \|P - B\| = |\text{pow}(P)| = \|P - C\| \cdot \|P - D\|.
$$
**Conversely**, if $\|P - A\| \cdot \|P - B\| = \|P - C\| \cdot \|P - D\|$ and the chords
through $P$ are collinear lines (i.e. $A, P, B$ collinear and $C, P, D$ collinear), then
the four chord-roots $t_A, t_B, t_C, t_D$ (parametrising distance from $P$ along the
chord directions) satisfy the same quadratic discriminant — which when written out via
$\|P - A\|^2 = \|A\|^2 - 2 A \cdot P + \|P\|^2$ reduces to a row-equivalence in the
$4 \times 4$ matrix above, forcing $\Delta = 0$.

The bridge calculation is elementary: subtract row $j$ from row $i$ in $\Delta$ and the
first column becomes $\|P_i\|^2 - \|P_j\|^2 = (P_i - P_j) \cdot (P_i + P_j)$. Using
collinearity, this is a scalar multiple of $(P_i - P_j) \cdot \hat{n}$ for a direction
$\hat{n}$ along the chord, and the product equality forces the determinant of the
reduced matrix to vanish by a Vieta-style argument.

## Likely-Useful Mathlib API

### Matrix and determinant

- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` — `Matrix.det`, `Matrix.det_fin_four`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Cofactor` — cofactor expansion if direct
  `det_fin_four` is too slow.
- `Mathlib.Data.Matrix.Notation` — `!![row1; row2; row3; row4]` matrix syntax.

### Cramer's rule

- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` — `Matrix.cramer`,
  `Matrix.mulVec_cramer`.
- For our use, the key fact is: a $3 \times 3$ matrix is non-singular iff its determinant
  is non-zero, so `Matrix.det_ne_zero_of_left_inverse` etc.

### Euclidean plane

- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — `EuclideanSpace ℝ (Fin 2)`.
- Parent file uses `Vec2 := Fin 2 → ℝ` (abbrev). We follow the same convention.

### Squared norm expansion

- `inner_sub_sub_self`, `norm_sub_sq_real`, `norm_sq_eq_inner` — for expanding
  $\|P_i - P_j\|^2$.

## Known Adjacent Results

- Parent gallery proof: `product-of-segments-of-chords` —
  `Proofs/ProductOfSegmentsOfChords.lean` (541 lines, 11 theorems, **1 axiom**).
- Sibling `product-of-segments-of-chords-oq-01`: 3D generalisation (power of a point for
  spheres). Independent of OQ-03, but shares the algebraic machinery.
- Cross-reference: `ptolemys-theorem` (also a concyclicity criterion, but via segment
  identities rather than determinants).
- Mathlib has `Affine.Simplex.circumcenter` and `Affine.Simplex.circumradius` for the
  $(n+1)$-point case in $\mathbb{R}^n$; specialised to the planar four-point case via
  `Affine.Simplex.dist_circumcenter_eq_circumradius`. **Not yet used** in the parent
  file — could be a shortcut for the (⇒) direction.

## Mathlib Gaps (preliminary — confirm during S2)

1. **No specialised concyclicity-determinant lemma.** Mathlib's `Matrix.det_fin_four`
   handles the expansion, but there is no `Matrix.concyclicityDet_eq_zero_iff` or
   equivalent.
2. **No `circleThroughThreePoints` constructor in the parent file.** The parent uses
   `axiom converse_product_implies_concyclic_axiom` precisely because it lacks this
   construction. Mathlib's `Affine.Simplex.circumcenter` exists; integrating it requires
   bridging `Vec2 := Fin 2 → ℝ` (parent) with `EuclideanSpace ℝ (Fin 2)` (Mathlib).
3. **No bridge lemma between power-of-a-point and the implicit-circle equation.** The
   identity `‖P − A‖ · ‖P − B‖ = |D · x_P + E · y_P + F + x_P² + y_P²|` (with $D, E, F$
   the circle coefficients) is implicit in the parent's `chord_product_algebraic` but
   not named.

## Numerical Sanity Check

Take four points on the unit circle: $A = (1, 0)$, $B = (0, 1)$, $C = (-1, 0)$,
$D = (0, -1)$. Then
$$
\Delta =
\det\begin{pmatrix}
1 & 1 & 0 & 1 \\
1 & 0 & 1 & 1 \\
1 & -1 & 0 & 1 \\
1 & 0 & -1 & 1
\end{pmatrix} = 0,
$$
since rows 1+3 = rows 2+4 (both equal $(2, 0, 0, 2)$). ✓

Now move $D$ off the circle: $D = (0, -2)$. Then row 4 becomes $(4, 0, -2, 1)$ and
$$
\Delta = -6 \ne 0.
$$
**Concyclic ⇔ $\Delta = 0$** verified on this case.

> **Correction (S17, 2026-06-13):** the S1 figure $\Delta = -8$ was a
> hand-computation slip. The correct value is $\Delta = -6$: row-reduce by
> subtracting row 1 from rows 2–4, then expand along column 4 (only row 1 is
> nonzero there, cofactor sign $-1$); the surviving $3\times3$ minor evaluates
> to $6$, so $\Delta = -1 \cdot 6 = -6$. This is machine-checked by the merged
> lemma `concyclicityDetCoords_off_circle` (PR #22967, S7b ACT), which proves
> `concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-2) = -6`.

## S2 SCAFFOLD (researcher-3, 2026-05-12)

Created `Proofs/ProductOfSegmentsOfChordsOQ03.lean` (106 LOC, 1 sorry):

- `concyclicityDetCoords` — raw $4 \times 4$ determinant in 8 real variables.
- `concyclicityDet` — `Vec2`-level wrapper accessing `P 0` / `P 1`.
- Two numerical examples (both `simp [Matrix.det_fin_four]; ring`-closed).
- Stub statement `concyclicityDet_eq_zero_iff_concyclic` with `sorry`.

### Notable design decisions

1. **Two-layer definition.** The coord form `concyclicityDetCoords` keeps the
   numerical sanity checks free of `EuclideanSpace`-norm gymnastics; the Vec2
   wrapper `concyclicityDet` is what S3 / S4 / S5 consume.
2. **Placeholder non-collinearity.** S2 punts on the exact form of the
   non-degeneracy hypothesis by using `(hNonCollinear : True)` — S3 will pick
   between `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` and a stronger 3×3
   invertibility statement on the first three rows of the implicit-circle
   linear system.
3. **`Matrix.det_fin_four` for the examples.** Direct cofactor expansion of
   the $4 \times 4$ determinant produces a polynomial expression that `ring`
   can close; `decide` and `norm_num` alone are not sufficient because the
   matrix entries are reals.

### Build status

Build pending. Local docker-build was attempted twice from
`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-3`:

- **Attempt 1**: ran from worktree, `proofs/.lake` symlink loop (main repo's
  `proofs/.lake` is `.lake -> /Users/.../proofs/.lake` — a self-loop) caused
  Mathlib source lookups to fail inside Docker.
- **Attempt 2**: removed the broken symlink, lake re-cloned Mathlib, but
  the clone was partial (truncated mid-download); `lake exe cache get` then
  failed with `no such file or directory: lean-toolchain` on the
  `.lake/packages/mathlib/lean-toolchain` path. The worktree was wiped by a
  daemon respawn before the build could be re-attempted.

The Lean code itself is straightforward and should compile cleanly from a
healthy worktree.

## Dead Ends

(None yet — this is the first session.)

## Decomposition Plan (S2–S6, see state.md)

- **S2** *(done, build pending — PR ...)*: Define `concyclicityDet` and
  `concyclicityDetCoords`, prove both numerical examples, state the main
  theorem with `sorry`.
- **S3**: Prove the (⇐) direction (`Δ = 0` ⇒ exists circle through all four), assuming
  $P_1, P_2, P_3$ non-collinear, by constructing $(D, E, F)$ via Cramer (~80 lines).
- **S4**: Prove the (⇒) direction (concyclic ⇒ $\Delta = 0$) by row reduction (~30 lines).
- **S5**: Bridge: chord-product equality ⇒ $\Delta = 0$. Uses `chord_roots_product` and
  the row-subtract identity above (~50 lines).
- **S6**: Replace `converse_product_implies_concyclic_axiom` with a theorem proved from
  S3 + S5 (~10 lines). Update parent meta.json: `axiomCount` 1 → 0,
  `status` axiomatized → verified.

## S18 ACT (researcher-1, 2026-07-24)

Headline iff proven (see state.md banner and the S18 session memo). Portable
lessons:

1. **The `(hNonCollinear : True)` placeholder was mathematically load-bearing**:
   with it the (⟹) direction is false (distinct collinear points give Δ = 0,
   no circle). The S2-era "S3 will pick the right non-degeneracy form" debt
   had to be paid before the sorry could close. Installed form:
   `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)`, bridged to the algebraic
   `collinearityDet ≠ 0` via `collinear_iff_of_mem` + coordinate-ratio
   witnesses.
2. **No `Matrix.cramer` needed — and no `field_simp` on squared quotients.**
   The S1/S18-note plan (Cramer API on the implicit-circle system) is heavier
   than explicit quotient circumcenter coordinates. But `field_simp; ring`
   directly on the squared-distance equality FAILS: the `(x-O₀)²` terms
   square the quotients and field_simp leaves uncancelled `(...)⁻¹ ^ 2`
   atoms that `ring` cannot kill (a first attempt also blew
   `maxRecDepth 512` inside field_simp). Working pattern: a division-free
   helper `bisector_to_dist` (`linear_combination -hb` — the `O₀²/O₁²` terms
   cancel, so the identity is *linear* in the center coordinates), plus a
   deterministic denominator-clearing chain on the linear bisector equations:
   `rw [← mul_div_assoc, ← mul_div_assoc, div_add_div_same, div_eq_iff h2d];
   ring`.
3. **Column-multilinearity beats row reduction for the forced fourth point**:
   `Δ = e₁M₁ − e₂M₂ + e₃M₃ − e₄M₄` (eᵢ = circle defects, Mᵢ = (x,y,1)-minors,
   M₄ = collinearityDet) is an *exact* polynomial identity; the S7b simp set
   (`Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero,
   Fin.succAbove`) + `ring` proves it first try, and
   `linear_combination -hΔ' + M₁*e₁ - M₂*e₂ + M₃*e₃` collapses it to
   `e₄·M₄ = 0`.
4. **v4.31 `WithLp` is a structure** (`toLp`/`ofLp`, `CoeFun` via `ofLp`):
   build points with `WithLp.toLp 2 ![a, b]`; coordinate projections are
   `rfl`. Point equality via `PiLp.ext`. **Avoid `fin_cases` on coordinate
   indices** — it produces `⟨0, ⋯⟩`/`⟨1, ⋯⟩` Fin atoms that `ring`/
   `linear_combination` treat as distinct from the literal `0`/`1` atoms;
   `rw [Fin.forall_fin_two]` after `apply PiLp.ext` keeps everything literal.
5. **`rcases hp with rfl | rfl | rfl` on `p ∈ {P₁, P₂, P₃}` has
   non-deterministic subst orientation** across sibling branches (one branch
   kept `P₃`, another eliminated it as `p`), producing "Unknown identifier"
   only in *some* branches. Deterministic fix: bind the last case as
   `hpe : p = P₃` and `rw [hpe]` in the goal instead of substituting.
6. `pow_left_inj₀ (norm_nonneg _) hr (two_ne_zero-proof)` is the v4.31 name
   for squaring-injectivity on nonnegatives (old `pow_left_injective` /
   `sq_eq_sq'` searches dead-end).

## S19 ACT (researcher-2, 2026-07-24) — COMPLETION

Bridge proven, problem complete (see state.md banner and the S19 session
memo). Portable lessons:

1. **Check sibling-OQ artifacts before executing a stale plan.** The S12-§3.2
   closed-form polynomial witness and the whole S20 parent-integration step
   were obsolete: the OQ-02 line had already (a) refuted the unsigned axiom
   (`unsigned_converse_counterexample`), (b) proven the signed converse with
   an explicit Cramer circumcenter (`signed_converse_implies_concyclic` in
   `Proofs/ProductOfSegmentsOfChordsConverse.lean`), and (c) flipped the
   parent gallery meta to `verified` (PR #24873). S19 collapsed from a
   projected heavy `linear_combination` session to a ~20-line composition:
   Part 6 scalar bridge → Converse circumcircle → Part 8 (⟸) direction.
2. **`LinearIndependent ℝ ![u, v]` componentwise nonvanishing**:
   `by simpa using hindep.ne_zero 0` gives `u ≠ 0` (the `![…] 0` reduces
   under `simpa` without naming `Matrix.cons_val_zero`); `sub_ne_zero.mp`
   turns `A - P ≠ 0` into `A ≠ P`.
3. **Cross-file `abbrev Vec2` duplicates unify definitionally** — composing
   theorems across `ProductOfSegmentsOfChordsOQ03` and
   `ProductOfSegmentsOfChordsConverse` namespaces needed no casts.
4. `Proofs.lean` is intentionally import-free; lake `globs` auto-discovers
   every `Proofs/*.lean`, so the Converse file (header says "NOT registered
   until built") has in fact been building since the v4.31 migration
   (#39062) — its header note is stale, trust the build.
