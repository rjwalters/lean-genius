# hilbert-17-oq-03 — knowledge

## Problem
"Complexity of Deciding PSD Polynomial Sum-of-Squares" — what is the
computational complexity of deciding whether a given PSD polynomial is a sum of
squares. This is a **complexity meta-question**, not a clean Lean theorem
target. The underlying mathematical substance is the PSD ⊋ SOS separation,
whose canonical witnesses are the Motzkin and Robinson polynomials.

## Session 2026-06-24 (researcher-1) — axiom elimination in parent hilbert-17
The parent entry `hilbert-17` (Hilbert17SumOfSquares.lean) carried 10 axioms,
two of which were *non-negativity* claims discharged here:

- `motzkin_nonneg`  (M = x⁴y²+x²y⁴−3x²y²+1 ≥ 0): the AM–GM step
  `x⁴y²+x²y⁴+1 ≥ 3x²y²` is a polynomial inequality `nlinarith` closes from
  square hints `(x²y²−1)², (x²y−y)², (xy²−x)²` and `x²y² ≥ 0`. No cube-root.
- `robinson_nonneg` (R = Σx⁶ − Σx⁴y² + 3x²y²z² ≥ 0): with a=x², b=y², c=z² ≥ 0,
  R IS Schur's expression `a(a−b)(a−c)+b(b−a)(b−c)+c(c−a)(c−b)`; `nlinarith`
  finds the constrained certificate from `a·(a−b)² ≥ 0` terms + `abc ≥ 0`.

Both now `#print axioms` → propext/Classical.choice/Quot.sound only.
**axiomCount 10 → 8.** Reduction step in `IsPositiveSemidefiniteMv`:
`intro v; simp only [<poly def>, map_add, map_sub, map_mul, map_pow, map_ofNat,
map_one, MvPolynomial.eval_X]; set x := v 0; …; nlinarith [...]`.

### Gotcha
- `def motzkin : MvPolynomial …` in a scratch needs `noncomputable`; in the real
  file it already lives in a context where it builds. The THEOREM proofs are
  computable-irrelevant — only the eval reduction + nlinarith matter.

## Session 2026-06-24 (researcher-1) — Motzkin non-SOS direction DONE
Shipped child entry `hilbert-17-oq-03-oq-02` (`Proofs/Hilbert17MotzkinNotSOS.lean`,
verified / 0-axiom, 25 thm-lemma / 3 def / 427 L): a fully elementary proof that
the Motzkin polynomial is **not** a sum of squares of polynomials — exactly the
parent axiom `motzkin_not_sos_polynomial_aux`. Three moves:
1. **degree_bound**: in `M = Σ qᵢ²`, every `qᵢ` has `totalDegree ≤ 3`. Core lemma
   `topsq`: `homogeneousComponent (2D) (p²) = (homogeneousComponent D p)²` (split
   `p = top + lo`, cross/lo² have degree `< 2D`). The degree-`2D` part of `Σ qᵢ²`
   is `Σ (top form)²`; over ℝ this is `0` only if each top form is `0`
   (`sum_sq_eq_zero` via `MvPolynomial.funext`), but `M` has degree 6 < 2·4.
2. **pure-axis vanishing**: extractions `pureX_extract`/`pureY_extract` collapse
   the `[x^{2n}]`/`[y^{2n}]` antidiagonal to `([xⁿ]qᵢ)²`; the chains x⁶→x⁴→x²,
   y⁶→y⁴→y² kill all pure powers of x,y (deg 1–3) in every `qᵢ`.
3. **coeff22_sq**: `[x²y²] qᵢ² = ([xy]qᵢ)²` (only surviving antidiagonal pair).
   ⟹ `−3 = [x²y²]M = Σ ([xy]qᵢ)² ≥ 0`, contradiction.

### Gotchas (v4.26)
- Finsupp antidiagonals don't `decide`; reason about a generic pair via its
  membership eq `a+b=μ` + `Finset.sum_eq_single_of_mem`, then component case-split.
- `coeff_homogeneousComponent` uses `Finsupp.degree d` (= `d 0 + d 1` on Fin 2).
- `totalDegree_monomial_le _ _ : ≤ s.degree` displays as `s.sum (fun _ e => e)`;
  bridge with a `calc … ≤ (mon a b).degree := …` (defeq) then `degree_mon`.
- `2*3 = 6` etc. reduce by `rfl`, so `mon (2*n) 0` is defeq `mon 6 0` — extraction
  results land on the literal monomials with no rewrite needed.
- ABSPATH WARNING: built/verified in MAIN `proofs/` (mathlib cache); `cp` to
  worktree, scrub strays from MAIN, never commit there.

## Session 2026-06-24 (researcher-1) — wired Motzkin proof into parent (axiom 8 → 7)
Discharged the parent axiom `motzkin_not_sos_polynomial_aux` by importing the
child entry into `Hilbert17SumOfSquares.lean` and replacing the axiom-wrapper
theorem with a direct proof:
```lean
import Proofs.Hilbert17MotzkinNotSOS
...
theorem motzkin_not_sos_polynomial : ¬ IsSumOfSquaresMvPolynomial motzkin := by
  intro h; exact Hilbert17MotzkinNotSOS.motzkin_not_sos h
```
The parent's `motzkin` (defined via `let x := X 0; let y := X 1; …`) and
`IsSumOfSquaresMvPolynomial` are **definitionally equal** to the child's
`motzkin` / `IsSOS`, so `exact … h` typechecks by defeq (no bridge lemma
needed). Built clean in MAIN: `motzkin_not_sos_polynomial` `#print axioms` →
propext/Classical.choice/Quot.sound only. **Parent axiomCount 8 → 7**; updated
gallery `meta.json` (both `.meta` and `.leanFile`), dropped the assumption,
added the import, refreshed prose.

### Gotcha (this session)
- FLEET WIPE hit the *worktree* (not just MAIN): both edits were reset to HEAD
  (git clean) between the verifying build and the commit. The build had already
  proven the exact content compiles 0-axiom, so I re-applied the two edits and
  **committed immediately** before re-verifying. Commit first, polish after.
- MAIN's `proofs/Proofs/Hilbert17SumOfSquares.lean` gets re-wiped to HEAD
  repeatedly by the fleet sync; don't trust a post-build `grep` on MAIN — trust
  the olean / `#print axioms` from the build that ran, and the worktree commit.

## Session 2026-06-24 (researcher-1) — Robinson non-SOS: method does NOT transfer (survey)
Assessed whether the elementary Motzkin coefficient-extraction proof transfers to
`robinson_not_sos_aux`. **It does not**, and the reason is structural:

- Robinson `R = x⁶+y⁶+z⁶ − Σ_sym x⁴y² + 3x²y²z²` is *homogeneous* of degree 6.
  The degree-bound step DOES generalize cleanly: in `R = Σ qᵢ²`, the top- and
  bottom-degree homogeneous components force every `qᵢ` to be a homogeneous
  **cubic** in `x,y,z` (10 monomials: x³,y³,z³,x²y,x²z,xy²,y²z,xz²,yz²,xyz).
- BUT the Motzkin engine worked because affine Motzkin has **zero** coefficients
  on every pure power (no x⁶, x⁴, x², …, no y⁶, …): those zeros force
  `[x³]qᵢ = [x²y]qᵢ = … = 0`, collapsing each `qᵢ` until only `[xy]qᵢ` survives,
  and then the single coefficient `[x²y²]M = −3 = Σ([xy]qᵢ)² ≥ 0` contradicts.
- Robinson has `[x⁶]=[y⁶]=[z⁶] = +1` (nonzero) ⟹ `Σᵢ([x³]qᵢ)² = 1` etc.: the
  cubic coefficients are NOT forced to vanish, so there is no "kill-the-coeffs"
  cascade. Worked the coefficient identities: the six `[x⁴y²]`-type coeffs each
  give `Σᵢ(qᵢ-quadratic) = −1` but each is `(square) + 2·(cross)` — the cross
  terms (`2 pᵢsᵢ` etc.) are sign-indefinite, so **no single coefficient nor any
  obvious linear combination yields a `Σ(perfect squares) = negative`** the way
  `[x²y²]M` did. Robinson's non-SOS-ness sits on the *boundary* of the SOS cone.
- Correct proof routes (both real projects, not one-coefficient tricks):
  (a) **Dual functional / Gram-matrix infeasibility**: exhibit a linear `L` on
      degree-6 forms, PSD on squares of cubics, with `L(R) < 0`. This `L` is
      *not* a combination of point evaluations (those give `L(R)=ΣλₖR(Pₖ)≥0`);
      it must be supported with 2nd-order data at R's projective zeros.
  (b) **Zero-set dimension count** (Reznick/Choi–Lam): every `qᵢ` vanishes at the
      common real projective zeros of R (the coordinate points [1:0:0],[0:1:0],
      [0:0:1] and the sign points [±1:±1:±1]); the space of cubics vanishing
      there is too small to span the needed Gram rank.
  Neither has a short Mathlib path; estimate ≥ a dedicated multi-session effort
  (Gram-matrix PSD machinery or a hand-built dual certificate). **Flagged: do
  not attempt as a quick coefficient port — it will become scaffolding.**

## Still open
- `robinson_not_sos` — needs route (a) or (b) above, NOT the Motzkin port.
  Would discharge `robinson_not_sos_aux` (parent 7 → 6).
- Remaining 7 parent axioms are genuinely deep (Artin transfer, Hilbert 1888
  classification, Pfister/Cassels bounds) — not routine Mathlib lookups.
- The actual complexity classification (SOS membership ≈ SDP feasibility) — a
  meta/complexity statement; unclear how to formalize meaningfully in Lean.

## Session 2026-06-24 (researcher-1) — redundant-axiom elimination (parent 7 → 4)
Three of the parent's seven axioms were not independent assumptions at all — each
was a logical *restatement* of a deeper axiom already in the same file. Converted
all three from `axiom` to derived `theorem`:
- **`artin_hilbert17`** (∃ m, p = Σ gᵢ² over RatFunc) ⟸ `pfister_bound_aux`:
  Pfister already gives the existence with the explicit count `2ⁿ`, so
  `fun n p h => ⟨2^n, pfister_bound_aux n p h⟩`.
- **`cassels_bound_bivariate`** (Fin 4 squares, n=2) ⟸ `pfister_bound_aux 2`:
  `2^2 = 4` reduces by rfl, so `Fin (2^2)` is *defeq* `Fin 4` and
  `pfister_bound_aux 2 p h` has exactly the target type — `:= pfister_bound_aux 2 p h`.
- **`artin_univariate`** (RatFunc SOS) ⟸ `univariate_psd_is_sos_aux` (polynomial SOS):
  apply the ring hom `algebraMap (Polynomial ℝ) (RatFunc ℝ)` to `p = Σ qᵢ²`,
  giving `algebraMap p = Σ (algebraMap qᵢ)²` via `map_sum` + `simp_rw [map_pow]`.

Mechanics: moved the two surviving deep axioms (`univariate_psd_is_sos_aux`,
`pfister_bound_aux`) into a "FOUNDATIONAL AXIOMS" block right after Part I so the
backward derivations (statements appear *before* their sources in the pedagogical
ordering) typecheck. `artin_hilbert17` is used downstream (`motzkin_sos_ratfunc`)
so it could not be moved; only its source axiom needed relocating.

Verified in MAIN (mathlib cache, `lake env lean`, exit 0):
- `#print axioms artin_hilbert17` → propext/Classical.choice/**pfister_bound_aux**/Quot.sound
- `#print axioms artin_univariate` → …/**univariate_psd_is_sos_aux**/…
- `#print axioms cassels_bound_bivariate` → …/**pfister_bound_aux**/…
No independent artin/cassels axioms remain. **Parent axiomCount 7 → 4.** Updated
gallery meta (`.meta.axiomCount`, `.leanFile.axiomCount`, assumptions list, prose).

Remaining 4 independent axioms are the genuinely deep ones:
`univariate_psd_is_sos_aux` (Hilbert 1888 univariate / FTA), `quadratic_psd_is_sos_aux`
(Gram/spectral), `pfister_bound_aux` (Pfister forms), `robinson_not_sos_aux`
(boundary-of-cone, needs dual-functional or zero-set route per prior survey).

### Gotcha (this session)
- FLEET WIPE recurred: the worktree edits were reset to HEAD between the first
  edit pass and the build check (git status went clean, 7 axioms back). Re-applied
  all six edits and **committed before building** — committing creates a HEAD that
  includes the change, so a subsequent "reset to HEAD" preserves it. Build-verify
  against the committed state, amend only if needed.
- MAIN's mathlib oleans live at `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/`
  and Proofs oleans at `.lake/build/lib/lean/Proofs/` (note the extra `lean/` segment
  in this toolchain layout) — the older `.lake/build/lib/Proofs/` path is empty.
- Removing an `axiom` that carried a `/-- … -/` docstring leaves an *orphan*
  docstring (must attach to a decl) → convert the leftover to a plain `/- … -/`
  comment or Lean errors.

## Session 2026-06-24 (researcher-1) — Robinson non-SOS PROVED (corrects prior survey)
**The prior survey was wrong**: Robinson non-SOS does NOT need Gram-matrix /
dual-functional multi-session machinery. The elementary **zero-set / linear-
algebra** route works. Shipped child entry `hilbert-17-oq-03-oq-03`
(`Proofs/Hilbert17RobinsonNotSOS.lean`, verified / 0-axiom, 32 thm-lemma / 3 def
/ 423 L) and wired it into the parent, discharging `robinson_not_sos_aux`
(**parent axiomCount 4 → 3**).

Proof (R = x⁶+y⁶+z⁶ − Σx⁴y² + 3x²y²z², homogeneous deg 6):
1. **degree bound**: in R = Σqᵢ², each qᵢ has totalDegree ≤ 3 (reuse Motzkin
   `topsq`/`degree_bound`, generalized to any `σ`).
2. **homogeneous reduction (the key simplification)**: `comp₆(R) = R` (R homog
   deg 6, proved via `IsHomogeneous` built from `isHomogeneous_X_pow`/`.mul`/
   `.add`/`.sub`), so `R = Σ (comp₃ qᵢ)²` by `topsq` with D=3 (2·3=6). Each
   `comp₃ qᵢ` is genuinely a homogeneous **cubic form** — NO bottom-degree
   cascade needed (this was the worry that made it look hard).
3. **zero set**: R vanishes at its 10 real projective zeros (1,±1,0),(1,0,±1),
   (0,1,±1),(1,±1,±1); sum-of-squares=0 ⟹ each cubic form vanishes at all 10.
4. **linear algebra (`cubic_zero`)**: the 10×10 matrix of the 10 cubic monomials
   at the 10 points has **det = 128 ≠ 0** (verified exactly in python first), so
   the only homogeneous cubic vanishing at all 10 is 0. ⟹ every comp₃ qᵢ = 0 ⟹
   R = 0, contra R(1,0,0)=1.

### Why the earlier "Motzkin coeff method doesn't transfer" survey missed this
The survey only considered the *coefficient-cascade* method (kill pure powers),
which genuinely fails for Robinson (x⁶ coeff = +1 ≠ 0, no cascade). But the
*zero-set* method is a different, cleaner argument: R's 10 zeros impose 10
**independent** conditions on the 10-dim space of ternary cubics (det 128). The
Motzkin file used coeff extraction because affine Motzkin has only 2 real zeros
in the relevant sense; Robinson's 10 projective zeros are exactly enough.

### Lean formalization techniques (v4.26)
- `cubic_zero` finish: `as_cubic` rewrites a homog cubic as Σ of its 10
  monomial terms (ext + `deg3_cases` enumerating degree-3 exponent vectors via
  `interval_cases a<;>interval_cases b<;>interval_cases c<;> first|(exfalso;omega)|simp`);
  `eval_mon3` turns each point-eval into a linear form in the 10 coeffs; then
  `rw[E] at h1..h10; norm_num[Matrix.cons_val_*] at h1..h10; linarith` per coeff.
  `linarith` solves the determined 10×10 system treating `coeff (mon3 ..) q` as
  opaque atoms (DON'T `set` them — the `set` let-binding breaks the final
  `rw [hcub]` which reintroduces unfolded `coeff` terms).
- GOTCHAS: `(3 : MvPolynomial _).IsHomogeneous 0` — numeral fights inference;
  `rw [map_ofNat]` to get `= C 3`, then `isHomogeneous_C _ _` (σ AND r both
  explicit — `isHomogeneous_C` takes the type first). `homogeneousComponent_of_mem`
  + `if_pos rfl` in one `rw` list → "CommSemiring ?m stuck" (rfl leaves branch
  types undetermined); prove `comp₆ R = R` by `ext d; coeff_homogeneousComponent;
  by_cases d.degree=6` + `robinson_isHom.coeff_eq_zero` instead. `Xpp3` needs
  trailing `rfl` (mon3 defeq the single-sum). `(C : ℝ →+* _)` with `_` codomain
  → stuck; write the codomain explicitly.
- Parent wiring identical to Motzkin: `import Proofs.Hilbert17RobinsonNotSOS`;
  `theorem robinson_not_sos := by intro h; exact …RobinsonNotSOS.robinson_not_sos h`
  (parent `robinson`/`IsSumOfSquaresMvPolynomial` DEFEQ child `robinson`/`IsSOS`).
- BUILD: child `import Mathlib` only (self-contained), built clean in MAIN
  (`LAKE_UNSAFE=1 lake env lean`); `#print axioms` = propext/Classical.choice/
  Quot.sound. MAIN parent .lean gets fleet-wiped to origin/main (8 axioms!) — the
  7→4 ancestor work is unmerged; verify the WORKTREE parent by cp+`lake env lean`
  atomically (race the sync), trust `#print axioms Hilbert17.robinson_not_sos`.

## Still open (parent hilbert-17, 3 axioms)
- `univariate_psd_is_sos_aux`, `quadratic_psd_is_sos_aux`, `pfister_bound_aux` —
  the genuinely deep, independent ones (Fundamental-Thm-of-Algebra factorization /
  Gram-Cholesky for quadratics / Pfister's 2ⁿ bound). Not quick coefficient ports.

## Session 2026-06-24 (researcher-1) — Univariate PSD = SOS PROVED (parent axiom 3 → 2)
Shipped child entry `hilbert-17-oq-03-oq-04` (`Proofs/Hilbert17UnivariatePSDSOS.lean`,
verified / 0-axiom, 5 thm + 1 def / 208 L) and wired it into the parent, discharging
`univariate_psd_is_sos_aux` (**parent axiomCount 3 → 2**). This is the univariate case
of Hilbert's 17th (Hilbert 1888): a non-negative `p : ℝ[X]` is a sum of *two* squares
`u² + v²`.

Proof = strong induction on `natDegree` (`Nat.strongRecOn`):
1. **base**: `deg 0` ⟹ `p = C c`, `c ≥ 0` (eval at 0), `c = (C √c)² + 0²` via
   `Real.sq_sqrt`. (GOTCHA: `rw [hpc]` rewrote `p` *inside* `Real.sqrt (p.coeff 0)`
   too → `conv_lhs => rw [hpc]` to touch only the LHS.)
2. **deg ≥ 1**: FTA `Complex.exists_root` on `p.map (algebraMap ℝ ℂ)` (degree via
   `degree_map` + `degree_eq_natDegree`) gives a root `z`; `aeval z p = 0` from
   `aeval_def + ← eval_map`.
   - **z real** (`z.im = 0`): real root `r = z.re` (`hzr : z = algebraMap ℝ ℂ z.re`
     via `Complex.coe_algebraMap` + `Complex.ext`; `hpr` via
     `aeval_algebraMap_apply_eq_algebraMap_eval` + `exact_mod_cast`). Analytic crux
     `sq_dvd_of_psd_root`: a real root of a PSD poly has mult ≥ 2 — if mult = 1 then
     `p = (X-C r)·g`, `g r ≠ 0`, and one-sided limits (`ge_of_tendsto` on `𝓝[>] r`,
     `le_of_tendsto` on `𝓝[<] r`, `mul_nonneg_iff_of_pos_left` / `mul_neg_of_neg_of_pos`)
     force `g r ≥ 0` AND `g r ≤ 0`, contra. So `(X-C r)² ∣ p`; quotient PSD (incl. at
     `r` itself by a right-limit), `natDegree` drops by 2, IH ⟹ `(X-C r)²(u²+v²)` =
     `((X-C r)u)² + ((X-C r)v)²`.
   - **z non-real** (`z.im ≠ 0`): `quadratic_dvd_of_aeval_eq_zero_im_ne_zero` gives
     `Q = X² - C(2 z.re) X + C ‖z‖² ∣ p`. `Q = (X-C z.re)² + (C z.im)²` (use
     `‖z‖² = z.re² + z.im²` via `Complex.normSq_eq_norm_sq` + `normSq_apply`; expand C
     with `C_add, C_pow, C_mul, map_ofNat` THEN `ring`). `Q > 0` everywhere ⟹ quotient
     PSD with NO limit needed (`mul_nonneg_iff_of_pos_left (hQpos x)`); `natDegree`
     (via `compute_degree!`) drops by 2; IH + **Brahmagupta–Fibonacci** recombine.

Wiring: parent `IsPositiveSemidefinite`/`IsSumOfSquaresPolynomial` are **defeq** to the
child's `IsPSD` / `univariate_psd_is_sos` conclusion, so the axiom becomes
`theorem univariate_psd_is_sos_aux p h := Hilbert17UnivariatePSDSOS.univariate_psd_is_sos p h`.
Verified in MAIN (mathlib cache, `lake env lean`): child + parent both
`#print axioms → propext/Classical.choice/Quot.sound`. The parent's downstream
`artin_univariate` / `univariate_psd_is_sos` now also 0-axiom.

### Why this matters / corrects the strand
The univariate case is the ONLY case where the *polynomial* conclusion holds — exactly
the positive counterpart to the Motzkin (oq-03-oq-02) and Robinson (oq-03-oq-03)
counterexamples that force rational functions for n ≥ 2.

## Still open (parent hilbert-17, 2 axioms remain)
- `quadratic_psd_is_sos_aux` — PSD quadratic form is SOS of linear forms. Route: Gram
  matrix ↔ symmetric `A`, `A` PSD ⟹ `A = BᵀB` (Cholesky / spectral, Mathlib
  `Matrix.posSemidef...`). The poly↔matrix bridge + extracting linear forms is the work.
- `pfister_bound_aux` — Pfister's 2ⁿ bound. Genuinely deep (Pfister forms / formally
  real fields); no short Mathlib path.

### Gotchas (this session)
- `ne_of_gt (hy : r < y) : y ≠ r` already (NOT `r ≠ y`) — do **not** `.symm` it before
  `sub_ne_zero.mpr` (wanted `y - r ≠ 0`).
- `lake env lean` writes NO olean; to typecheck the parent (which imports the child)
  I built the child olean explicitly with `lake env lean <child> -o .lake/build/lib/lean/Proofs/<child>.olean`
  then `lake env lean <parent>`.
- MAIN's working copy of `Hilbert17SumOfSquares.lean` is STALE vs this branch (still has
  old `artin_univariate_aux` axioms) — edit/commit the WORKTREE copy; only borrow MAIN
  for its mathlib cache (back up + restore MAIN, scrub stray child .lean/.olean).
- Aristotle MCP/API is DOWN this session (smoke test: 404 on .../api/v1/project) — the
  HARD-sorry route was unavailable; proved everything manually.

## Survey 2026-06-24 (researcher-1) — quadratic_psd_is_sos_aux route + Mathlib gap
Scoped the next axiom `quadratic_psd_is_sos_aux` (Q : MvPolynomial (Fin n) ℝ,
totalDegree Q = 2, PSD ⟹ SOS). This is the (n, 2d)=(n,2) row of Hilbert's
PSD=SOS classification — it holds for EVERY n (only n=1, deg-2, and (2,4) are SOS=PSD).

**Route (Gram / matrix):** homogenize Q (deg ≤ 2) by an extra coordinate x₀ to a
quadratic form in (x₀, x₁,…,xₙ); extract the (n+1)×(n+1) symmetric coefficient
matrix M with Q.eval x = (1,x)ᵀ M (1,x); show PSD-everywhere ⟹ M.PosSemidef; factor
M = BᵀB; then Q = ‖B·(1,x)‖² = Σ (affine-linear)² — a polynomial SOS.

**Mathlib pieces present:**
- `Matrix.PosSemidef`, `Matrix.posSemidef_iff_dotProduct_mulVec`
  (M PSD ⟺ ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x) — the matrix↔quadratic-positivity bridge.
- `Matrix.PosSemidef.sqrt` (+ `sqrt_mul_self`) gives M = √M·√M with √M Hermitian, i.e.
  the BᵀB factorization over ℝ (B := √M, symmetric).
- `QuadraticMap.associated` / `polarBilin` (quadratic form ↔ symmetric bilinear, 2 invertible).

**Genuine GAP (the multi-session work):** there is NO Mathlib helper connecting
`MvPolynomial (Fin n) ℝ` of `totalDegree = 2` to a `QuadraticForm` / symmetric matrix.
Must hand-build: (a) the coefficient-extraction `Q ↦ M` over the homogenizing
coordinate, (b) `Q.eval x = (1,x)ᵀ M (1,x)` as a `MvPolynomial`/eval identity, (c)
`(∀ x, 0 ≤ Q.eval x) ⟺ M.PosSemidef` (the ⟸ is dotProduct_mulVec; the ⟹ needs that
the affine slice (1,x) ranges over enough vectors — careful with the x₀=1 normalization,
PSD of M is about ALL (t,x) incl t=0, so need a limiting/scaling argument t·(1, x/t)),
and (d) reassembling `‖B·(1,x)‖²` back into `IsSumOfSquaresMvPolynomial`. Estimate:
a dedicated multi-session build (~300–500 L), comparable to the univariate file but with
the matrix↔polynomial bridge as the hard, un-Mathlib'd part. NOT a quick port.

`pfister_bound_aux` remains genuinely hopeless for a short proof (Pfister forms over
formally real fields). The two remaining parent axioms are correctly left axiomatized.

## Session 2026-06-24 (researcher-1) — BUILT the verified matrix Gram core
Discharged the *matrix-level* heart of `quadratic_psd_is_sos_aux` into a new
zero-axiom file `proofs/Proofs/Hilbert17QuadraticGram.lean` (namespace `Hilbert17`):

- `sqrt_transpose_eq_self`  : `(√M)ᵀ = √M`  — over ℝ the Hermitian sqrt is symmetric
  (`isHermitian` ⟹ `conjTranspose_eq_transpose_of_trivial`).
- `posSemidef_eq_transpose_mul_sqrt` : `(√M)ᵀ * √M = M`  — the real Gram factorization.
- `posSemidef_quadratic_isSumSq` (headline): for `M.PosSemidef`,
  `x ⬝ᵥ (M *ᵥ x) = ∑ i, ((√M *ᵥ x) i)²` — an explicit SOS of linear forms.
- `posSemidef_exists_sumSq` : packaged `∃ B, ∀ x, xᵀMx = ∑ ((B*ᵥx) i)²` (B = √M).
- `posSemidef_matrixQuadratic_isSumSq` (NEW headline, COMPLETE homogeneous case):
  for `M.PosSemidef`, the homogeneous degree-2 polynomial `∑ i j, C(M i j)·Xᵢ Xⱼ`
  satisfies `IsSumOfSquaresMvPolynomial` (existence form) — equals `∑ k, (∑ j, C(√M k j)·Xⱼ)²`.

`#print axioms` → propext/Classical.choice/Quot.sound only (0 real axioms).

### SLICK polynomial-equality route (the key trick)
`IsSumOfSquaresMvPolynomial` is *polynomial EQUALITY* (`∃ q, p = ∑ q²`), NOT eval.
Don't grind the MvPolynomial double-sum algebra — use `MvPolynomial.funext`
(ℝ is `[CommRing][IsDomain][Infinite]`): reduce `p = q` to `∀ x, eval x p = eval x q`,
then `simp only [map_sum, map_mul, map_pow, eval_C, eval_X]` turns both eval sides
into ℝ-sums and the matrix lemma `posSemidef_quadratic_isSumSq` closes it. Need
`simp only [dotProduct, mulVec] at key` to unfold the matrix lemma to bare ℝ-sums,
then `rw [← key]` + `Finset.sum_congr … (Finset.mul_sum) … ring`. Compiled FIRST TRY.

### Engine (the calc)
`xᵀMx = xᵀ(SᵀS)x = xᵀ(Sᵀ(Sx)) = (xᵥ*Sᵀ)·(Sx) = (Sx)·(Sx) = ∑ (Sx)i²`, using
`mulVec_mulVec`, `dotProduct_mulVec`, `vecMul_transpose`, `dotProduct`+`pow_two`.
S := `CFC.sqrt M` (the modern CFC sqrt; the `Matrix.PosSemidef.sqrt` API is now
DEPRECATED→use `CFC.sqrt`, `CFC.sqrt_nonneg`, `CFC.sqrt_mul_sqrt_self`).

### Gotchas
- Needs `open scoped MatrixOrder` (brings the `StarOrderedRing`/`PartialOrder`
  instance so `0 ≤ M` / `CFC.sqrt_nonneg` typecheck). Without it: "failed to
  synthesize PartialOrder (Matrix …)".
- `IsHermitian` is a `def` (`Aᴴ = A`) — `rw [conjTranspose_eq_transpose_of_trivial]`
  can't see the `ᴴ` through the wrapper; ascribe the type explicitly
  `have h : (CFC.sqrt M)ᴴ = CFC.sqrt M := …isHermitian` first, THEN rw.
- DOCKER DOWN this session (daemon hangs; `docker version`/`info` never return,
  docker-build.sh returned exit 0 with empty output and NO olean). Worktree
  `.lake/packages/mathlib/.lake/build` is EMPTY (0 oleans). Verified instead by
  `cd <MAIN>/proofs && LAKE_UNSAFE=1 ./bin/lake env lean /tmp/copy.lean` — MAIN's
  cache has the 7376 mathlib oleans; `lake env lean` on one file only READS them
  (no mathlib writes, concurrency-safe). Registered in `proofs/Proofs.lean`.

### Remaining bridge (still open, multi-session)
The polynomial↔matrix coefficient extraction (`Q : MvPolynomial (Fin n) ℝ`,
`totalDegree = 2` ↦ symmetric `M`) + homogenisation/PSD transfer + reassembly
into `IsSumOfSquaresMvPolynomial`. The Gram engine above is what that bridge
will call. `pfister_bound_aux` still genuinely hard.

## Session 2026-06-24 (researcher-1) — HOMOGENEOUS quadratic PSD=SOS PROVED (polynomial level)
Completed the entire **homogeneous** case of `quadratic_psd_is_sos_aux` at the
polynomial level, 0 axioms, extending `Hilbert17QuadraticGram.lean` (now 325 L).
The prior Gram work only had the *matrix-given* form
(`posSemidef_matrixQuadratic_isSumSq`: given a PSD matrix M, `∑ᵢⱼ C(Mᵢⱼ)XᵢXⱼ` is
SOS). This session built the missing **polynomial → matrix bridge** for arbitrary
homogeneous degree-2 `Q`:

- `homogeneous_quadratic_psd_isSumSq` (HEADLINE): `Q.IsHomogeneous 2` ∧
  `(∀x, 0 ≤ eval x Q)` ⟹ `∃ q, Q = ∑ qᵢ²`. Every PSD homogeneous real quadratic
  form in n variables is a polynomial SOS of linear forms. `#print axioms` →
  propext/Classical.choice/Quot.sound only.
- `quad_repr`: `Q.IsHomogeneous 2 ⟹ Q = ∑ᵢⱼ C(quadMatrix Q i j)·Xᵢ·Xⱼ` where
  `quadMatrix Q i j = if i=j then coeff(single i 2)Q else coeff(single i 1+single j 1)Q/2`
  (symmetric Gram matrix). Proved by `MvPolynomial.ext` coeff comparison.
- Supporting: `degree_two_cases` (a deg-2 exponent vector is `single k 2` or
  `single a 1+single b 1`, a≠b), `match_diag`/`match_offdiag` (which (i,j) realize
  a given deg-2 monomial), `sum_ite_diag`/`sum_ite_offdiag` (collapse the coeff
  double sums via product+filter = singleton/pair), `quadMatrix_transpose` (symm).

Assembly of the headline: `quad_repr` gives `Q = ∑ᵢⱼ C(Mᵢⱼ)XᵢXⱼ`; then
`x ⬝ᵥ (M *ᵥ x) = eval x Q ≥ 0` ⟹ `M.PosSemidef`; then
`posSemidef_matrixQuadratic_isSumSq` finishes. `M = quadMatrix Q`.

### Why this does NOT yet discharge the parent axiom (honest)
`quadratic_psd_is_sos_aux` is stated for **affine** `totalDegree Q = 2` (allows
degree 1 and 0 terms), NOT homogeneous. So parent axiomCount stays at **2**
(`quadratic_psd_is_sos_aux`, `pfister_bound_aux`). What remains is the standard
homogenisation: lift Q to a homogeneous quadratic Q* in n+1 vars (add x₀,
multiply the degree-1 part by x₀ and the constant by x₀²), show Q* PSD (the
degree-2 top part must be PSD by a scaling limit; the rest is t²Q(x/t)≥0), apply
`homogeneous_quadratic_psd_isSumSq` to Q*, then set x₀=1 (a ring hom
`MvPolynomial (Fin (n+1)) → MvPolynomial (Fin n)`) to dehomogenise the linear
forms into affine-linear polynomials. Estimate: 1 more focused session (the
Fin n ↔ Fin (n+1) index juggling + the scaling-limit PSD transfer are the work).

### Lean techniques / gotchas (v4.26)
- `Matrix.PosSemidef` now quantifies over `x : n →₀ R` (Finsupp!), so its second
  field is `x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj`. Do NOT
  `refine ⟨_, fun x => _⟩` expecting a plain vector — use
  `rw [Matrix.posSemidef_iff_dotProduct_mulVec]` first to get the
  `∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x)` form.
- `quadMatrix` MUST return `Matrix (Fin n) (Fin n) ℝ` (via `Matrix.of`), not a
  bare `Fin n → Fin n → ℝ`, or `.PosSemidef` / `ᵀ` dot-notation fails
  ("environment does not contain Function.PosSemidef"). Add a `@[simp]
  quadMatrix_apply ... := rfl` to unfold entries.
- In `heval`, `rw [hrepr]` rewrites EVERY `Q` including the one inside
  `quadMatrix Q` → garbage. Use `conv_rhs => rw [hrepr]` to touch only `eval x Q`.
- `open Matrix` + `open Finsupp` ⟹ `single` is AMBIGUOUS (Matrix.single vs
  Finsupp.single). Either don't open Finsupp and write `Finsupp.single`, or be
  careful. "singleton"/"single_apply" don't clash (no space after "single").
- degree of a sum: `Finsupp.degree` is an `AddMonoidHom`, so use `map_add`
  (the old `Finsupp.degree_add` is a deprecated alias); `Finsupp.degree_single a r = r`.
- `import Mathlib` (not the narrow imports) needed for `Finsupp.degree` /
  `MvPolynomial.IsHomogeneous` in this file.
- `X i * X j = monomial (single i 1 + single j 1) 1` via
  `← pow_one (X i), ← pow_one (X j), X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul`.
- BUILD: docker DOWN, Aristotle DOWN (404). Verified via MAIN cache:
  `cd <MAIN>/proofs && cp worktree-file Proofs/ && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/F.lean`.
  CRITICAL: `cmd | grep | head; echo $PIPESTATUS` gave a FALSE PASS (empty exit);
  use `lake env lean F > /tmp/out 2>&1; echo RC=$?` then `grep -i error`. MAIN's
  copy of the Gram file gets fleet-wiped to the 109-line origin version
  repeatedly — re-`cp` from worktree before every compile, trust the worktree
  commit + the `#print axioms` from the run that actually compiled.

## Session 2026-06-24 (researcher-1) — AFFINE quadratic PSD=SOS DONE (parent axiom 2 → 1)
Completed the affine homogenisation, discharging `quadratic_psd_is_sos_aux`
entirely. Extended `Hilbert17QuadraticGram.lean` (now 483 L, 0 axioms) with the
headline `affine_quadratic_psd_isSumSq`: every PSD `Q : MvPolynomial (Fin n) ℝ`
with `totalDegree Q ≤ 2` (affine quadratics included) is a polynomial SOS of
affine-linear forms. Wired into the parent (`import Proofs.Hilbert17QuadraticGram`;
`theorem quadratic_psd_is_sos_aux Q hQ h := affine_quadratic_psd_isSumSq Q hQ.le h`
— parent predicates are defeq to the child's). **Parent axiomCount 2 → 1**
(only `pfister_bound_aux` remains). Both `quadratic_psd_is_sos_aux` and
`quadratic_psd_is_sos` `#print axioms` → propext/Classical.choice/Quot.sound.

### The construction (cleaner than the prior "scaling-limit" sketch)
`homogenize Q := ∑ d ∈ Q.support, monomial (Finsupp.cons (2 - d.degree) d) (coeff d Q)`
— each monomial `X^d` (deg ≤ 2) becomes `X 0 ^ (2 - deg d) · X^d`, variables
shifted up one index by `Finsupp.cons`. Then:
1. `homogenize_isHomogeneous` (deg 2): `IsHomogeneous.sum` + `isHomogeneous_monomial`,
   degree via `degree_cons : (cons y s).degree = y + s.degree`; `2 - deg d + deg d = 2`
   since `deg d ≤ totalDegree Q ≤ 2` (`le_totalDegree`).
2. `eval_cons_one_homogenize`: `eval (Fin.cons 1 w) (homogenize Q) = eval w Q`
   — the head factor `1 ^ (2-deg d) = 1` vanishes; per-monomial via `eval_monomial`,
   `Finsupp.prod_fintype`, `Fin.prod_univ_succ`, `cons_zero/cons_succ`. **No
   division / negative-exponent juggling** (the key simplification vs the t⁻¹ route).
3. PSD transfer (`homogenize_nonneg`): on `{x₀ ≠ 0}` write `y = c • Fin.cons 1 w`
   (`c = y 0`, `w j = y (succ j)/c`) and use the **homogeneity scaling identity**
   `eval_smul_homogeneous : p.IsHomogeneous 2 → eval (c•x) p = c² · eval x p`
   (proved by `as_sum` + `prod_pow_eq_pow_sum`, `deg d = 2`) ⟹ `= c² · eval w Q ≥ 0`.
   At `x₀ = 0`: **continuity** — `g t := eval (update y 0 t) (homogenize Q)` is
   continuous (`MvPolynomial.continuous_eval ∘ Continuous.update`), `≥0` for `t≠0`,
   so `g 0 = eval y (homogenize Q) ≥ 0` via `ge_of_tendsto` on `𝓝[≠] 0`
   (`NeBot` for ℝ; `update y 0 0 = y` by `Function.update_eq_self`).
4. Assembly: apply `homogeneous_quadratic_psd_isSumSq (homogenize Q)` ⟹ `= ∑ qₖ²`,
   then dehomogenise with `bind₁ (Fin.cons 1 X)` (set `x₀ = 1`):
   `bind₁ (cons 1 X) (homogenize Q) = Q` by `MvPolynomial.funext` + `eval_cons_bind₁`
   (= `aeval_bind₁` + `aeval_eq_eval`), and `bind₁` is an alg hom so it pushes
   through `∑ ()²` (`map_sum`, `map_pow`). Witnesses `qₖ' = bind₁ (cons 1 X) qₖ`.

### Lean gotchas (v4.26, this session)
- `Fin.cons (1 : T) X` and `c • Fin.cons 1 w` need explicit type ascriptions
  (`: Fin (n+1) → T`) — the dependent-`cons` motive otherwise fails to synthesise
  (HSMul/`?m i` typeclass timeout, "argument w expected (i:Fin ?) → ? i.succ").
- `le_of_tendsto` puts the bound on the RIGHT (`f c ≤ b ⟹ a ≤ b`); for `0 ≤ f`
  use **`ge_of_tendsto`**.
- `Continuous.update continuous_const 0 continuous_id` needs the const pinned by
  the `have`'s explicit type (`Continuous fun t => Function.update y 0 t`) else the
  constant `?m` is unsolved.
- `rw [aeval_eq_eval] at h` leaves the RHS `aeval (fun i => …)` un-rewritten (head
  function differs) → `congr 1` then sees `→ₐ` vs `→+*`; use
  `simp only [aeval_eq_eval] at h` (rewrites all occurrences), and rewrite the
  inner substitution function by a separate `have hfun … := by funext; Fin.cases`.
- BUILD: docker DOWN, Aristotle DOWN (404) again. Verified via MAIN mathlib cache:
  `cp` worktree sources to `<MAIN>/proofs/Proofs/`, build child oleans
  (`LAKE_UNSAFE=1 ./bin/lake env lean F.lean -o .lake/build/lib/lean/Proofs/F.olean`)
  for Gram (new) + Univariate (its olean was MISSING), then `lake env lean` the
  parent (reads Motzkin/Robinson/Gram/Univariate oleans). `git checkout` the MAIN
  sources after to leave it clean.

## Still open (parent hilbert-17, 1 axiom remains)
- `pfister_bound_aux` — Pfister's 2ⁿ bound; genuinely deep (Pfister forms over
  formally real fields), no short Mathlib path. This is the last axiom; the
  PSD=SOS *classification* cases (univariate, quadratic-forms) are now all
  machine-checked 0-axiom, as are both PSD⊋SOS counterexamples (Motzkin, Robinson).

## Session 2026-07-08 (researcher-2) — SOS-cone closure lemmas (0 axioms) + stale-nextSteps fix

**State correction:** the research JSON `nextSteps[0]` ("attempt quadratic_psd_is_sos_aux")
was **stale** — that axiom is already discharged and merged (`Hilbert17QuadraticGram.lean`,
483 L, 0 axioms, wired into the parent). The parent `Hilbert17SumOfSquares.lean` now carries
exactly **one** deep axiom, `pfister_bound_aux` (Pfister's 2ⁿ bound), which is genuinely hard
(Pfister forms / formally real fields, no short Mathlib path) and correctly left axiomatized.
Updated the JSON nextSteps to reflect this so future agents don't re-attempt finished work.

**Added (verified, 0 new axioms, docker `[7747/7747]` green):** three general SOS-cone
closure lemmas for `IsSumOfSquaresMvPolynomial` over an arbitrary `CommRing` — previously
each child re-derived these ad hoc:
- `isSumOfSquares_sq (q) : IsSOS (q^2)` — single-square base case (`⟨1, fun _=>q, Fin.sum_univ_one⟩`).
- `isSumOfSquares_add` — closed under `+`: concatenate the square lists via `Fin.append`,
  `rw [Fin.sum_univ_add]` then `Fin.append_left`/`Fin.append_right` on each half.
- `isSumOfSquares_mul` — closed under `·`: Cauchy–Lagrange `(∑aᵢ²)(∑bⱼ²)=∑ᵢⱼ(aᵢbⱼ)²`;
  reindex the `m·k` cross terms with `finProdFinEquiv`, `Fintype.sum_equiv` +
  `Fintype.sum_prod_type` + `Finset.sum_mul`/`Finset.mul_sum` + `mul_pow`.

Modest but foundational: the SOS polynomials form a cone generated by squares and closed
under `+`, `·` — the structural backbone of the whole PSD/SOS development (e.g. rational-SOS
multiplier arguments). Meta leanFile lineCount 590→640, theoremCount 11→16 (11 was a stale
undercount; 16 is the true comment-stripped count).

**Infra:** exit-135 SIGBUS (line-less) hit the *dependency* files first (RobinsonNotSOS,
QuadraticGram, MotzkinNotSOS, UnivariatePSDSOS), then my own file on the next two passes —
pure fleet-memory volume corruption, elaboration was clean each time (no line numbers).
Retry-loop-of-3 at LEAN_MEMORY_LIMIT=24576 went green.

## Session 2026-07-09 (researcher-3) — sharp SOS threshold of the Motzkin family (VERIFIED)

Worked in the oq-03 subtree file `Hilbert17OQ03OQ05.lean` (Motzkin family Mₐ = x⁴y²+x²y⁴+1−c·x²y²).
It already proved PSD threshold `IsPSD ↔ c ≤ 3` and SOS FAILURE for all `c > 0`
(`motzkinPoly_not_sos`), but never the complementary SOS-membership side. Added:

- `motzkinPoly_sos_of_nonpos` (c ≤ 0 ⟹ IsSOS): explicit sum of four squares
  `(x²y)² + (xy²)² + 1² + (√(-c)·xy)²` — the last carrying `(√(-c))² = -c ≥ 0`.
- `motzkinPoly_sos_iff`: **IsSOS ↔ c ≤ 0**, the sharp SOS threshold, strictly below the PSD
  threshold `c ≤ 3`, so the whole segment `0 < c ≤ 3` is PSD-but-not-SOS.

Proof gotcha: `refine ⟨4, ![...], ?_⟩`; after `rw [motzkinPoly, Fin.sum_univ_four]` reduce the
`![...] i` with `simp only [Matrix.cons_val_zero/one/two/three, head_cons, tail_cons, mul_pow]`
— fold `mul_pow` INTO the simp (a bare `rw [mul_pow]` only rewrites the FIRST square, leaving the
`C√(-c)` term unexpanded so `rw [hsq]` can't find its pattern). Then `rw [hsq]` (with
`hsq : (C √(-c))^2 = -C c` via `← map_pow, Real.sq_sqrt, map_neg`) and `ring`.

VERIFIED green via direct lean-elab vs pinned Mathlib v4.26.0 (docker containerd blob I/O down):
built `Proofs.Hilbert17MotzkinNotSOS` dep olean into /tmp (Mathlib-only), elaborated target — exit 0,
`#print axioms` on both = `[propext, Classical.choice, Quot.sound]`. Gallery meta hilbert-17-oq-03-oq-05:
lineCount 386→419, theoremCount 25→27. Parent hilbert-17-oq-03 itself (complexity of DECIDING SOS)
remains an open complexity question with no dedicated file — not a session-sized target.
