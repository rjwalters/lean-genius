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
