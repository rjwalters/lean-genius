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
