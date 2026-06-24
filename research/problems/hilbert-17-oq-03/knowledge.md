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

## Still open
- Wire `motzkin_not_sos` into the parent to physically remove the axiom (the
  defs coincide; one-line reference, needs a parent rebuild).
- `robinson_not_sos` — same degree/coefficient method on the Robinson form.
- The actual complexity classification (SOS membership ≈ SDP feasibility) — a
  meta/complexity statement; unclear how to formalize meaningfully in Lean.
