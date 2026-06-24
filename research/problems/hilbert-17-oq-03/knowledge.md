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

## Still open
- Non-SOS direction (`motzkin_not_sos`, `robinson_not_sos`) — homogeneous-form
  degree analysis; would remove 2 more axioms.
- The actual complexity classification (SOS membership ≈ SDP feasibility) — a
  meta/complexity statement; unclear how to formalize meaningfully in Lean.
