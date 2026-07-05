# Knowledge Base: cube-root-3-irrational-oq-02-oq-03

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

---

## Session 2026-07-04 (researcher-6) — root obstruction + n=4 reduction

**Mode**: REVISIT (continuing prior n=2 base-case work). **Outcome**: progress (1 new proved lemma, complete n=4 paper-reduction documented).

### What I did
- Added `no_root_of_not_square_even` (PROVED, general all even n): if `a` is not a square
  then `X^n − C a` has no root in `K`. Isolates the linear-factor obstruction in the
  *sufficiency* direction — any nontrivial factorisation of even `X^n − C a` is rootless.
- Worked out and documented the COMPLETE `n = 4` sufficiency reduction (base case of the
  2-power tower, first case where condition (2) is active in sufficiency).

### Key findings
- Mathlib gap is precise: `X_pow_sub_C_irreducible_iff_of_prime_pow` is restricted to
  ODD primes (`p ≠ 2`); `X_pow_sub_C_irreducible_iff_of_prime` covers `n = 2` (used for the
  base case already on main). Missing: the `p = 2` prime-power (`n = 2^k`) case AND
  multiplicativity across coprime exponent factors. So even `n = 6 = 2·3` is NOT covered.
- `n = 4` full reduction: reducible ⟹ linear factor (root ⟹ `a` square, killed by the new
  no-root lemma) OR two monic quadratics `(X²+pX+q)(X²−pX+t)`. Coeff-matching: `q+t=p²`,
  `p(t−q)=0`, `qt=−a`. `p=0` ⟹ `a=q²` (square); `p≠0` ⟹ `t=q`, `2q=p²`, `q²=−a`, and
  `b:=p/2` gives `a=−(4b⁴)`.
- **char-2 handles itself**: `p≠0` forces `(2:K)≠0` (else `p²=2q=0`), so no separate
  `char ≠ 2` hypothesis is required — `n=4` sufficiency holds over EVERY field.

### Dead ends / blockers
- Aristotle MCP endpoint DOWN this session ("Resource not found" on prove, both sync/async).
  The two-quadratic coefficient extraction for `n=4` (mechanical, known math) is the natural
  Aristotle delegation target once the endpoint recovers.

### Next steps
1. Prove `vahlen_capelli_four` (n=4 sufficiency) — mechanical two-quadratic extraction.
   Delegate to Aristotle when available; else formalize the `∃ monic g h` factor split.
2. Generalize to `n = 2^k` by induction (the `−4b⁴` obstruction is the inductive step).
3. Multiplicativity across coprime exponent factors (mirrors Mathlib's odd-case proof).
