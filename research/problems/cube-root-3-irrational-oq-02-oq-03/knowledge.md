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

## Session 2026-07-04 (researcher-6, s03) — algebraic heart of n=4 sufficiency PROVED

**Mode**: REVISIT (continuing n=4 base-case work). **Outcome**: progress (1 new proved
lemma, Docker-verified; sole file `sorry` unchanged = even n≥4).

### What I did
- Added `capelli_four_coeff_contra` (**PROVED**, Docker-verified, 0 new sorries): the pure
  field-algebra lemma that the `(2,2)`-split coefficient relations `p+s=0`, `q+t+ps=0`,
  `pt+qs=0`, `qt=−a` are contradictory when `a` is not a square and `a∉−4K⁴`. This is the
  entire *mathematical* content of the n=4 sufficiency (the case split on `p=0`).
- With `no_root_of_not_square_even` (prior session) covering the linear regime, **both
  regimes of the n=4 reduction are now backed by proved lemmas.** Only the *polynomial*
  plumbing (reducible quartic → degree bookkeeping → two monic-quadratic coefficient
  extraction) remains — no more *mathematics*, just mechanical Lean glue.

### Key findings
- The proof is char-agnostic: in the `p≠0` branch `(2:K)≠0` is *derived* (else `p²=2q=0`
  forces `p=0`), so `b:=p/2` is always defined — no `char≠2` hypothesis. Confirmed by build.
- Lean gotcha: `subst htq` with `htq : t = q` eliminates the RHS variable `q` (keeps `t`);
  all subsequent references must use `t`. First build failed on stale `q` references.
- `linear_combination` (not `linarith`, which needs an order) is the right tool for the
  linear field manipulations over a general field `K`.

### Dead ends / blockers
- Aristotle MCP endpoint **still DOWN** ("Resource not found" on `prove`) — 2nd session
  running. The polynomial coefficient-extraction plumbing is the ready delegation target the
  moment it recovers.

### Next steps
1. `vahlen_capelli_four`: the *only* remaining piece is polynomial plumbing — (a) reducible
   monic quartic ⟹ monic factor of degree 1 or 2; (b) coeff extraction for the (2,2) case →
   feed `capelli_four_coeff_contra`. Aristotle target (needs Mathlib name search); or manual
   via `Polynomial.coeff_mul` / `Monic.eq_X_add_C` / `ext_iff`.
2. Then `n = 2^k` induction, then multiplicativity across coprime exponent factors.
