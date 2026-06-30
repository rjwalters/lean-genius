# Knowledge Base: lagrange-four-squares-oq-01-oq-03

**OQ**: "What is the exact count of four-square representations of n, and can the
Jacobi four-square formula `r4(n) = 8·Σ_{d|n, 4∤d} d` be formalized?"
**Parent**: `lagrange-four-squares-oq-01` (computational complexity of four-square
representations; `Proofs/LagrangeFourSquaresOQ01.lean` — search bounds + greedy
algorithm, NOT a count).

---

## Problem Understanding (S1 ORIENT, researcher-6, 2026-06-15)

The exact count is **Jacobi's four-square theorem** (1834): for `n ≥ 1`,
```
r4(n) = 8 · Σ_{ d | n, 4 ∤ d } d
```
where `r4(n) := #{ (x₁,x₂,x₃,x₄) ∈ ℤ⁴ : x₁²+x₂²+x₃²+x₄² = n }` counts **ordered,
signed** quadruples (zeros allowed). Equivalent closed forms (all three checked
against the brute-force lattice count in `verify_jacobi_four_squares.py`, n=1..120):
- `n` odd:  `r4(n) = 8 · σ(n)`.
- `n` even: `r4(n) = 24 · σ(m)`, `m` = largest odd divisor of `n`.

**Convention is the formalization trap.** The `8·` (and `24·`) prefactor encodes
the sign/coordinate symmetries; `r4(1)=8`, `r4(2)=24`, `r4(3)=32`, `r4(4)=24`,
`r4(5)=48`, `r4(7)=64`. The `4∤d` exclusion is **load-bearing**: at `n=4` the naive
`8·σ(4)=56` is WRONG; the true value is `r4(4)=24` (drop `d=4`). The cert asserts
this explicitly so a future Lean statement can't silently use `8·σ`.

---

## Mathlib inventory (surveyed 2026-06-15 vs master + pin v4.26.0)

**The COUNT is a genuine Mathlib gap.** What exists is only *existence*:
- `Mathlib/NumberTheory/SumFourSquares.lean`: Lagrange's theorem
  `Nat.sum_four_squares` (every `n` IS a sum of four squares) + `euler_four_squares`
  (the 4-square multiplicativity identity). **No `r4`, no count, no Jacobi formula.**
- `Mathlib/NumberTheory/SumTwoSquares.lean`: Fermat's two-square theorem
  (`Nat.Prime.sq_add_sq`, the `n` characterization). **No `r2` count** either —
  the companion fact `r2(n) = 4·(d₁(n) − d₃(n))` is also absent.
- `Archive/ZagierTwoSquares.lean`: Zagier's one-sentence proof — existence only.

**All three classical proof routes are blocked by large gaps:**
1. **Modular forms** (θ⁴ ∈ M₂(Γ₀(4)), Eisenstein basis 1-dim ⇒ formula). Mathlib
   has *some* modular-forms machinery (≈14 Eisenstein hits) but not the weight-2
   level-4 theta identity. Research-grade; ≫1000 LOC.
2. **Hurwitz quaternions** (count Hurwitz integers of norm `n`; norm-multiplicativity
   + unique factorization + unit group of order 24). Mathlib has `Quaternion` but
   the Hurwitz/Lipschitz *order arithmetic* is essentially absent (1 search hit
   each, no developed order). ≫1000 LOC.
3. **Elementary / Lambert-series** (Liouville). Needs the `r2` count first (gap)
   plus a Liouville-style convolution identity. Still several hundred LOC of new
   number theory.

---

## Insight — the one elementary, formalizable reduction
`r4 = r2 ⋆ r2` (Cauchy convolution): `r4(n) = Σ_{k=0}^{n} r2(k)·r2(n−k)`. This is
pure rearrangement of the defining sum (split `(x₁,x₂)` from `(x₃,x₄)`), is
**elementary and Lean-formalizable**, and is exactly the identity the cert uses to
compute `r4`. It reduces the four-square count to the two-square count — but the
`r2` closed form is itself a Mathlib gap, so the reduction doesn't close the OQ on
its own.

## Recommended ACT (tractable increment, NOT the general theorem)
Mirror the parent OQ01's "verified for small cases" pattern and the konigsberg
Matrix-Tree base-case oracle (PR #24324): define `r4` as a **computable
`Finset.card`** over the bounded box `[-isqrt n, isqrt n]⁴` and prove
`r4 n = jacobiCount n` for explicit small `n` by `decide`/`native_decide`. This is
a real, buildable artifact (when Docker returns) that pins the convention and
serves as a regression oracle, without claiming the (Mathlib-blocked) general
proof. Honest verdict for the **general** theorem: **BLOCKED** (needs >1000 LOC of
new Mathlib — quaternion orders or weight-2 modular forms).

---

## Dead Ends
- `8·σ(n)` as the formula for all `n` — WRONG on even `n` (`n=4`: `56 ≠ 24`); the
  `4∤d` exclusion (equivalently the odd/even `8·σ` / `24·σ(odd part)` split) is
  mandatory.
- Searching Mathlib for "Jacobi" finds only `JacobiSymbol` (quadratic-residue
  symbol) — unrelated to the four-square *formula*.

## Links
- Parent: [[lagrange-four-squares-oq-01]] (four-square representation complexity).
- Same build-free survey + durable-cert + small-n-oracle vein as
  [[project-researcher-1-20260615-konigsberg-oq0401-matrixtree-basecases]] and
  [[project-researcher-6-20260615-abelruffini-galois-oq040-mapapi-gap]].
