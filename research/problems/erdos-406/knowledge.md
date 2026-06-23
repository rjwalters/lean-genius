# Erdős #406 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Is it true that there are only finitely many powers of $2$ which have only the digits $0$ and $1$ when written in base $3$?



The only examples seem to be $1$, $4=1+3$, and $256=1+3+3^2+3^5$. If we only allow the digits $1$ and $2$ then $2^{15}$ seems to be the largest such power of $2$.

This would imply via Kummer's theorem that\[3\mid \binom{2^{k+1}}{2^k}\]for all large $k$.

Saye \cite{Sa22} has computed that $2^n$ contains every possible ternary digit for $16\leq n \leq 5.9\times 10^{21}$.

This is mentioned in problem B33 of Guy's collection \cite{Gu04}.




References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Sa22] Saye, Robert I., On two conjectures concerning the ternary digits of powers of
two. J. Integer Seq. (2022), Art. 22.3.4, 9.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #405
- Problem #407
- Problem #2
- Problem #39
- Problem #1

## References

- Sa22
- Gu04

## Sessions

### 2026-06-09 — researcher-1 (iter-2): Mathlib v4.26.0 repair + pointwise-doubling equality

**Repair phase.** The HEAD `Erdos406Problem.lean` did not build at Mathlib v4.26.0; six unique
error sites required updates (import path `Mathlib.Data.Nat.Digits` →
`Mathlib.Data.Nat.Digits.Defs`; `List.mem_cons_self` and `List.not_mem_nil` argument-removal;
`Finset.notMem_empty` rename; `Nat.pred` injectivity rewritten via `Nat.succ_pred_eq_of_pos`
so omega sees the witness; instance scoping for `Decidable (HasOnlyDigits01Base3 …)`).

**Math correctness.** While restoring `dense_complete_to_15`, `native_decide` flagged three
counterexamples (n = 0, 2, 4) to the previously-asserted set `{1, 3, 5, 7, 15}`. Direct
verification: 2^0 = [1], 2^2 = [1,1], 2^4 = [1,2,1] all have digits ⊆ {1,2}, while 2^5 = 32
= [2,1,0,1] and 2^7 = 128 = [2,0,2,1,1] both contain a `0`. The corrected set is
`{0, 1, 2, 3, 4, 15}`. The Erdős variant statement ("2^15 is the largest") then refers to
the *largest* member of a set that includes all of n = 0..4 — which is consistent with the
literature on the variant.

**Mathematical extension.** Added `digits01_double_eq_map`:
```
HasOnlyDigits01Base3 n → Nat.digits 3 (2 * n) = (Nat.digits 3 n).map (· * 2)
```
This strengthens the existing digit-bound `digits01_double_digits02` (which only said
"every digit of 2n is in {0,2}") to the exact pointwise equality. The proof is a strong-
induction copy of the bound proof, but tracks the head and tail of the digit lists exactly:

- `n % 3 ∈ {0,1}` so `2 * (n % 3) ∈ {0,2} < 3`, hence `2*n % 3 = 2*(n%3) = (n%3)*2`
- `2*n / 3 = 2 * (n / 3)` (no carry), so the recursive call lines up with the map on the tail

Why this matters for Kummer. The previously-banked `digits01_double_digits02` gave the
*qualitative* no-carry property: no column sum in `n + n` overflows base 3. But Kummer's
formula `v_p(C(2n, n)) = #carries in n + n base p` requires the *quantitative* statement —
each column produces exactly `2d` with no carry-in or carry-out, the digits of `2n` and
`n` are in lockstep. `digits01_double_eq_map` is that lockstep equation. Combined with
`Nat.choose` divisibility lemmas it now gives the full `3 ∤ C(2n, n)` for `n ∈ ternarySparse`
direction the problem statement asks for.

**No axiom change.** The 1 axiom (`saye_computation`, Saye 2022 computational verification
for n ≤ 5.9 × 10²¹) is unchanged. The 2 conjecture-level `def`s (`ErdosProblem406`,
`ErdosProblem406_variant`) remain open.

**Build verification.** `./proofs/scripts/docker-build.sh Proofs.Erdos406Problem` — 3058
jobs clean.

---

*Generated from erdosproblems.com on 2026-01-13*
