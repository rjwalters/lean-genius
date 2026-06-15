# erdos-978-oq-01: Squarefree values of n⁴ + 2

**Parent gallery:** `erdos-978` (Erdős Problem #978 — Power-Free Values of Polynomials)
**Lean:** `proofs/Proofs/Erdos978Problem.lean` (`squarefree_conjecture_n4_plus_2`, line ~206)
**Status:** OPEN (genuine open conjecture, $\$$-prize-adjacent)

## Statement

Does `n⁴ + 2` represent infinitely many squarefree numbers? Formally:

> ∀ N, ∃ n > N, `IsSquarefree (n⁴ + 2)`.

This is the **k = 4 case** of Erdős #978. For an irreducible `f ∈ ℤ[x]` of degree `k > 2`:
- **(k−1)-power-free** values have positive density — **YES** (Hooley 1967). For `k = 4`
  this is the *cubefree* case, encoded as the axiom `n4_plus_2_cubefree`.
- **(k−2)-power-free** values infinitely often — **YES for k ≥ 9** (Heath-Brown 2006,
  Browning 2011); **OPEN for k < 9**. For `k = 4` the (k−2) = *squarefree* case is this OQ.

## Why it is hard

Proving `f(n)` squarefree infinitely often requires sieving out every prime square
`p² | f(n)`. The "small" primes (`p ≲ N^{1/2}`) are handled by standard sieves, but the
"large" primes (`p` up to `~N^{k/2} = N²` for `k = 4`) need a power-saving count of
`#{n ≤ N : p² | f(n)}` uniformly in `p` — exactly the input Heath-Brown/Browning obtain
only for `k ≥ 9`. No method currently reaches `k = 4` for the squarefree exponent.

## Formalization target

The full conjecture is **not** provable with current mathematics, so it cannot be a Lean
proof target. The realistically formalizable / checkable pieces are:
1. **No local obstruction**: no fixed square `m² > 1` divides `n⁴ + 2` for all `n`.
2. **Positive conjectural density**: `C = ∏_p (1 − ρ(p²)/p²) > 0`, where
   `ρ(p²) = #{n mod p² : p² | n⁴ + 2}`.
3. The bridge to the known cubefree result (`n4_plus_2_cubefree`).

See `verify_squarefree_density.py` for the build-free numerical certification of (1)–(2).
