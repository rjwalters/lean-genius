# Hurwitz (oq-03) — Universal Commutative-Ring Square Identities

**Status:** COMPLETED — shipped as gallery entry `hurwitz-theorem-oq-03-incomplete-01`
**Lean:** `proofs/Proofs/HurwitzUniversal.lean` (195 lines, 14 theorems/lemmas, 6 defs, 0 axioms, 0 sorries)
**Verification:** builds against pinned Mathlib v4.26; `#print axioms` on every result returns only `propext, Classical.choice, Quot.sound`.

## Result

The Hurwitz 1-, 2-, 4-, and 8-square identities are **universal** polynomial identities — they
hold over **every commutative ring**, not only over ℝ:

```
normSq a * normSq b = normSq (nMul a b)      for n ∈ {1, 2, 4, 8}, over any CommRing R
```

where `nMul` is the multiplication table of ℝ / ℂ / ℍ / 𝕆 and `normSq v = ∑ (v i)²`. Each is
closed by a single `ring` call (the n=8 Degen identity included), so no quaternion/octonion
library is used.

### Arithmetic corollary

`IsSumOfSquares n r := ∃ v : Fin n → R, normSq v = r` is multiplicatively closed for
n ∈ {1,2,4,8} in any commutative ring, and contains 0 and 1. Over ℤ this gives the elementary
multiplicative steps `int_sumTwoSq_mul` and `int_sumFourSq_mul` behind the two- and four-square
theorems; worked witnesses exhibit `15 = 3·5` as a sum of four squares via Euler's identity.

## Relation to parent

Strengthens `hurwitz-theorem-oq-03`, which proves the existence direction only over ℝ (n=4 from
Mathlib quaternions). This entry does **not** touch the parent's remaining `sorry`: the
impossibility of bilinear n-square identities for n ∉ {1,2,4,8}, which needs Clifford-algebra /
Bott-periodicity machinery.

## Next steps

- Impossibility direction (parent's open sorry).
- Bridge `IsSumOfSquares` to Mathlib's number-theoretic two-/four-square theorems.
- Pfister denominator identities for all 2-powers.
