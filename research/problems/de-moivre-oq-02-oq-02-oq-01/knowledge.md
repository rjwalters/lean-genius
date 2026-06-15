# de-moivre-oq-02-oq-02-oq-01: Chebyshev U·U Linearization

**Target**: Prove `U_m · U_n = ∑_{k=0}^{n} U_{m+n−2k}` as a polynomial identity over any
commutative ring `R[X]`, for `m : ℤ`, `n : ℕ`. This is the genuine product-to-sum
("linearization") formula for second-kind Chebyshev polynomials — the open question
explicitly posed by the parent T·U entry de-moivre-oq-02-oq-02.

## Summary

The parent only proved the *mixed* T·U cross-product and a U·U product-to-*difference*
scaled by `(1−x²)`. The bare product `U_m·U_n` had not been expressed purely in second-kind
terms. The classical answer is a full arithmetic-progression sum of indices from `|m−n|` to
`m+n` in steps of 2.

## Key idea

Isolate the combinatorics. Let `S(m,n) = ∑_{k=0}^{n} U_{m+n−2k}`.
- **`Ssum_rec`** (product-free): `2X·S(m,n+1) = S(m,n+2) + S(m,n)`. Distribute `2X` into the
  sum via `2X·U_k = U_{k+1}+U_{k−1}`, giving `∑_{k=0}^{n+1}(U_{m+n+2−2k}+U_{m+n−2k})`. Peel the
  boundary terms of the two telescoped ranges with `Finset.sum_range_succ`; both equal
  `U_{m−n−2}` and cancel.
- **`U_mul_U`**: two-step induction on `n` carrying `P(j) ∧ P(j+1)` (the U recurrence is
  second-order). Base `n=0,1`; step uses `U_{i+2}=2X·U_{i+1}−U_i` together with `Ssum_rec`,
  closed by `linear_combination`.

Verified numerically before formalizing: `U_2·U_2 = U_4+U_2+U_0 = 16x⁴−8x²+1` ✓;
`U_3·U_1 = U_4+U_2 = 16x⁴−8x²` ✓.

## Sessions

### Session 2026-06-15 (Session 1) — FRESH, ORIENT→ACT

**Mode**: FRESH
**Outcome**: progress (full proof written; build verification pending — Docker contended, Aristotle 404)

#### What I Did
- Claimed the problem; confirmed via parent meta.json that this exact linearization is the
  parent's stated open question (genuine gallery gap, not a duplicate).
- Derived the clean strategy: reduce the product identity to the product-free sum recurrence
  `Ssum_rec`, then two-step induction.
- Wrote `proofs/Proofs/DeMoivreOQ02OQ02OQ01.lean` (def `Ssum`; lemmas `two_X_U`,
  `Ssum_succ_expand`, `Ssum_rec`, `Ssum_zero`, `Ssum_one`; theorem `U_mul_U`).
- Created gallery data `src/data/proofs/de-moivre-oq-02-oq-02-oq-01/meta.json`.

#### Key Findings
- The U·U product, unlike T·T and T·U (two terms each), is a `min(m,n)+1`-term sum.
- The entire boundary bookkeeping can be quarantined in a product-free lemma (`Ssum_rec`),
  which keeps the induction step a one-line `linear_combination`.
- Indexing the summand by `m+n−2k` with `m : ℤ` avoids any `m ≥ n` hypothesis.

#### Files Modified
- `proofs/Proofs/DeMoivreOQ02OQ02OQ01.lean` (new, ~146 lines)
- `src/data/proofs/de-moivre-oq-02-oq-02-oq-01/meta.json` (new)

#### Next Steps
- Verify the build (`./proofs/scripts/docker-build.sh Proofs.DeMoivreOQ02OQ02OQ01`) once
  Docker contention clears; the only risk areas are Finset term-matching in `Ssum_rec`
  (range `(n+1)+1` vs `n+2`, cast normalization of `↑(n+1)`) — fix with explicit `show`
  rewrites / `push_cast` if the compiler flags them.
- If verified, flip meta status to verified/original and register in proof index.
