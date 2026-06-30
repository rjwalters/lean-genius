# Knowledge: geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01-oq-03-oq-02

## Summary

Closed form for the fourth column ⟨n,3⟩ of the Eulerian triangle:

`6·⟨n,3⟩ = 6·4ⁿ − 6·(n+1)·3ⁿ + 3·n·(n+1)·2ⁿ − (n−1)·n·(n+1)`   (OEIS A000498)

equivalently `⟨n,3⟩ = 4ⁿ − (n+1)·3ⁿ + C(n+1,2)·2ⁿ − C(n+1,3)`.

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ03OQ02.lean`, namespace
`GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ03OQ02`, 0 axioms / 0 sorries:

- `eulerian_col_three` — the closed form above.

## Proof

Induction on n. Base n=0: `norm_num [eulerian]`. Step: the Eulerian recurrence
`⟨n+1,3⟩ = 4·⟨n,3⟩ + (n−2)·⟨n,2⟩` holds by `rfl` (definitional unfolding at k=2).
Multiply by 6, substitute the IH and the parent's `eulerian_col_two`
(`2·⟨n,2⟩ = …`), close with `push_cast [pow_succ]; ring`.

Truncated subtraction: `(n−2 : ℕ)` is reconciled with `(n−2 : ℤ)` by
`rcases n with _ | _ | m`. For n=0,1 the factor is 0 in ℕ; the column-two value
`2·⟨n,2⟩` is also 0 there, so the term vanishes either way (`norm_num`). For
n=m+2, `((m+1+1-2 : ℕ):ℤ) = m` (`simp`), then `push_cast; ring`.

## Lineage / dependencies

- `eulerian` (ℕ→ℕ→ℕ) defined in level-4 `GeometricSeriesOQ07OQ01OQ01OQ01`.
- `eulerian_col_one`, `eulerian_col_two` in level-5
  `GeometricSeriesOQ07OQ01OQ01OQ01OQ01` (both 0-axiom; olean in store).
- The slug's nominal parent `...OQ01OQ01OQ01OQ01OQ03` does not exist (chain gap);
  imported the level-5 ancestor directly.

## Verification checks

⟨3,3⟩=0: 6·64−6·4·27+3·3·4·8−2·3·4 = 384−648+288−24 = 0.
⟨4,3⟩=1: 6·256−6·5·81+3·4·5·16−3·4·5 = 1536−2430+960−60 = 6 = 6·1.
⟨5,3⟩=26: 6·1024−6·6·243+3·5·6·32−4·5·6 = 6144−8748+2880−120 = 156 = 6·26.

## Approaches Tried

- Direct induction with the definitional recurrence — worked first try once the
  defining namespace of `eulerian` (level 4) was added to `open`.
