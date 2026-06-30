# erdos-816-oq-01: Remove the n ≥ 600 restriction from Chen–Ma's stronger result

**Parent**: Erdős Problem #816 (Equal-Degree Vertices and Paths of Length 3),
solved YES by Chen–Ma (2025), arXiv:2503.19569. Gallery: `src/data/proofs/erdos-816`,
Lean: `proofs/Proofs/Erdos816Problem.lean`.

## Background

For a simple graph `G`, say `G` has an **equal-degree P3 pair** if there exist two
distinct vertices `u, v` with `deg(u) = deg(v)` joined by a **path of length 3**
(four distinct vertices `u-a-b-v`, three edges).

- **Erdős #816 (main):** every `G` on `2n+1` vertices with `n²+n+1` edges has an
  equal-degree P3 pair. (YES, Chen–Ma 2025.)
- **Threshold tightness:** the complete bipartite `K_{n,n+1}` has exactly `n²+n`
  edges and has **no** equal-degree P3 pair (equal-degree vertices share a part;
  P3 has odd length so connects the two parts, i.e. different degrees).
- **Chen–Ma stronger result:** for **n ≥ 600**, every `G` on `2n+1` vertices with
  **≥ n²+n** edges has an equal-degree P3 pair, with `K_{n,n+1}` the **unique**
  exception.

## The open question

Can the `n ≥ 600` restriction be **lowered or removed**? I.e. for which `n` is it
true that every `G` on `2n+1` vertices with `≥ n²+n` edges other than `K_{n,n+1}`
has an equal-degree P3 pair? Chen–Ma's `600` is widely expected to be an artifact of
their stability/counting method rather than the true threshold.

## Formalization correspondence

`Erdos816Problem.lean` axiomatizes only the `n²+n+1` form (`erdos_816_full`, all `n`).
The stronger `≥ n²+n` form is captured by the *predicate* `satisfiesWeakerEH816` but is
**not** stated as an axiom/theorem. A Lean resolution of this OQ would state, for the
lowest provable threshold `n₀`,
`∀ n ≥ n₀, satisfiesWeakerEH816 G n ∧ ¬isCompleteBipartite G n → hasEqualDegreePath3Pair G`,
which forces handling the finitely many small-`n` base cases explicitly.
