# Erdős #131 — General Direct-Sum Davenport Lower Bound `D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1`

**Slug:** `erdos-131-oq-01-oq-01-oq-01-oq-04-oq-03`
**Lean file:** `proofs/Proofs/Erdos131DavenportDirectSum.lean` (namespace `Erdos131DavenportDirectSum`)
**Status:** verified · 0 axioms · 0 sorries · 7 theorems · 3 definitions · 196 lines

## Summary

The **Davenport constant** `D(G)` of an additive group `G` is the least `d` such that
every length-`d` sequence over `G` has a nonempty zero-sum subsequence. The cyclic value
`D(ℤ/nℤ) = n` is elementary (companion `erdos-131-oq-01-oq-01-oq-01-oq-03`); the rank-2
**cyclic** lower bound `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1` (companion
`erdos-131-oq-01-oq-01-oq-01-oq-04`) is proved there by exhibiting one explicit extremal
sequence `(1,0)^{a−1}(0,1)^{b−1}`.

This entry proves the **structural principle** behind that witness, for **arbitrary**
additive groups:

> `davenport_directSum_lower : IsLeast (DavenportSet G₁) d₁ → IsLeast (DavenportSet G₂) d₂ → IsLeast (DavenportSet (G₁ × G₂)) d → d₁ + d₂ − 1 ≤ d`.

Iterating it over an invariant-factor decomposition (each factor cyclic) recovers the
Olson–Davenport lower bound `D(G) ≥ 1 + Σ(nᵢ − 1)`. The matching **upper** bound — Olson's
theorem, sharp only for rank ≤ 2 and `p`-groups — is the deep open piece and is *not*
formalized (Mathlib lacks it).

## The engine: concatenation principle

`concat_not_hasZeroSum`: if `f₁ : Fin m₁ → G₁` and `f₂ : Fin m₂ → G₂` are each
zero-sum-free, then `concatSeq f₁ f₂ : Fin (m₁ + m₂) → G₁ × G₂` is too, where
`concatSeq f₁ f₂ = Fin.addCases (fun i => (f₁ i, 0)) (fun j => (0, f₂ j))` places `f₁` in
the first coordinate over the first block and `f₂` in the second over the second.

Proof sketch:
1. A candidate zero-sum index set `s ⊆ Fin (m₁ + m₂)` is reindexed along
   `finSumFinEquiv : Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂)` to `t ⊆ Fin m₁ ⊕ Fin m₂`.
2. `Finset.toLeft_disjSum_toRight` + `Finset.sum_disjSum` split the total sum over `t`
   into a `t.toLeft` block and a `t.toRight` block; `finSumFinEquiv_apply_left/right` and
   `Fin.addCases_left/right` evaluate `concatSeq` on each block to `(f₁ j, 0)` resp.
   `(0, f₂ k)`.
3. `Prod.fst_sum` / `Prod.snd_sum` read the two coordinates: the first is
   `∑_{j ∈ t.toLeft} f₁ j`, the second `∑_{k ∈ t.toRight} f₂ k`. The pair being `0` forces
   both block sums to `0`.
4. Zero-sum-freeness of `f₁`, `f₂` makes each block empty; `Finset.disjSum_eq_empty` gives
   `t = ∅`, hence `s = ∅`, contradicting nonemptiness.

## Supporting infrastructure

- `DavenportSet G := {m | ∀ f : Fin m → G, HasZeroSumSubseq f}`, with `HasZeroSumSubseq`
  the nonempty-zero-sum-subsequence predicate (same as the companions, now over a generic
  additive group).
- `davenport_set_mono`: the Davenport set is upward closed (restrict via `Fin.castLE`,
  re-embed via `Fin.castLEEmb`).
- `zero_not_mem_davenportSet` / `one_le_of_isLeast_davenport`: length `0` is never a
  Davenport length, so the least Davenport length is positive — needed so that
  `D(Gᵢ) − 1` is a genuine zero-sum-free length.

## Main proof

`davenport_directSum_lower`: from `IsLeast` minimality, `D(G₁) − 1` and `D(G₂) − 1` are
below the least Davenport lengths, so each admits a zero-sum-free sequence `f₁`, `f₂`.
Their concatenation is zero-sum-free of length `(d₁ − 1) + (d₂ − 1) = d₁ + d₂ − 2`, so that
length is not a Davenport length. Were `d ≤ d₁ + d₂ − 2`, upward closure would make
`d₁ + d₂ − 2` a Davenport length — contradiction. Hence `d ≥ d₁ + d₂ − 1`.

Specializations: `davenport_rank2_lower_of_cyclic` (feed `D(ℤ/aℤ)=a`, `D(ℤ/bℤ)=b` → `a+b−1`)
and `davenport_directSum_diag_lower` (`D(G ⊕ G) ≥ 2·D(G) − 1`).

## Mathlib gaps filled

Mathlib has the Erdős–Ginzburg–Ziv constant `s(ℤ/nℤ) = 2n − 1` but **not** the Davenport
constant, zero-sum-free sequences, or the direct-sum concatenation principle. This entry
supplies the general-group concatenation infrastructure (`concatSeq`,
`concat_not_hasZeroSum`) axiom-free.

## Lean gotchas (v4.26.0)

- `finSumFinEquiv_apply_left/right` are simp lemmas; do **not** `set e := finSumFinEquiv`
  (the simp lemmas are stated for `finSumFinEquiv`, and `set` hides it). Write
  `finSumFinEquiv` literally.
- Reindex via `t := s.map finSumFinEquiv.symm.toEmbedding`, then prove
  `t.map finSumFinEquiv.toEmbedding = s` by `rw [Finset.map_map]; ext x; simp`
  (`Equiv.symm` then `Equiv` collapses to the identity embedding under `simp`).
- One `simp only [Equiv.coe_toEmbedding, finSumFinEquiv_apply_left,
  finSumFinEquiv_apply_right, concatSeq, Fin.addCases_left, Fin.addCases_right]` reduces both
  block summands to the `(f₁ j, 0)` / `(0, f₂ k)` form in one shot.
- Extract coordinates with `congrArg Prod.fst hsum` then `simpa [Prod.fst_sum]`.

## Next steps

- `oq-04-oq-03-oq-01`: lift the binary principle to an arbitrary indexed direct sum
  `⨁_{i : Fin k} Gᵢ` (Σ-type block bookkeeping).
- `oq-04-oq-03-oq-02`: characterize / exhibit groups where the bound is strict
  (rank ≥ 4 examples beyond Olson's equality range).
- The matching upper bound (Olson, `oq-04-oq-01`) remains the deep open piece.
