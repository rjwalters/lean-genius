# S25 ACT — The equitable re-cut (merging half, combinatorial) (2026-07-24, researcher-1)

## Goal

Execute the residual recorded by S24: the purely combinatorial merging step of
AFKS re-equitization — pool the ≤ `|P|` deficient remainders of the S23
chop-refinement and re-cut their union into size-`m` chunks, bounding the
energy cost with S24's replace bound.

## What was proved

New file `SzemerediRegularityOQ04Recut.lean` (2 theorems, 0 axioms, 0 sorries):

- **`exists_equitable_recut`** (capstone): every pairwise-disjoint family `P`
  re-cuts into a pairwise-disjoint `R` on the same ground set with all pieces
  nonempty of size ≤ `m` and **at most ONE deficient piece globally**, with

      `partitionEnergy G P − 2·|P|·m/n ≤ partitionEnergy G R`.

  Construction: S23 `exists_chop_refinement` (lossless, ≤ `|P|` deficient) →
  `D := Q.filter (card < m)` → S22 `exists_chop_pieces` on `D.biUnion id`
  (≤ 1 deficient) → keep `Q \ D`. Key facts: pieces of `Q \ D` are exactly the
  non-deficient ones, so the assembled family's deficient filter is contained
  in `F`'s (≤ 1); kept pieces are disjoint from the pooled union
  (`Finset.disjoint_biUnion_right` + family disjointness); energy via
  `partitionEnergy_replace_ge_of_small` and `|D| ≤ |P|` (numerator
  monotonicity, same `div_le_div_of_le` shape as S24).
- **`exists_equitable_recut_unit`** (m = 1 sanity): all pieces exactly
  singletons, cost `2·|P|/n`.

## Status of the re-equitization program

- S23 refinement half: DONE (lossless).
- S24 merging analytic half: DONE (replace bound).
- **S25 merging combinatorial half: DONE (this session).**
- Residual: parameter bookkeeping only — choose `m` with `2·|P|·m/n` below the
  retained `ε⁴m²/n²`-scale gain and feed
  `exists_afksTwoLevel_of_maintained_oracle` (S26 target), noting the S22
  `n = a·m + b·(m+1)` equitability packaging also applies to the recut output.

## Verification

`./proofs/scripts/docker-build.sh Proofs.SzemerediRegularityOQ04Recut` — see
PR for result.
