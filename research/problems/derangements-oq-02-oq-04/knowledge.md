# Knowledge: derangements-oq-02-oq-04

## Summary

Closed forms for the top of the fixed-point distribution of permutations of
`Fin n`, extending the parent's extreme cases:

| k (fixed points) | S(n,k) = #{σ : exactly k fixed} |
|---|---|
| n | 1 (parent) |
| n−1 | 0 (parent) |
| n−2 | C(n,2)  (**this entry**, transpositions) |
| n−3 | 2·C(n,3) (**this entry**) |

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/DerangementsOQ02OQ04.lean`, namespace `DerangementsOQ02OQ04`,
0 ax / 0 sorry:

- `numDerangements_two : numDerangements 2 = 1` (decide)
- `numDerangements_three : numDerangements 3 = 2` (decide)
- `card_perms_n_minus_two_fixed {n} (2 ≤ n) : S(n,n−2) = n.choose 2`
- `card_perms_n_minus_three_fixed {n} (3 ≤ n) : S(n,n−3) = 2 * n.choose 3`

## Proof

Both specialise the parent `PartialDerangements.card_perms_with_kfixed (n k)
(hk : k ≤ n) : S(n,k) = n.choose k * numDerangements (n−k)`:
- rw at k=n−2 (resp. n−3); `n − (n−2) = 2` (resp. 3) by omega;
- rw the small derangement value (D(2)=1 / D(3)=2);
- `Nat.choose_symm hn : n.choose (n−k) = n.choose k` turns C(n,n−2)→C(n,2) etc.;
- `mul_one` / `Nat.mul_comm` finish.

## Lineage / dependencies

- Parent `Proofs.DerangementsOQ02`, namespace `PartialDerangements`, opens
  `Finset Fintype Nat Equiv.Perm`. `numDerangements` = `Nat.numDerangements`.
  Olean in store; source matches origin/main.
- `S(n,k)` is the filter-card `(univ.filter fun σ => (univ.filter fun x => σ x = x).card = k).card`.

## Approaches Tried

- Direct specialisation of the parent formula — worked first try; the only fiddle
  was using `Nat.choose_symm` to flip C(n,n−2) into C(n,2).
