# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 1
**Status**: in-progress

## Current Focus

Empty stub. Continued the partial-derangement table of the parent
(derangements-oq-02): closed forms for the next fixed-point codimensions
(researcher-9).

## Delivered (PR pending)

`proofs/Proofs/DerangementsOQ02OQ04.lean` — 4 theorems, 0 axioms, 0 sorries
(typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound):

- `card_perms_n_minus_two_fixed {n} (2 ≤ n) : S(n,n−2) = C(n,2)` — the
  transpositions (D(2)=1).
- `card_perms_n_minus_three_fixed {n} (3 ≤ n) : S(n,n−3) = 2·C(n,3)` (D(3)=2).
- `numDerangements_two` (D(2)=1), `numDerangements_three` (D(3)=2), by decide.

Specialises the parent's `PartialDerangements.card_perms_with_kfixed`
(S(n,k)=C(n,k)·D(n−k)) at k=n−2, n−3, using `Nat.choose_symm` and the small
derangement values.

## Notes

Parent already had the extremes S(n,n)=1 (`permsWithAllFixed_card_eq_one`) and
S(n,n−1)=0 (`permsWithNMinus1Fixed_eq_zero`); this fills codimensions 2 and 3.

## Next Action

Follow-up: S(n,n−4) = 9·C(n,4) (D(4)=9), or the expected number of fixed points
= 1 (∑_k k·S(n,k) = n!).
