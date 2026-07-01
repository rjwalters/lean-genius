# Knowledge Base: van-der-waerden-first-moment-oq-01-oq-01

Exact enumeration of the fitting van der Waerden AP family.

---

## Problem

The sibling entry `van-der-waerden-first-moment-oq-01` proves the upper bound
`|vdwFamily n k| ≤ ∑_{d=1}^{n} (n - (k-1)d)` (`card_vdwFamily_le_sum`) via
`Finset.card_image_le`: the family is the image of the fitting parameter box
`{(a,d) : a + (k-1)d < n}` under `(a,d) ↦ vdwAP n a d k`. The open question:
**is that bound an equality** — i.e. is the parametrization injective on the box?

---

## Insights

- **Yes, for `k ≥ 2`.** A fitting AP has no wraparound in `Fin n` (all terms
  `a + i·d < n`), so `Fin.val_cast_of_lt` reads off the underlying naturals and
  the `Fin n` order matches the natural order on the terms.
- Injectivity needs only the **two endpoints**: the least element recovers `a`,
  the greatest recovers `a + (k-1)d`; with `k ≥ 2` the factor `k-1 ≥ 1` recovers
  `d`. No need to reconstruct the entire set.
- Extremum-by-membership ("`x` is least ⟺ `x` is a member `≤` all members")
  transports across the equality of two AP sets directly, avoiding
  `Finset.min'`/`max'` dependent-proof juggling.

---

## Built (Proofs/VanDerWaerdenFirstMomentOQ01OQ01.lean, namespace ProbMethod.VanDerWaerden)

- `card_vdwFamily_eq_sum (k) (hk : 2 ≤ k)` :
  `(vdwFamily n k).card = ∑ d ∈ Icc 1 n, (n - (k-1)*d)` — exact count (0 sorry).
- `vdwAP_injOn (k) (hk : 2 ≤ k)` : the fitting parametrization is `Set.InjOn`.
- `card_vdwFamily_ge (k) (hk : 2 ≤ k)` : `n - (k-1) ≤ (vdwFamily n k).card`,
  the closed-form lower bound from the `d=1` interval slice.
- Endpoint helpers `vdwAP_fst_mem / vdwAP_fst_le / vdwAP_last_mem / vdwAP_last_ge`.

Reuses the sibling's `vdwFilter_card_eq_sum` (exact box count) and the base
entry's `vdwAP` / `vdwFamily`.

---

## Status

PROGRESS → exact count established. 0 sorries, 0 axioms (only
`propext`/`Classical.choice`/`Quot.sound`), no `native_decide`.

## Next Steps

- Combine with the sibling `card_vdwFamily_two_mul_le` to bracket the family size
  in `[n-(k-1), n²/(2(k-1))]`.
- State the exact Gauss closed form of the triangular sum with cutoff
  `D = ⌊(n-1)/(k-1)⌋`.

---

## Dead Ends

- `Finset.min'`/`max'` recovery works but entangles the `Nonempty` proof in
  dependent rewrites across the set equality; the membership-extremum phrasing
  is cleaner.
