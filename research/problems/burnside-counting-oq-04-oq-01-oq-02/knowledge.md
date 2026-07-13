# burnside-counting-oq-04-oq-01-oq-02 — Closed form for binary bracelet numbers via dihedral Burnside sum

## Result

`BurnsideCountingOQ04OQ01OQ02.lean` (namespace `BurnsideBraceletClosedForm`) writes down and
validates the classical closed form for the binary bracelet numbers `b(n) = A000029(n)`:

```
rotTerm n  = ∑_{i : ZMod n} 2 ^ gcd(n, i.val)            -- rotation fixed-point total
reflTerm n = if n odd then n · 2^((n+1)/2)               -- reflection fixed-point total
             else (n/2)·2^(n/2+1) + (n/2)·2^(n/2)
braceletClosed n = (rotTerm n + reflTerm n) / (2 n)      -- Burnside average over |D_n| = 2n
```

- `rotTerm_eq` : for all `n`, `rotTerm n = ∑_i |Fix(r i)|` (via the sibling's
  `card_rotFixed = 2^gcd(n, i.val)`) — computation-free.
- `braceletClosed_eq_orbitCount_{three,four,five,six}` : the formula equals the genuine
  `Fintype.card (orbitRel.Quotient (DihedralGroup n) (Coloring n))` for `n = 3,4,5,6`.
  `b(3)=4`, `b(4)=6` are freshly Burnside-computed here (kernel `decide` on the fixed-point
  sums `24`, `48`); `b(5)=8`, `b(6)=13` are imported from the grandparent.
- `bracelet_seven … bracelet_ten` : the formula predicts `b(7)=18, b(8)=30, b(9)=46, b(10)=78`
  by pure arithmetic, beyond the parents' length-6 `decide` ceiling.

Axiom-free: no `native_decide`; `#print axioms` reports only `propext, Classical.choice,
Quot.sound`.

## Lineage

- grandparent `burnside-counting-oq-04-oq-01-oq-01` — generic `DihedralGroup n` action on
  `Coloring n = ZMod n → Fin 2`, `bracelet_count_mul` (Burnside), `b(5)`, `b(6)`.
- sibling `burnside-counting-oq-04-oq-01-oq-01-oq-01` — rotation closed form
  `|Fix(r i)| = 2^gcd(n, i.val)`; this file reuses it for `rotTerm_eq`.

This entry answers the grandparent/sibling open question "replace per-`n` decide by a closed
form for `b(n)`".

## Next open question

Prove the reflection fixed-point count generically: for the reflection `sr i` (acting as
`x ↦ -i - x`), the number of fixed colourings is `2 ^ (orbits of that involution)`, i.e.
`2^((n+1)/2)` for odd `n`, and `2^(n/2+1)` or `2^(n/2)` for even `n` according to the parity of
`i` (whether `2x = -i` is solvable). That would prove `reflTerm n = ∑_i |Fix(sr i)|` and upgrade
`braceletClosed n = A000029(n)` to a theorem for ALL `n`. Route: Burnside on the order-2
subgroup `⟨sr i⟩ ≤ D_n` acting on `ZMod n`, giving `orbits = (n + |{x : 2x = -i}|)/2`, plus a
quotient-bijection `RefFixed n i ≃ (ZMod n / ⟨sr i⟩ → Fin 2)` analogous to `rotFixedEquiv`.
