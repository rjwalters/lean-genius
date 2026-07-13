# Knowledge Base: pascals-hexagon-oq-03-incomplete-01 (OQ-03-OQ-02)

Pascal-line map well-definedness for the Hexagrammum Mysticum.

## Status: COMPLETED (verified, merged)

The titled deliverable — well-definedness of the Pascal-line map
`HexagonLabeling = Sym(6)/D₆ → ProjLine` — is machine-checked and merged:

- `pascalLine_sameProjLine_rep` (#30806): the total `pascalLine` (via canonical
  representative `lbl.out`) agrees, as a *projective* line (`sameProjLine`), with
  the Pascal line from **any** representative `π` of `lbl`, under the
  general-position hypothesis `hnd`. This is the genuine OQ-03-OQ-02 content.
- `pascalProjLine_sameProjLine_of_quotient_eq` (#30806): two permutations in one
  coset relabel `hex` to the same projective Pascal line.
- Generator action (PART 4c): `hexRot:(P,Q,R)↦(Q,R,−P)`, `hexRev:(P,Q,R)↦(−Q,−P,R)`,
  exact vector identities; `sameProjLine` PER + `Subgroup.closure_induction` descent.
- Non-degeneracy meaning (PART 4j, #30840): `pascalProjLine_eq_zero_iff` (cross
  product = 0 iff all three 2×2 minors of `P,Q` vanish) and
  `pascalProjLine_ne_zero_of_minor` (one nonzero minor ⟹ genuine line).
- Incidence (PART 4k, #30863): `pointOnLine_pascalProjLine_iff_collinear` — the
  Pascal line is exactly the locus of points collinear with `P` and `Q`.

`#print axioms pascalLine_sameProjLine_rep`: only `conic_implies_pascal_constraint`
(the file's foundational Pascal axiom) + `propext/Classical.choice/Quot.sound`.
No `native_decide`.

## Out of scope (genuinely open)

- `steiner_count_eq_20` (OQ-03-OQ-03) and `kirkman_count_eq_60` (OQ-03-OQ-04):
  Conway–Ryba concurrence combinatorics. These are the file's two remaining
  `sorry`s and belong to **sibling** count slugs, not this well-definedness slug.
- Discharging `hnd` from a named general-position predicate on `hex`. The result
  is false without general position, so `hnd` is correctly an explicit hypothesis.

## Honesty note

Marked completed by researcher-1 (2026-06-28) after the JSON metadata had been
corrupted to phase NEW / empty fields (the work survived only in the `knowledge`
object). The deliverable is conditional on the explicit general-position
hypothesis — the honest formulation — and verified/merged across #30806–#30863.
