# Problem: Completing the Wantzel-Galois Constructibility Proof — OQ extension (01)

## Statement

### Plain Language

The parent slug `angle-trisection-oq-02-oq-01-oq-02-incomplete-01`
(file `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`,
639 LOC, **0 sorries, 0 axioms**) closes all three classical
straightedge-and-compass impossibility results
(`angle_trisection_impossible_degree`,
 `doubling_cube_impossible_degree`,
 `regular_7gon_construction_impossible`) via the degree-not-power-of-two
route. It also proves several pieces of supporting Galois infrastructure
along the way:

- `isConstructible_algebraic_degree`: constructible α has
  `Module.finrank ℚ ℚ⟮α⟯` dividing a power of 2;
- `isConstructible_map`: ℚ-algebra endomorphisms of ℂ preserve
  `IsConstructible`;
- `isConstructible_minpoly_pow2`: constructible α has minpoly degree
  equal to a power of 2;
- `isConstructible_irred_degree_pow2`: any irreducible polynomial with a
  constructible root has natDegree a power of 2.

**What is *not* proved in the parent**: the full Wantzel-Galois
characterization

> `wantzel_galois_iff`: α ∈ ℂ is constructible ⇔ the Galois group of
> the splitting field of `minpoly ℚ α` is a 2-group.

The parent's docstring lists this as out-of-scope (~500 LOC of additional
Galois theory). All three impossibility results are dispatched by the
weaker degree-of-minimal-polynomial criterion alone, so
`wantzel_galois_iff` is genuinely extra.

This **OQ extension (01)** asks whether `wantzel_galois_iff` can be
proved (one direction or both) using the infrastructure already built
in the parent file plus the standard Mathlib Galois library. The
direction split:

- **Forward (⇒)** "α constructible ⇒ Gal(splitting field of minpoly_ℚ α) is a 2-group":
  the parent's `isConstructible_map` already gives Galois-invariance.
  A natural plan (sketched in Session 36 of the parent knowledge.md):
  use `isConstructible_map` + `IsAlgClosed.lift` to show all roots of
  `minpoly ℚ α` are constructible, then apply `isConstructible_minpoly_pow2`
  to bound the splitting-field degree.
- **Reverse (⇐)** "Gal is a 2-group ⇒ α constructible": needs FTGT +
  Sylow-style composition series + characterization of degree-2
  extensions as adjunctions of square roots.

### Formal Statement

The intended target lemma, stated in the parent's notation:

```lean
theorem wantzel_galois_iff (α : ℂ) :
    IsConstructible α ↔
      ∃ (n : ℕ), Fintype.card
        ((minpoly ℚ α).SplittingField ≃ₐ[ℚ] (minpoly ℚ α).SplittingField)
        = 2 ^ n
```

with `IsConstructible` defined inductively in the parent
(`AngleTrisectionOQ02OQ01OQ02Incomplete01.lean:81-86`) by rationals +
`sqrt_ext`.

For this OQ-01 extension the realistic scope is the **forward
direction** alone:

```lean
theorem isConstructible_galois_two_group {α : ℂ} (h : IsConstructible α) :
    ∃ n, Fintype.card ((minpoly ℚ α).SplittingField ≃ₐ[ℚ]
                       (minpoly ℚ α).SplittingField) = 2 ^ n
```

(Exact statement subject to S2 PREP audit — for instance, the Galois
group `Gal(K/ℚ)` for `K = splitting field of minpoly` may need to be
expressed via `IntermediateField.normalClosure` rather than the abstract
`SplittingField` constructor, depending on Mathlib API ergonomics.)

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - extension
  - gallery-extracted
  - galois-theory
  - constructibility
  - direction-split-candidate
```

**Significance**: 6/10 — closes a classical theorem ledger entry that
the parent file marks as out-of-scope. Not a research-frontier problem,
but a meaningful gallery-completion deliverable.

**Tractability**: 5/10 — the ⇒ direction has a documented ~200 LOC
plan (parent Session 36), the ⇐ direction is ~300 LOC and needs FTGT
composition-series infrastructure. ⇒ alone is moderately tractable; the
full ↔ is at the upper end of single-research-cycle reach.

## Why This Matters

1. **Gallery completion**: The parent file proves all three classical
   impossibilities but leaves the abstract characterization
   (`wantzel_galois_iff`) unstated. Stating + proving the ⇒ direction
   closes the most prominent open thread in the parent's docstring.
2. **Galois-theory infrastructure**: A proof of even the ⇒ direction
   will exercise `isConstructible_map`, `IsAlgClosed.lift`, and the
   `Gal(K/F)` cardinality machinery in the same file. This is reusable
   infrastructure for downstream impossibility proofs (regular 9-gon,
   etc.).
3. **Bridge to OQ-02 sibling problems**: Several sibling slugs
   (`angle-trisection-oq-02-oq-04-oq-01`,
    `angle-trisection-cos-20-gal-oq-01-*`) already use a
   `QuadraticTower` formulation that is essentially the explicit form
   of the ⇒ direction. Proving the abstract version here would
   consolidate the framework.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` | **Parent**. Contains `IsConstructible`, `isConstructible_map`, `isConstructible_minpoly_pow2`, `isConstructible_irred_degree_pow2`. 639 LOC, 0 sorries. |
| `angle-trisection-oq-02-oq-04-oq-01` | Sibling: explicit `QuadraticTower` formulation of constructibility. Useful template for the ⇐ direction's "tower of √-adjoins → constructible" lemma. |
| `angle-trisection-cos-20-gal-oq-01-*` | Sibling family: Galois-group calculations for cos 20° irrationality. Sets precedent for explicit `SplittingField`/`Gal` cardinality reasoning. |
| `angle-trisection-oq-02-oq-01-oq-02` | Grandparent: original 5-sorries variant; `Incomplete01` reduced this to 0 sorries. |
