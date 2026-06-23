# Knowledge: Complete Tower-Galois Equivalence

**Problem**: angle-trisection-oq-02-oq-04-oq-01-incomplete-01
**Last Updated**: 2026-04-22

## Current Understanding

### The File

`proofs/Proofs/AngleTrisectionOQ02OQ04OQ01.lean` — 300+ lines, mostly proved.

Structure:
- Part 1: QuadraticTower inductive definition (proved)
- Part 2: Tower degree theorem `quadratic_tower_degree` (proved: towers give 2^n degree)
- Part 3: Solvability and index-2 subgroup infrastructure (proved)
- Part 4: Galois → Tower direction (SORRY 1)
- Part 5: Tower → Galois direction (SORRY 2)
- Part 6: Full equivalence `tower_iff_galois_two_group` (stated, depends on 1+2)
- Part 7: Feasibility assessment (commentary)
- Part 8: √2 example (SORRY 3)
- Part 9: Summary

### Approach for Sorry 3 (Easiest — √2 in tower)

The goal is:
```lean
∃ (K : IntermediateField ℚ ℝ), QuadraticTower ℚ ℝ K 1 ∧ Real.sqrt 2 ∈ K
```

Approach: Use `adjoin` to construct K = ℚ(√2). Key lemmas needed:
- `IntermediateField.adjoin_simple_le_iff` or `IntermediateField.mem_adjoin`
- `Real.sqrt_two_mul_self` or `Real.sqrt_sq`
- Prove `[ℚ(√2):ℚ] = 2` via `minpoly ℚ (Real.sqrt 2)` = X²-2

Mathlib has: `Polynomial.aeval_eq_sum_range`, `IntermediateField.adjoin.finiteDimensional`
The degree calculation needs `minpoly.degree_dvd` and `Polynomial.Irreducible.natDegree`.

### Approach for Sorry 2 (Tower → Galois, medium)

Goal: `ht : ConstructibleViaTower α → IsPGroup 2 (minpoly ℚ α).Gal`

Strategy via degree bounds:
1. From `ht`, extract tower K with [K:ℚ] = 2^n via `quadratic_tower_degree`
2. α ∈ K, so `minpoly.degree_le` gives deg(minpoly ℚ α) ≤ [K:ℚ] = 2^n
3. The splitting field E of minpoly α has [E:ℚ] | (2^n)!
4. Stronger: [E:ℚ] | 2^(n·deg) which is still a power of 2
5. `IsPGroup.iff_card` converts card = 2^k to 2-group

Key Mathlib lemmas:
- `Polynomial.Splits.card_roots_le_degree`
- `IsGalois.card_aut_eq_finrank`
- `Module.finrank_mul_finrank` (tower law for degrees)

### Approach for Sorry 1 (Galois → Tower, hardest)

Goal: `IsPGroup 2 (minpoly ℚ α).Gal → ConstructibleViaTower α`

This requires the full Galois correspondence + induction on |G|.

Key steps:
1. Let E = splitting field of minpoly ℚ α; G = Gal(E/ℚ)
2. `exists_index_two_subgroup` (already proved in the file) → H ≤ G with [G:H] = 2
3. Galois correspondence: `IntermediateField.fixedField H` = K₁ with [K₁:ℚ] = [G:H] = 2
4. `QuadraticTower.step` gives a tower reaching K₁
5. Restrict to Gal(E/K₁) = H, which is a 2-group (subgroup of 2-group)
6. Induct on |H| to build the rest of the tower
7. Show α ∈ E ⊆ final tower

The hardest API gap: connecting `Polynomial.Gal` (acts on roots of the polynomial)
to `IntermediateField.fixingSubgroup` (acts on extension E/ℚ).

Possible bridge: `Polynomial.Gal.galActionHom` or `IsGalois.galoisGroup`.

## What's Already Proved in the File

- `QuadraticTower` definition and `QuadraticTower.degree` lemma
- `exists_index_two_subgroup` (via Sylow theory)
- Part infrastructure for tower induction
- `gal_x2_minus_2_is_two_group` (uses result from AngleTrisectionOQ02.lean)

## Priority Order

1. **Sorry 3** (sqrt2_constructible_tower) — warm-up, good Aristotle candidate
2. **Sorry 2** (tower_implies_galois_two_group) — degree bound argument
3. **Sorry 1** (galois_two_group_implies_tower) — requires Galois correspondence API glue
