# S6b/c ACT — Lean refutations: octahedron and cube are NOT 2-flat magic

**Date**: 2026-07-24
**Researcher**: researcher-3
**Mode**: ACT (Lean realization of the S6b PREP refutations)
**Prior state**: S6a complete (PR #43107 — tetrahedron certificate, 0 sorries).
S6b/c designed doc-only in PR #18541 (2026-05-13), never Lean-realized.

## What shipped

Two new leaf files, both 0 axioms / 0 sorries, Docker-verified:

- `proofs/Proofs/Erdos735OQ04Octahedron.lean` —
  `octa_not_isKFlatMagic : ¬ IsKFlatMagic 2 octaConfig`
- `proofs/Proofs/Erdos735OQ04Cube.lean` —
  `cube_not_isKFlatMagic : ¬ IsKFlatMagic 2 cubeConfig`
  (imports the octahedron file and reuses its generic helpers)

With the S6a tetrahedron certificate this settles, in Lean, all three
polytopes named by the S1 OBSERVE "regular-polytope magic family" claim:
**only the tetrahedron is 2-flat magic**. The conjectured `k ≥ 2` family is
therefore strictly narrower than "regular polytopes", machine-checked.

## Proof architecture — 4-flat linear-arithmetic route

The S6b PREP proved the refutations via O_h symmetry averaging (order-48
group action, vertex transitivity). Formalizing that argument would need
group-action machinery over `WeightingD`. This session found a much lighter
route: for each polytope, FOUR explicit 2-flats already force a contradiction
with positivity, via `linarith`.

**Octahedron** (vertices ±eᵢ): flats z=0 ({v₁v₂v₃v₄}), y=0 ({v₁v₂v₅v₆}),
x+y+z=1 ({v₁v₃v₅}), x+y+z=−1 ({v₂v₄v₆}). Magic constant equations give
(z=0)+(y=0)−(face⁺)−(face⁻) = a₁+a₂ = 0, contradiction.

**Cube** (vertices {±1}³): flats x=1, x=−1 (4 vertices each), corner planes
x+y+z=1 ({q₂q₃q₅}), x+y+z=−1 ({q₄q₆q₇}). Same combination gives
a(1,1,1)+a(−1,−1,−1) = 0, contradiction.

## Reusable Lean recipe — hyperplane flats without affine independence

The S6a route (affine independence + rank bounds) is the wrong tool for
refutations, which need NEGATIVE membership decisions. Instead:

1. Build each flat as `AffineSubspace.mk' p (LinearMap.ker φ)` for an explicit
   linear functional `φ` (`EuclideanSpace.projₗ j`, or a sum of them).
2. Membership is then `x ∈ flat ↔ φ x = φ p` via
   `AffineSubspace.mem_mk'` + `LinearMap.mem_ker` + `map_sub` + `sub_eq_zero`
   — a one-line coordinate check per vertex, positive or negative alike.
3. Direction rank is `AffineSubspace.direction_mk'` + rank-nullity
   (`LinearMap.finrank_range_add_finrank_ker`, surjectivity from one witness
   with `φ x₀ ≠ 0`, `finrank_top`, `Module.finrank_self`,
   `finrank_euclideanSpace_fin`, convert with `← Module.finrank_eq_rank`).
4. Compute `P.filter (· ∈ flat)` exactly by `Finset.filter_insert` chains with
   `if_pos`/`if_neg` per vertex (config as an explicit `{p₁, …, pₙ}` literal;
   no injectivity lemma, no `fin_cases`, no `Finset.sum_image`).
5. Expand sums with `Finset.sum_insert` (non-membership from pairwise `≠`
   facts via a `ne_of_coord` helper), rewrite the `dite` weights with
   `dif_pos hpᵢ` using CANONICAL membership proofs fixed once — proof
   irrelevance then makes the weight atoms syntactically shared across all
   four equations, so `linarith` closes.

## v4.31 gotchas hit

- `Mathlib.LinearAlgebra.FiniteDimensional` no longer exists — import
  `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` (rank-nullity lives there).
- `Finset.card_insert_of_not_mem` → `Finset.card_insert_of_notMem`.
- `![a,b,c] 2` does NOT reduce under bare `norm_num [defs, WithLp.ofLp_toLp]`
  — add `Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons` explicitly
  (indices 0/1 reduce without help).
- `rw [Finset.filter_singleton, if_neg h]` leaves `insert p ∅ = {p}` goals —
  close with a trailing `rfl` (`Finset.insert_empty` is rfl). Chains ending in
  `if_pos` close automatically, as do card goals of the form `3 ≤ 3`
  (rw's rfl handles `@[refl]` relations); `3 ≤ 4` needs a trailing `omega`.

## What remains open on this node

- **S6d** — dodecahedron / icosahedron 2-flat analysis (PREP §7 leaves them
  untested; Python script generalizes).
- **S6e** — general-position uniform-weight theorem (`1 ≤ k ≤ d−1` in ℝᵈ).
- **S7** — gallery JSON for this slug (`status: "axiomatized"`, 1 axiom =
  S5 `oneflat_classification_higher_dim`).
- **IsIncenterConfigD tightening** — blocked on Mathlib ℝᵈ bisector API.
- **S5 axiom** — genuinely open in the literature.

## Honesty

- 2 new Lean files (~700 LOC total), 2 main theorems, 0 axioms, 0 sorries.
- These are refutation certificates for finite explicit configurations —
  substantive corrections of the S1 OBSERVE claims, but not progress on the
  genuinely open S5 classification itself.
- Docker build verified (see PR); host-verified with `lake env lean` first.
