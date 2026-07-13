# Research State: hurwitz-theorem-oq-03-oq-01-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-05
**Iteration**: 8

## Current Focus
Iter 8 (build-VERIFIED, docker 2715 jobs, 0 sorry/0 axiom added): **the metric-level
Frobenius cap package** — recast all remaining algebraic obstructions in terms of the
positive-definite form `B = imaginaryBilin A` on `Im A`, plus the rank–nullity reduction.
Four new verified lemmas:

1. `finrank_eq_imaginary_add_one`: `finrank ℝ A = finrank ℝ (Im A) + 1`. `realPart : A →ₗ[ℝ] ℝ`
   is surjective (`c•1 ↦ c` via `realPartValue_smul_one`) and `Im A = ker realPart`, so
   rank–nullity (`LinearMap.finrank_range_add_finrank_ker` + `finrank_top`/`Module.finrank_self`)
   gives the reduction. **This collapses the whole theorem to `finrank ℝ (Im A) ∈ {0,1,3}`.**
2. `imaginary_mul_mem_imaginarySubmodule`: for B-orthogonal imaginary x,y, `x*y ∈ Im A`
   (metric wrapper over `isImaginary_mul_of_anticomm` via the bridge).
3. `imaginaryBilin_mul_orthogonal`: the third unit `z = x*y` is B-orthogonal to both x and y
   (metric wrapper over `mul_anticomm_left`/`mul_anticomm_right`). Grows an orthonormal pair
   into an orthonormal quaternion triple ⟨x, y, x*y⟩.
4. `eq_zero_of_orthogonal_to_triple`: **no fourth orthogonal unit** — any `w ∈ Im A`
   B-orthogonal to x, y, and x*y is zero (metric wrapper over
   `eq_zero_of_anticomm_pair_and_product`). Caps `finrank ℝ (Im A) ≤ 3`.

The whole file still has exactly ONE sorry (`hurwitz_only_if_ring` non-commutative branch),
now scoped PURELY to the linear-algebra assembly: pick a B-orthonormal basis of `Im A`, use
(2)+(3) to manufacture the third generator and (4) + positive-definiteness to rule out
`finrank = 2` and `finrank ≥ 4`, concluding `finrank ℝ (Im A) ∈ {0,1,3}`; combine with (1).

## Active Approach
All ALGEBRAIC and METRIC prerequisites are now in place (0 sorry). What remains is a pure
finite-dimensional inner-product-space counting argument with NO further division-ring
input:
- Reduction to Im A: DONE (`finrank_eq_imaginary_add_one`).
- Positive-definite inner product on Im A: DONE (`imaginaryBilin*`, iter 6).
- Metric↔algebra bridge: DONE (`imaginaryBilin_eq_zero_iff_anticomm`, iter 7).
- Third-unit manufacture + no-fourth-unit obstruction: DONE (iter 8, this commit).

## Attempt Count
- Total attempts: 4 (code, shipped)
- Approaches tried: 3

## Blockers
- The last sorry needs: an orthonormal basis of the positive-definite space `(Im A, B)` and
  the standard "orthogonal complement is trivial ⟹ full" reasoning to convert lemmas (2)–(4)
  into the numerical bound `finrank ℝ (Im A) ∈ {0,1,3}`. This is now pure Mathlib linear
  algebra (needs an `InnerProductSpace`/`BilinForm.Nondegenerate` packaging of `imaginaryBilin`,
  or a hand-rolled Gram–Schmidt), no more algebra of `A`.

## Next Action
Convert `imaginaryBilin` into an inner product (via `InnerProductSpace.ofCore` or a
`LinearMap.BilinForm` that is positive-definite hence nondegenerate) so that:
- `finrank ≠ 2`: with orthonormal e₁,e₂ spanning Im A, `e₁*e₂` (lemma 2) is nonzero and
  B-orthogonal to the full basis (lemma 3) ⇒ B(e₁*e₂, e₁*e₂)=0 ⇒ e₁*e₂=0, contradiction.
- `finrank ≤ 3`: a fourth vector orthogonal to e₁,e₂,e₁*e₂ vanishes (lemma 4).
Then `finrank ℝ (Im A) ∈ {0,1,3}` and `finrank_eq_imaginary_add_one` closes the sorry.
Consider submitting the fully-scaffolded `hurwitz_only_if_ring` to Aristotle with all four
new lemmas as context, hint = "finish Frobenius: finrank ℝ (Im A) ∈ {0,1,3} via the
positive-definite form imaginaryBilin".
