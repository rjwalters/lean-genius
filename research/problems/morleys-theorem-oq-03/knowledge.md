# Knowledge Base: morleys-theorem-oq-03

Extremal question for Morley's trisector theorem.

---

## Problem Understanding

The parent file `MorleysTheorem.lean` establishes that the Morley equilateral
triangle of a triangle with angles `α, β, γ` and circumradius `R` has common side

    s(α, β, γ) = 8 R · sin(α/3) · sin(β/3) · sin(γ/3).

OQ-01 formalized Conway's backward construction; OQ-02 studies *second* Morley
triangles from non-adjacent trisectors. OQ-03 is the orthogonal **extremal**
question:

> Among all triangles with a fixed circumradius `R`, which one maximizes the
> Morley triangle's side length?

**Answer: the equilateral triangle, uniquely.** Maximal side = `8R sin³(π/9) ≈ 0.32008 R`.

---

## Insights

- Substituting `aᵢ = αᵢ/3`, the constraint `α+β+γ = π` becomes `a₁+a₂+a₃ = π/3`,
  so the **trisected-angle mean is always `π/9`** independent of the triangle.
  Maximizing `s` reduces to maximizing `∏ sin aᵢ` subject to fixed sum `π/3`.
- The maximum of `∏ sin aᵢ` (fixed sum, each in `(0, π/3)`) is at `a₁=a₂=a₃=π/9`
  by concavity of `sin` plus AM–GM. No calculus / Lagrange multipliers needed.
- **Two-step bound** (numerically verified at many points, 0 violations):
    `∏ sin aᵢ ≤ ((Σ sin aᵢ)/3)³ ≤ sin(π/9)³`,
  the first step is AM–GM(3), the second is Jensen for the concave `sin`.
- AM–GM(3) has an explicit SOS-style certificate:
    `(u+v+w)³ − 27uvw = 3·Σ u(v−w)² + ½·(u+v+w)·Σ(u−v)² ≥ 0`,
  which `nlinarith` discharges from the six product hints.
- Three-point sin-Jensen is obtained by chaining the two-point midpoint
  concavity (`strictConcaveOn_sin_Icc.concaveOn.2`) four-point style: treat the
  mean `m` as a fourth point so the four-point average is again `m`.

---

## Built Items (proofs/Proofs/MorleysTheoremOQ03.lean — build-pending, UNREGISTERED)

- `amgm_three`              : AM–GM for three nonnegatives, cubed form.
- `sin_jensen_three`        : three-point Jensen for `sin` on `[0, π]`.
- `div_three_mem_Icc`       : trisected angle lies in `[0, π]`.
- `morley_side_le_equilateral` : `s(α,β,γ) ≤ 8R sin³(π/9)`.
- `morley_side_equilateral`    : the equilateral attains the bound.
- `morley_side_max`            : packaged "maximum at the equilateral".

---

## Mathlib Gaps

- None blocking. `strictConcaveOn_sin_Icc`, `ConcaveOn.le_map_sum`,
  `geom_mean_le_arith_mean3_weighted`, `pow_le_pow_left₀`, `sin_nonneg_of_mem_Icc`
  all present in pinned Mathlib v4.26. (The proof avoids the weighted-AM–GM rpow
  form in favor of a self-contained `nlinarith` certificate.)

---

## Dead Ends

- Lagrange-multiplier / derivative approach: unnecessary; the elementary
  AM–GM + Jensen chain is shorter and fully formalizable without `deriv`.

---

## Next Steps

- **Strict uniqueness**: prove equality `s = 8R sin³(π/9)` holds *iff*
  `α=β=γ=π/3`, via `StrictConcaveOn` strict Jensen for `sin` and strict AM–GM.
- Verify the build once Docker is available; register in the gallery and add
  `src/data/proofs/morleys-theorem-oq-03/` meta.json.
