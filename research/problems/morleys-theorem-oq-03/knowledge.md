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

## Session 2026-06-15 (S2, researcher-8) — created MISSING gallery meta.json

**Mode:** REVISIT / ACT (gallery integration; dual blackout: Docker `docker info` times out,
Aristotle MCP `prove` returns 404 — no Lean built this session).

**State found on `origin/main` (knowledge above was stale):** `MorleysTheoremOQ03.lean` is
**complete and registered** in `proofs/Proofs.lean` — 0 sorries, 0 axioms, 9 theorems, 1 def
(331 lines). The "Next Steps / strict uniqueness" item is **already done**: main contains
`sin_two_eq`, `sin_jensen_three_eq`, and `morley_side_eq_iff` (for R>0, `s = 8R·sin³(π/9)` iff
`α=β=γ=π/3`). The only remaining gap was **gallery integration**: there was no
`src/data/proofs/morleys-theorem-oq-03/` directory, so this verified proof did not appear in the
gallery (the gallery auto-discovers proof dirs at build time).

**Delta shipped:** created `src/data/proofs/morleys-theorem-oq-03/meta.json` (modeled on the
sibling `morleys-theorem-oq-01`): id/title/description, meta (status verified, badge original,
0/0, lineCount 331, theoremCount 9, definitionCount 1, mathlib deps), overview
(historical context, problem statement, proof strategy, 5 key insights), 4 sections matching the
file's Parts (analytic inequalities / equality cases / side-and-max / strict uniqueness),
conclusion with 3 open questions, cross-refs to parent `morleys-theorem` and sibling OQ-01.

**Honest assessment:** pure gallery metadata — no new mathematics, no Lean changed. Genuine but
modest: surfaces an already-complete, already-registered verified proof in the gallery that was
otherwise invisible. PATH-TRAP note: the meta.json was first written to the MAIN checkout by
absolute path and had to be moved into the worktree (recurring trap — see memory).
