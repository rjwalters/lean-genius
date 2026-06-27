# Knowledge Base: area-of-circle-oq-03-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Question:** Can Archimedes' original half-angle doubling method (computing
polygon side lengths via √((1−cos)/2)) be formalized as a constructive proof?

**Answer: YES.** Formalized in `proofs/Proofs/AreaOfCircleOQ03OQ02OQ01.lean`
(14 declarations, 0 sorries, 0 axioms; not yet machine-verified — host Docker
build environment corrupted, see Dead Ends).

For the unit circle the inscribed regular n-gon has side length
`sideLength n = 2·sin(π/n)` (a chord subtending central angle 2π/n). Archimedes
doubled the number of sides (6→12→24→48→96), computing each new side length from
the previous one by square roots only — the constructive content of the method.

---

## Insights

1. **The nested-radical recurrence.** The doubling step is exactly
   `sideLength (2n) = √(2 − √(4 − sideLength(n)²))` for n ≥ 2. It unwinds to
   Archimedes' √((1−cos)/2): writing s = 2 sin(π/n),
   - `4 − s² = 4 cos²(π/n)`, so `√(4 − s²) = 2 cos(π/n)` (needs cos ≥ 0, i.e.
     n ≥ 2 — true at every step of the 6→12→24→… chain);
   - `2 − 2 cos(π/n) = (2 sin(π/2n))²` by the half-angle identity, so the outer
     √ yields `2 sin(π/2n) = sideLength (2n)`.

2. **Half-angle core is range-free.** `sin(x/2)² = (1 − cos x)/2` holds for ALL
   real x (proved from `cos_two_mul` + Pythagoras, pure `linarith`). The square
   root form `sin(x/2) = √((1−cos x)/2)` needs only `0 ≤ x ≤ 2π` to fix the sign
   (via `Real.sin_nonneg_of_nonneg_of_le_pi` + `Real.sqrt_sq`). This is the
   cleanest entry point and avoids Mathlib's `Real.cos_half`/`sin_half` (whose
   exact names/signatures are version-fragile).

3. **Constructivity is witnessed concretely.** From the hexagon base
   `sideLength 6 = 1` the recurrence gives `sideLength 12 = √(2 − √3)`
   (`sideLength_dodecagon`), and the pattern continues
   `sideLength 24 = √(2 − √(2 + √3))`, … — each a finite tower of square roots,
   i.e. a constructible number.

4. **Convergence ties it to π.** `perimeter n = n · sideLength n = 2n·sin(π/n)
   → 2π` (`perimeter_tendsto`, via `sin h / h → 1`), and `perimeter n < 2π`
   for n ≥ 2 (`perimeter_lt_two_pi`, Archimedes' lower-bound side). So the
   doubling sequence of constructible side lengths produces perimeters that
   increase to the circumference — i.e. compute π.

5. **Gap vs. existing gallery.** Sibling files cover *areas*
   (`ArchimedesMethodOfExhaustion`), the O(1/n²) *convergence rate*
   (`AreaOfCircleOQ03OQ01`), and the 96-gon *π-bounds* via Mathlib's `pi_gt_d4`
   (`AreaOfCircleOQ03OQ02`). None formalize the constructive *side-length
   doubling recurrence* — this file fills that gap.

---

## Dead Ends

- **Machine verification blocked this session.** Host Docker/containerd content
  store is I/O-corrupted (`docker images` errors) and `/System/Volumes/Data` is
  100% full (~5 GiB free), so `docker-build.sh` cannot run. Aristotle MCP only
  fills `sorry`s, so it cannot compile-check a sorry-free file. The file is
  hand-reviewed against Mathlib v4.26.0 API; mark the PR ready once a build
  passes. Lemma names were chosen to match patterns already compiling in
  sibling files (`tendsto_const_div_atTop_nhds_0_nat`, `div_lt_iff₀`,
  `Real.cos_nonneg_of_mem_Icc`, `Real.sqrt_sq`, `gcongr`).
