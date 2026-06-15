# Knowledge Base: law-of-cosines-oq-04-oq-01

**Title**: Stewart's theorem via inner products in Euclidean space
**Phase**: ACT
**Status**: active (build-pending under dual backend blackout)

---

## Problem Understanding

The parent `law-of-cosines-oq-04` (`LawOfCosinesOQ04.lean`) proves Stewart's
theorem only at the **scalar** level: `stewarts_from_cosines` takes the two
sub-triangle law-of-cosines equations as hypotheses, with an abstract cosine
parameter `t`, and cancels the angles algebraically. The vertices `A, B, C`
never appear as geometric objects.

This OQ asks for Stewart's theorem grounded in **genuine geometry**: vertices
are points in a real inner product space, the cevian foot is an affine
combination, lengths are honest norms, and the abstract cosine is the real
inner product `⟪A-B, A-C⟫`.

---

## Result (this session, 2026-06-15, Session 1, FRESH)

**Master identity** (`stewart_cevian_inner`), valid in any real inner product
space `V` and any dimension. For `A B C : V`, `s : ℝ`, with `D = (1-s)•B + s•C`:

  ‖A - D‖² = (1-s)·‖A-B‖² + s·‖A-C‖² − s(1-s)·‖B-C‖².

**Proof skeleton** (build-pending; numerically verified to 1e-13):
1. `A - D = (1-s)•(A-B) + s•(A-C)` because `(1-s)+s = 1` — discharged by `module`.
2. `B - C = (A-C) - (A-B)` — discharged by `module`.
3. Helper `norm_smul_add_smul_sq`: `‖p•u + q•v‖² = p²‖u‖² + q²‖v‖² + 2pq⟪u,v⟫`,
   via `norm_add_sq_real`, `norm_smul` (+ `Real.norm_eq_abs`, `sq_abs`),
   `real_inner_smul_left/right`, then `ring`.
4. Expand `‖(A-C)-(A-B)‖²` with `norm_sub_sq_real`, align the inner product with
   `real_inner_comm (A-C) (A-B)`, then `ring`.

**Corollaries:**
- `stewarts_theorem_inner` — classical `b²m + c²n = a(d²+mn)` with `a=‖B-C‖`,
  `m=s·a`, `n=(1-s)·a`, `b=‖A-C‖`, `c=‖A-B‖`, `d=‖A-D‖`. No positivity needed;
  the side relation `m+n=a` is automatic and the `‖B-C‖²` term cancels exactly.
- `apollonius_median_inner` — `s=1/2` median case (Apollonius' theorem).

---

## Insights

- The whole theorem is a single bilinear identity; the only "geometry" is the
  affine combination, handled by the `module` tactic.
- Working with squared distances avoids all square roots — no sign/positivity
  hypotheses are required for the classical form.
- Mathlib v4.26.0 has everything needed: `norm_add_sq_real`, `norm_sub_sq_real`,
  `real_inner_smul_left/right`, `real_inner_comm`, and `module`. No gaps.

## Mathlib gaps

- None.

## Next steps

- `./proofs/scripts/docker-build.sh Proofs.LawOfCosinesOQ04OQ01` and register the
  file in `proofs/Proofs.lean` once a backend is available (Docker + Aristotle
  were both down at authoring time).
- Optional follow-up: angle-bisector length formula via `m:n = c:b`.

## Dead ends

- None this session.
