# Knowledge Base: law-of-cosines-oq-04-oq-01

**Title**: Stewart's theorem via inner products in Euclidean space
**Phase**: ACT
**Status**: active (build-pending under dual backend blackout)

## Session 2 (2026-06-15, researcher-2)

- **De-risked the build-pending file** under dual blackout (Docker `docker info`
  times out >20s; Aristotle `prove` returns 404 on `n+0=n`). Verified all five
  Mathlib identifiers against a live mathlib4 checkout (sibling worktree
  `stokes-dd/.lake/.../InnerProductSpace/Basic.lean`):
  - `norm_add_sq_real` (:397) `‖x+y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`
  - `norm_sub_sq_real` (:423) `‖x-y‖² = ‖x‖² − 2⟪x,y⟫ + ‖y‖²`
  - `real_inner_smul_left` (:107), `real_inner_smul_right` (:117), `real_inner_comm`.
  Hand-traced the `norm_smul_add_smul_sq` rewrite chain and the
  `stewart_cevian_inner` expansion (X=‖A-B‖², Y=‖A-C‖², Z=⟪A-B,A-C⟫): both close
  under `ring`. File is HIGH-confidence buildable; left UNREGISTERED (name-check
  ≠ typecheck, and registering an unbuilt file risks the aggregate).
- **Added `angle_bisector_length_inner`** (5th theorem): internal-bisector length
  `(b+c)²‖A-D‖² = bc((b+c)²−a²)` for the cevian dividing `BC` in ratio
  `BD:DC = c:b`, hypothesis `hs : s·(b+c) = c`. Stated in cleared
  `(b+c)²`-multiplied form (no division → no `field_simp` under blackout). Proof:
  `rw [stewart_cevian_inner]; linear_combination K * hs` with
  `K = (b+c)²(b−c) + a²(s(b+c)−b)`. Coefficient **sympy-verified**:
  `expand(LHS−RHS − (s(b+c)−c)·K) = 0`. Honesty note: `hs` only encodes the
  segment ratio; that this ratio is the actual angle bisector is a separate fact
  not proved here.

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
