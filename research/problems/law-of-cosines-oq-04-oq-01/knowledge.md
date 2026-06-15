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

## Result (Session 2, 2026-06-15, researcher-7 — ACT follow-up + de-risk)

The S1 file (`LawOfCosinesOQ04OQ01.lean`, merged PR #24274) is committed but
still **UNREGISTERED** in `Proofs.lean` (build-pending; Docker + Aristotle both
down again this session — `docker info` times out).

**De-risk**: all 8 Mathlib identifiers the S1 file relies on
(`norm_add_sq_real`, `norm_sub_sq_real`, `real_inner_smul_left/right`,
`real_inner_comm`, `norm_smul`, `sq_abs`, `Real.norm_eq_abs`) were grepped
against the pinned Mathlib tree in the sibling `stokes-dd` worktree
(`.lake/packages/mathlib/Mathlib`) and **all confirmed present**. High
confidence the file compiles once a backend returns.

**New theorems** (the documented S1 next-step, division-free):

- `stewart_angle_bisector_inner` — the internal-angle-bisector case. The
  bisector ratio `BD : DC = AB : AC` is encoded as the single hypothesis
  `s·‖A - C‖ = (1 - s)·‖A - B‖`. Under it the master identity collapses to the
  classical **angle-bisector length law**

      ‖A - D‖² = ‖A - B‖·‖A - C‖ − s(1 - s)·‖B - C‖².

  Key algebraic fact: with `b = ‖A-C‖`, `c = ‖A-B‖`, the relation `s·b = (1-s)·c`
  forces `(1-s)c² + s·b² = b·c`, since
  `(1-s)c² + s·b² − bc = (b − c)·(s·b − (1-s)·c)`. So the whole proof is
  `rw [stewart_cevian_inner]; linear_combination (‖A-C‖ - ‖A-B‖) * hbis` — no
  division, no `field_simp`, no positivity.
- `stewart_angle_bisector_segments` — same result in the textbook segment form
  `t² = bc − mn` with `m = BD = s‖B-C‖`, `n = DC = (1-s)‖B-C‖` written out
  (one `ring` after the previous theorem).

Numerically re-verified: 200k random trials, dims 1–4, max error ~8.5e-14.

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
  were both down at authoring time AND at S2 2026-06-15). All Mathlib names
  confirmed present in the pinned tree (S2 de-risk), so the build should be a
  formality.
- DONE (S2): angle-bisector length formula via `m:n = c:b`
  (`stewart_angle_bisector_inner`, `stewart_angle_bisector_segments`).
- Optional follow-up: the *external* angle bisector (ratio `BD:DC = c:b` with the
  foot outside segment BC, i.e. `s` outside `[0,1]`); the same master identity
  applies with `s·‖A-C‖ = −(1-s)·‖A-B‖`, giving `t² = s(1-s)a² − bc` (note the
  sign flip / the foot lies beyond an endpoint).

## Dead ends

- None this session.
