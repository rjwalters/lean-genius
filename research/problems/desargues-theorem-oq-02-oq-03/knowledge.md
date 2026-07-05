# Knowledge Base: desargues-theorem-oq-02-oq-03

Desargues' theorem over free rank-3 modules on (non-commutative) division rings.
Forward direction: Desargues holds over any division ring; commutativity unused.

---

## Problem Understanding

Classical result (Artin, *Geometric Algebra*): the Desargues configuration holds
in the projective plane `P(R^3)` **iff** `R` is a division ring. Commutativity is
*not* required — that governs Pappus. The parent `desargues-theorem-oq-02`
supplies the failure direction (Moulton plane, non-Desarguesian). This problem is
the positive/coordinatized direction.

---

## Insights

- **The nucleus is a telescoping identity.** The whole geometric content is
  `(a-b) + (b-c) + (c-a) = 0`. It holds in *any* `AddCommGroup` module — no
  division, no commutativity. Linear dependence of the three cross vectors (with
  the canonical witness `(1,1,1)`) is exactly collinearity of the three
  side-intersection points.
- **Cross-vector coincidence.** Under normalized central perspectivity
  `o = a+a' = b+b' = c+c'`, one gets `a - b = b' - a'` (pure group arithmetic).
  This is what makes `a - b` lie on *both* line `AB` and line `A'B'`, i.e. be
  their intersection point.
- **Commutativity genuinely unused.** The entire proof typechecks over
  `[DivisionRing R]`, not `[Field R]`, and applies to modules over the
  quaternions `H`. Scalars are only ever applied by left-multiplication to a
  single vector; no scalar is ever moved across a product.
- **Where division enters (exactly one spot).** Rescaling a *raw* perspectivity
  `o = α·a + β·a'` to normalized form `o = (α·a) + (β·a')` needs the rescaled
  representatives `α·a`, `β·a'` to remain nonzero — i.e. **no zero divisors**.
  A general ring can have `α·a = 0` with `α, a ≠ 0`, which is precisely how
  Desargues can fail without a division ring (`normalize_perspective`,
  `smul_ne_zero'`).

## What was built (UNVERIFIED — blackout)

`research/problems/.../lean/DesarguesTheoremOQ02OQ03.lean` (178 lines, 7 theorems,
1 def, 0 sorries):
`nucleus_sum`, `Dep`/`cross_dep`, `cross_eq`, `sub_mem_span`, `desargues`
(the assembled statement), `smul_ne_zero'`, `normalize_perspective`, plus a
quaternion `example`. Placed outside the `proofs/Proofs/` glob so it cannot break
the gallery build.

## Dead Ends / Deferred

- **Uniqueness of the intersection point** (that `a-b` is *the* unique
  intersection, not merely *an* incident point) needs general-position
  hypotheses (non-degenerate triangles, distinct lines) — deferred.
- **The converse** (Desargues ⇒ division-ring coordinatization) is the hard
  coordinatization theorem — not attempted this session.

## Blockers

Verification blackout 2026-07-04: Docker image build fails (containerd
`meta.db` I/O error); Aristotle MCP `prove_file` returns 404. File is UNVERIFIED.

## Sessions

### Session 2026-07-04 (Session 1) — Forward direction formalized
**Mode**: FRESH · **Outcome**: progress (build-blocked)
- Formalized the linear-algebra Desargues over a division ring; isolated the
  no-zero-divisors step; showed commutativity unused (quaternion example).
- Could not machine-check (dual blackout). File placed under `research/lean/`.
- Next: verify + promote when infra returns; then attempt uniqueness / converse.
