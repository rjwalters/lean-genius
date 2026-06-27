# S9 — Non-Vacuity Witness for the OQ-03-OQ-02 Well-Definedness Theory

**Date:** 2026-06-27
**Agent:** researcher-1
**Phase:** ACT (addendum — non-vacuity of the conditional development)
**Build status:** PENDING (host blocker, see below) — hand-verified by compiled precedent.

## Motivation

Every well-definedness theorem of PART 4g–5b carries a general-position
hypothesis of the form `pascalProjLine (permuteHexagon hex k) ≠ 0` (the `hnd`
family). PART 4j (S8) gave that hypothesis its exact geometric meaning ("the two
spanning Pascal points are projectively distinct") and a checkable sufficient
condition `pascalProjLine_ne_zero_of_minor` (one nonvanishing `2×2` minor ⟹ the
line is genuine). But a sceptical reader should ask the **vacuity question**: is
`hnd` ever satisfiable at all? If `pascalProjLine hex = 0` for *every* inscribed
hexagon, the whole conditional theory would be empty.

S9 rules that out with an explicit witness.

## What was added (PART 4k)

Appended **PART 4k** to `proofs/Proofs/PascalsHexagonOQ03.lean`
(0 sorry / 0 new axiom):

- `stdConic_nondegenerate` — the standard conic `x₀²+x₁²=x₂²` (matrix
  `diag(1,1,-1)`) has `det = -1 ≠ 0`. (`Matrix.det_fin_three` + `norm_num`,
  same pattern as parent line 403.)
- `mem_stdConic` (private) — `![a,b,c]` with `a²+b²=c²` lies on `stdConic`.
  (`Fin.sum_univ_three` + `Matrix.of_apply` + `linear_combination h`, mirroring
  parent `stdConicPoint_on_conic` at line 349.)
- `valid_of_last` (private) — `![a,b,c]` with `c ≠ 0` is a valid (nonzero)
  projective point (`congrFun … 2` + `simpa`).
- `witnessHexagon : InscribedHexagon stdConic` — the explicit hexagon with the
  six rational conic points
  `A=(1,0,1), B=(0,1,1), C=(-1,0,1), D=(0,-1,1), E=(3,4,5), F=(4,3,5)`.
- `pascalProjLine_witnessHexagon_ne_zero` — **main result**: the witness's
  Pascal line is genuinely nonzero. Discharged via `pascalProjLine_ne_zero_of_minor`
  on the `(0,1)`-minor: `pascalP = (-6,-6,-12)`, `pascalQ = (2,12,10)`, so
  `P₀Q₁ − P₁Q₀ = -72 − (-12) = -60 ≠ 0`. (`cross_apply` + `cons_val` simp set
  + `norm_num`, the pattern of `crossProduct_eq_zero_iff` / `pascal_std_conic_parametrized`.)
- `exists_inscribedHexagon_pascalProjLine_ne_zero` — packaged existence:
  ∃ a non-degenerate conic carrying an inscribed hexagon with a genuine Pascal
  line. The existence statement underlying PART 4g–5b.

## Numerical check (Python, before encoding)

```
A=(1,0,1) B=(0,1,1) C=(-1,0,1) D=(0,-1,1) E=(3,4,5) F=(4,3,5)  on x²+y²=z²
pascalP = cross(cross A B, cross D E) = (-6,-6,-12)
pascalQ = cross(cross B C, cross E F) = ( 2,12, 10)
pascalProjLine = cross(P,Q) = (84,36,-60) ≠ 0   (minor P₀Q₁−P₁Q₀ = -60)
```

## Significance (honest assessment)

Modest but genuine. The core OQ-03-OQ-02 (`pascalLine` well-definedness) was
already complete and verified through S8. S9 does **not** discharge the full
`hnd` (all 720 relabelings) for any hexagon — that is the deep conic
general-position theory, still open — and does **not** touch the open
Steiner-20 / Kirkman-60 counts. What it does is close the *vacuity* gap: it
proves the conditional well-definedness results are not empty statements by
exhibiting one concrete model, and demonstrates `pascalProjLine_ne_zero_of_minor`
firing on real data. This is the natural capstone to the PART 4j non-degeneracy
analysis.

## Build blocker (unchanged from S3–S5)

`docker-build.sh` fails: host Data volume 100% full (8.2 GiB free) and the
containerd blob store is I/O-corrupt (`docker system df` errors on a missing
blob); no `lean4-arm64:v4.26.0` image present. Local single-file `lean`
typecheck also impossible — the worktree's olean cache is partial
(`Aesop.olean`, `Mathlib/Tactic.olean` absent), and refetching needs network +
disk on a full volume. Direct `lake build` is prohibited by policy.

All PART 4k proofs reuse tactic patterns with **compiled precedent in the same
two files**: `simp only [Matrix.det_fin_three, Matrix.of_apply]` + `norm_num`
(parent 403), `simp only [Fin.sum_univ_three, Matrix.of_apply]` for the
`stdConic` match reduction (parent 351), `linear_combination h` (OQ03 1224/1439),
the `cross_apply`/`cons_val` simp set + `norm_num` (OQ03 `crossProduct_eq_zero_iff`),
and `congrFun`-at-index validity (OQ03 896–951). Same hand-verification status as
S3–S5 (which S6 later build-confirmed once the host recovered).

**Next (unchanged):** Steiner-20 / Kirkman-60 (OQ-03-OQ-03/04, genuinely open)
and the full `hnd` general-position discharge remain the only open directions.
