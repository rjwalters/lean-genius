# Desargues — OQ-03: Relationship to the Fundamental Theorem of Projective Geometry

## Summary

- **Base entry `desargues-theorem-oq-03` is already complete and merged** (#33082,
  `VERIFIED, 0-axiom, 8thm/4def/150L`). It proves, over `ℝ`, the linear engine of the
  FTPG: `det [M·p, M·q, M·r] = det M · det [p, q, r]`, so `GL₃(ℝ)` acts on `PG(2,ℝ)` by
  collineations (collinearity/concurrence preserved, and reflected when `det M ≠ 0`),
  and the Desargues configuration is projectively invariant. It explicitly leaves the
  **semilinear part** and the abstract FTPG open.

- This session authored a **follow-up**, `Proofs/DesarguesTheoremOQ03OQ01.lean`, that
  closes the semilinear gap and adds frame rigidity, over an **arbitrary field `K`**.

## Session 2026-07-02 (Session 1) — Follow-up over general fields (build-pending)

**Mode**: FRESH → SOLVED(base) → follow-up
**Outcome**: progress (new Lean file written, 0 sorry / 0 axiom by construction;
verification blocked by infra outage)

### What I did
- Surveyed the Desargues family: base (ℝ), OQ-01 (commutative rings), OQ-01-OQ-01 /
  OQ-02 (Moulton non-Desarguesian plane), OQ-04 (self-duality). Found the pool problem
  `desargues-theorem-oq-03` was already solved+merged but still claimable.
- Wrote `Proofs/DesarguesTheoremOQ03OQ01.lean` (~308 lines) generalizing the FTPG
  relationship to any field `K`:
  - `rowMat_mulVec_det` — determinant transformation law over `K`.
  - `collinear_mulVec`, `collinear_mulVec_iff` — `PGL(3,K)` acts by collineations.
  - `rowMat_map`, `collinear_semilinear` — **new**: `Aut(K)` acts by collineations
    (the semilinear factor, invisible over `ℝ`).
  - `collinear_projSemilinear` — **new**: `PΓL(3,K) ⊆ Collineations`, the constructive
    half of the FTPG.
  - `frame_general_position`, `frame_stabilizer_scalar` — **new**: the standard frame is
    in general position, and a projective map fixing a frame is scalar (frame rigidity —
    the computational kernel of the FTPG).
  - `desargues_relation_mulVec`, `desargues_relation_preserved` — Desargues invariance
    over `K`.

### Key findings
- The `Aut(K)` semilinear factor of `PΓL` cannot be seen over `ℝ` (`Aut(ℝ)` trivial);
  the general-field formulation is the natural home of the Desargues⇒coordinates⇒FTPG
  chain.
- Frame rigidity (stabilizer of a frame is trivial in `PGL`) is exactly the
  uniqueness statement that powers the FTPG.

### Blockers
- **Infrastructure outage**: local `docker-build.sh` fails — Docker VM internal disk
  throws I/O errors (os error 5) unpacking the Mathlib cache; host data volume at 100%
  (< 1 GiB free). Aristotle MCP returns `Resource not found` (service down). Neither
  kernel nor server-side verification was possible this session.
- The file is written against idioms that compile elsewhere in this repo (sibling
  `DesarguesTheoremOQ01.lean` uses the same `det_fin_three` expansion) and standard
  Mathlib lemmas (`det_mul`, `det_transpose`, `RingHom.map_det`, `Fin.sum_univ_three`),
  but remains **UNVERIFIED pending build**.

### Files modified
- `proofs/Proofs/DesarguesTheoremOQ03OQ01.lean` (new, build-pending)
- `src/data/research/problems/desargues-theorem-oq-03.json` (knowledge)
- `research/problems/desargues-theorem-oq-03/knowledge.md` (this file)

### Next steps
- Build-verify with `./proofs/scripts/docker-build.sh Proofs.DesarguesTheoremOQ03OQ01`
  when Docker/disk recover; if green, create gallery entry `desargues-theorem-oq-03-oq-01`
  (badge `original`, `verified`, 0-axiom).
- Do NOT treat as verified until built.
