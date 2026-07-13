# pascals-hexagon-incomplete-01-oq-01

**Goal:** Discharge the remaining `sorry` `sylvester_stdConic_of_isotropic` in
`proofs/Proofs/PascalsHexagon.lean` — a non-degenerate symmetric real conic carrying a
real point is projectively equivalent to `stdConic = diag(1,1,-1)`. This is the sole gap
on the `proof_sketch_conic_implies_pascal` path (Pascal's theorem for general symmetric
non-degenerate conics).

## Session 2026-06-30 (researcher-2) — original `sorry` is GONE; asymmetric reduction landed

**Mode:** ACT (axiom-narrowing). **Outcome:** PROGRESS.
- **State change**: the `sorry` that this whole knowledge file targets
  (`sylvester_stdConic_of_isotropic` / `exists_scaledCongr_stdConic_of_isotropic`) is
  **already discharged on `main`** — `PascalsHexagon.lean` is now **0-sorry** (researcher-10
  closed the Sylvester isometry→matrix bridge manually). The file carries **1 axiom**,
  `conic_implies_pascal_constraint`, retained ONLY for the asymmetric + degenerate cases.
- **This session**: added **`proof_sketch_conic_implies_pascal_of_symmetrization`** —
  Pascal for *asymmetric* non-degenerate conics, dropping the `C.symmetric` hypothesis of
  `proof_sketch_conic_implies_pascal`. Proof: pass to the symmetric representative
  `S := ½·(C + Cᵀ)` (zero set preserved by the pre-existing `pointOnConic_iff_symmetrized`;
  `S` symmetric by `symmetrizedConic_symmetric`), rebuild the inscribed hexagon vertex-for-
  vertex in `S`, apply the symmetric theorem; `pascalConstraint` depends only on the shared
  vertices so it transfers back by `exact`. Sole extra hypothesis: `S.det ≠ 0` (the correct
  notion of non-degeneracy for an asymmetric conic — all geometric content lives in `S`).
  **Verified 0-axiom** (`#print axioms = [propext, Classical.choice, Quot.sound]`),
  host `lake env lean` EXIT 0 and docker build 3065 jobs OK.
- This discharges **step 1** of the axiom-elimination roadmap (asymmetric→symmetric).
  Residual axiom scope is now just the **degenerate** case (`S.det = 0`: pairs of lines /
  Pappus-type), which `proof_sketch_conic_implies_pascal_of_symmetrization` cannot reach.
- **GOTCHA (re-confirmed)**: edit/Write in the WORKTREE path, not the main repo checkout —
  a first edit applied to `/Users/.../lean-genius/proofs/...` (and `research/.../knowledge.md`)
  was clobbered by a concurrent main operation within seconds. Use
  `.loom/worktrees/researcher-2/...`.

### Next steps
1. The degenerate case (`S.det = 0`) is the only thing keeping the axiom. It is genuinely
   harder (Cayley–Bacharach / Pappus for line-pairs) and likely not a single-session item.
2. Optionally: prove `det(½·(C+Cᵀ)) ≠ 0 ← (some condition on C)` to phrase the asymmetric
   theorem directly in terms of `C` rather than its symmetrization.

## Summary of state
- The theorem statement is TRUE (Sylvester's law of inertia; the real-point hypothesis is
  essential and rules out the definite case).
- As of session 2026-06-28 the proof is **reduced** to a single clean linear-algebra core
  lemma; the projective-geometry wrapper is fully machine-checked (0-axiom).

## Session 2026-06-28 (researcher-2) — Step 2.3 verified (`conic_eq_of_qf_eq_of_symmetric`) + sharpened gap

**Mode:** ACT (STUCK-decompose: add an intermediate lemma toward the single hard sorry).
**Outcome:** PROGRESS — added one verified 0-axiom lemma closing the final algebraic step
(2.3) of the matrix-congruence extraction, and sharpened the remaining gap to steps 2.1–2.2.
The single real `sorry` is unchanged at `exists_scaledCongr_stdConic_of_isotropic`
(`PascalsHexagon.lean`, now ~1376 after the insertion). **Verified via `lake env lean`
(EXIT 0; full file compiles, only the pre-existing unused-simp warnings + the one expected
`sorry` warning); `#print axioms conic_eq_of_qf_eq_of_symmetric = [propext, Classical.choice,
Quot.sound]` (0-axiom).**

### What was delivered (`PascalsHexagon.lean`, before the core lemma)
- **`conic_eq_of_qf_eq_of_symmetric (C D : Conic) (hC : C.symmetric) (hD : D.symmetric)
  (h : ∀ p, conicQuadraticForm C p = conicQuadraticForm D p) : C = D`** — polarization over
  `Fin 3`: diagonals from `h` at `![1,0,0]`/`![0,1,0]`/`![0,0,1]`, off-diagonals from `h` at
  `![1,1,0]`/`![1,0,1]`/`![0,1,1]` (`simp [Fin.sum_univ_three, Matrix.cons_val_*]` then
  `ring_nf`), then 9 entry equalities by `linarith` using `symmetric`, closed by
  `ext i j; fin_cases i <;> fin_cases j <;> assumption` (defeq-tolerant `assumption` matches
  the `⟨0,_⟩`-form Fin indices that `linarith` could not atom-match — KEY GOTCHA).
- This is **step 2.3** of `exists_scaledCongr_stdConic_of_isotropic`'s plan: it upgrades a
  pointwise QF identity to a matrix equality `C = Lᵀ · diagonal w · L` (both symmetric).

### GOTCHA (reusable)
After `simp [Fin.sum_univ_three, Matrix.cons_val_*]; ring_nf`, hypotheses are clean
(`C 0 0 = D 0 0`, …) but `ext i j; fin_cases i,j` leaves the GOAL's indices as
`(fun i=>i) ⟨0,_⟩` etc., which `linarith` treats as atoms distinct from `C 0 0`. Fix: derive
the 9 entry-equalities as named `have`s with literal indices, then close with `assumption`
(defeq-tolerant), NOT `linarith`.

### The single remaining gap (now steps 2.1–2.2 only)
Extract a **matrix congruence** `C = Lᵀ · Matrix.diagonal w · L` (with `L` invertible) from
the abstract `φ : (Matrix.toQuadraticMap' C).IsometryEquiv (weightedSumSquares ℝ w)` that
`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` returns, across the
`Fin (Module.finrank ℝ (Fin 3 → ℝ)) ↔ Fin 3` cast. Then `M := P · L` (`P`, `c` from the
already-proved step 4 `diag_pm_one_congr_stdConic`) and `conic_eq_of_qf_eq_of_symmetric`
(step 2.3, this session) finish the core lemma.

### Current facts (verified by reading main)
- **Step 4 already DONE on main**: `diag_pm_one_congr_stdConic` (permutation/sign correction
  `Pᵀ · diagonal w · P = c • stdConic` for indefinite `±1` weights), 0-axiom.
- **Step 2.3 DONE this session**: `conic_eq_of_qf_eq_of_symmetric` (above), 0-axiom.
- **Aristotle is DOWN again today** (`prove_file` → `"Resource not found"`, same as
  researcher-8's session). The flagged-ideal route for this sorry is blocked until it's back.

### Open work = steps 2.1–2.2 only (the hard Mathlib-API bridge)
1. **finrank cast** `Module.finrank ℝ (Fin 3 → ℝ) = 3` via `Module.finrank_pi` /
   `Module.finrank_fin_fun`; transport `w : Fin (finrank) → ℝ` to `w' : Fin 3 → ℝ` (still
   `±1`) and the isometry `φ` along this cast.
2. **isometry → pointwise QF equality**: from `IsometryEquiv` get
   `∀ x, (toQuadraticMap' C) x = (weightedSumSquares ℝ w') (φ x)`, i.e.
   `∀ p, conicQuadraticForm C p = conicQuadraticForm (Lᵀ · diagonal w' · L) p`, with
   `L := LinearMap.toMatrix' φ.toLinearEquiv` (invertible; `weightedSumSquares` as a matrix
   is `Matrix.diagonal w'` via `toQuadraticMap'`). Both sides symmetric, so
   `conic_eq_of_qf_eq_of_symmetric` then gives `C = Lᵀ · diagonal w' · L` — closing step 2,
   hence (with steps 1/4) the whole `exists_scaledCongr_stdConic_of_isotropic`.

### Next steps
1. Land steps 2.1–2.2 (above) — the finrank cast + isometry→pointwise bridge. Best as an
   Aristotle target (resubmit `exists_scaledCongr_stdConic_of_isotropic`) once the service is
   reachable; otherwise manual via the live Mathlib 4.26 QuadraticForm API.

## Session 2026-06-28 (researcher-8, Session 1) — REDUCTION + verified infrastructure

**Mode:** FRESH | **Outcome:** progress (1 sorry → 1 sorry, but isolated + 2 new verified lemmas)

### What I did
- Aristotle was unreachable this session ("Resource not found" on every call incl. a trivial
  ping), so all work was manual.
- Added two fully-verified (`propext`/`Classical.choice`/`Quot.sound` only) lemmas:
  - `conicQF_projTransform (S M p) : conicQuadraticForm S (M·p) = conicQuadraticForm (Mᵀ*S*M) p`
    — the matrix-congruence identity `(Mp)ᵀ S (Mp) = pᵀ(MᵀSM)p`. Proof chases
    `mulVec_mulVec` / `dotProduct_mulVec` / `vecMul_transpose`.
  - `pointOnConic_projTransform_iff_of_congr (C M c hc hcong p)` : if `Mᵀ*stdConic*M = c•C`
    with `c ≠ 0` then `pointOnConic p C ↔ pointOnConic (M·p) stdConic`. This is the
    *structural heart* of projective equivalence of conics.
- Reproved `sylvester_stdConic_of_isotropic` so its body is now `sorry`-free: it `obtain`s
  the congruence witness from the new core lemma and applies
  `pointOnConic_projTransform_iff_of_congr`.
- Isolated the single remaining `sorry` into a new, sharper, purely matrix-algebraic core
  lemma `exists_scaledCongr_stdConic_of_isotropic`:
  `∃ M, M.det ≠ 0 ∧ ∃ c ≠ 0, Mᵀ * stdConic * M = c • C`.

### Key findings
- The scalar `c` (signature ±1) is genuinely needed: Sylvester gives congruence to
  `±stdConic`, and `-stdConic` has the same zero locus, so the `iff` is preserved.
- Validated against the live Mathlib 4.26 API:
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared (Matrix.toQuadraticMap' C) hsep`
  applies (hypothesis discharged by the pre-existing `mathlibQF_separatingLeft`), returning
  `w : Fin (Module.finrank ℝ (Fin 3 → ℝ)) → ℝ` with `w i = ±1` + an `IsometryEquiv`.
- **Main remaining obstacle** (documented in the core lemma's docstring): turning the abstract
  `IsometryEquiv` into a *matrix* congruence `C = Lᵀ * diagonal w * L` requires the
  `Fin (Module.finrank ℝ (Fin 3 → ℝ)) ↔ Fin 3` cast (`Module.finrank_fin_fun`/`finrank_pi`).
- Remaining sub-steps after the cast are elementary: (a) real point ⟹ `w` indefinite
  (definite forms vanish only at 0); (b) indefinite ±1 weights ⟹ permutation/sign matrix `P`
  with `Pᵀ * diagonal w * P = ±stdConic`.

### Files modified
- `proofs/Proofs/PascalsHexagon.lean` (verified, 1 sorry, all on host `lake env lean` exit 0)

### Next steps
1. Prove the permutation/sign correction as its own verified lemma (elementary, 6 cases /
   `Equiv.Perm` conjugation of `diagonal`) — cuts the core to just the Sylvester+cast step.
2. Prove the matrix-congruence extraction from `IsometryEquiv` + finrank cast — the hard part;
   ideal Aristotle target once the service is reachable again (submit
   `exists_scaledCongr_stdConic_of_isotropic`).

## Session 2026-06-28 (researcher-3) — ORIENT/de-risk: central bridge `toMatrix'_comp` identified

**Mode**: ORIENT (Aristotle UNREACHABLE — `mcp-smoke-test.sh` returns HTTP 404 on
`/api/v1/project`, same as researcher-8's session 1; all work manual). **Outcome**:
de-risk — converted step 2 ("the main remaining obstacle") into a concrete, near-mechanical
skeleton by identifying the Mathlib lemma the prior session had not named.

### Key finding
The matrix-congruence extraction `C = Lᵀ · diagonal w · L` from the abstract
`IsometryEquiv` is exactly **`QuadraticMap.toMatrix'_comp`** (Mathlib
`LinearAlgebra/QuadraticForm/Basic.lean`):
  `(Q.comp f).toMatrix' = (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f)`.
Combined with `QuadraticMap.IsometryEquiv.map_app` (`Q₂ (φ x) = Q₁ x`), the abstract
isometry becomes `toQuadraticMap' C = (weightedSumSquares ℝ w).comp φ`, and applying
`.toMatrix'` to both sides + `toMatrix'_comp` gives the congruence directly — no need to
reason about the isometry's action pointwise.

### Concrete remaining sub-steps (now spelled out in the lemma docstring)
- `(toQuadraticMap' C).toMatrix' = C`: from the already-proven `associated (toQuadraticMap' C)
  = toLinearMap₂' C` (inside `mathlibQF_separatingLeft`) + `toMatrix' Q = toMatrix₂'(associated Q)`
  + the `toMatrix₂'`/`toLinearMap₂'` round trip. NOTE: the round-trip lemma is NOT named
  `toMatrix₂'_toLinearMap₂'` in Mathlib 4.26 — `LinearMap.toMatrix₂'` is a `LinearEquiv`, so use
  `.apply_symm_apply` / `Matrix.toLinearMap₂'` as its symm. (Verify name on next attempt.)
- `(weightedSumSquares ℝ w).toMatrix' = Matrix.diagonal w`: needs a standalone helper
  (off-diagonal mixed terms of the associated bilinear form vanish). No direct Mathlib lemma.
- **The one genuinely type-dependent step**: `L := LinearMap.toMatrix' φ` is `Fin (finrank) × Fin 3`,
  NOT square. Reindex with `e := finCongr Module.finrank_fin_fun : Fin (finrank ℝ (Fin 3→ℝ)) ≃ Fin 3`
  (`Module.finrank_fin_fun : finrank R (Fin n → R) = n` confirmed present). `det ≠ 0` from φ being
  a `LinearEquiv` (`Matrix.isUnit_iff_isUnit_det`). Then steps 3 (indefinite) + 4
  (`diag_pm_one_congr_stdConic`, already proven) finish.

### Honest status
- NO new verified Lean this session (the round-trip helper names + finrank-cast reindexing each
  cost a ~60s offline build to test; closing them reliably without Aristotle is a multi-iteration
  effort I did not complete). The file still builds (offline `LAKE_UNSAFE=1 lake env lean` EXIT 0,
  1 real sorry, 1 axiom `conic_implies_pascal_constraint`). The deliverable is the sharpened,
  lemma-named skeleton in the docstring — this is the right Aristotle target the moment the
  service is reachable again (submit `exists_scaledCongr_stdConic_of_isotropic` via `prove`).
- Problem remains IN-PROGRESS (1 sorry), not completed.

### Next steps
1. When Aristotle is back: `prove_file Proofs/PascalsHexagon.lean` (single sorry) or
   `prove` the isolated `exists_scaledCongr_stdConic_of_isotropic` with the docstring skeleton.
2. Manual fallback: prove the two round-trip helpers as standalone lemmas first (build-verifiable
   independently), then the finrank-cast reindex, then assemble via `toMatrix'_comp`.

## Session 2026-06-28 (researcher-1) — Aristotle reachability re-checked: STILL DOWN → flag BLOCKED

**Mode**: ACT→BLOCKED. **Outcome**: no code change (honest). The single remaining sorry
`exists_scaledCongr_stdConic_of_isotropic` (step 2.1–2.2: finrank cast + isometry→matrix
congruence bridge) is the documented Aristotle target. Re-tested the Aristotle MCP this
session: `prove_file Proofs/PascalsHexagon.lean` → `{"status":"error","message":"Resource
not found."}` — same 404 outage seen by researcher-8/3/2.

This sorry is now stuck across **3+ sessions** (researcher-2, -3, -8), every one blocked by
the Aristotle outage; manual closure needs the uncertain Mathlib 4.26 round-trip API names
(`toMatrix₂'`/`toLinearMap₂'` round trip, `weightedSumSquares.toMatrix' = diagonal` helper —
researcher-3: "No direct Mathlib lemma") over ~10-min Docker build cycles, a multi-iteration
effort not worth a single blocked session. **Recommended status: BLOCKED until Aristotle is
reachable** — first action next session is to re-ping `prove_file`; only fall back to manual
helpers if the service stays down for several more cycles. File unchanged (1 sorry, 1 axiom
`conic_implies_pascal_constraint`); the researcher-3 skeleton in the lemma docstring remains
the exact plan.

## Session 2026-06-28 (researcher-2) — Aristotle MCP re-pinged: STILL DOWN (404) → remains BLOCKED

**Mode**: ACT→BLOCKED. **Outcome**: no code change (honest). The Aristotle MCP is now
*connected* this session, so re-tested the documented first action:
- `prove_file Proofs/PascalsHexagon.lean` → `{"status":"error","message":"Resource not found."}`
- trivial `prove` smoke test (`n + 0 = n`) → same 404 "Resource not found".

So the entire Aristotle backend is still 404 (same outage as researcher-8/-3/-2/-1 across
3+ prior sessions), not just `prove_file`. The single remaining sorry
`exists_scaledCongr_stdConic_of_isotropic` (PascalsHexagon.lean:1406, the Sylvester
isometry→matrix-congruence bridge) is unchanged. File state: 2 sorry / 1 axiom
(`conic_implies_pascal_constraint`). The researcher-3 lemma-named skeleton in the docstring
remains the exact plan; the manual fallback (uncertain Mathlib 4.26 round-trip API names over
~10-min Docker cycles) is a multi-iteration effort not worth a single blocked session.
**Status: BLOCKED until Aristotle is reachable** — first action next session: re-ping
`prove_file`; only fall back to manual helpers if the outage persists several more cycles.

## Session 2026-06-30 (researcher-3) — honest assessment: no tractable single-session work

**Mode**: OBSERVE/ORIENT → no code change (honest). Re-examined the current state:
- `PascalsHexagon.lean` is **0 real sorry** (the original target sorry
  `sylvester_stdConic_of_isotropic` was discharged by researcher-10; remaining `sorry`
  string matches are all docstring prose).
- The sole remaining axiom is `conic_implies_pascal_constraint` (line 255), stated for ALL
  conics. The proven paths `proof_sketch_conic_implies_pascal` (symmetric non-degenerate) and
  `proof_sketch_conic_implies_pascal_of_symmetrization` (asymmetric non-degenerate,
  researcher-2 PR #31606) already cover the non-degenerate cases; the axiom's *residual* scope
  is the **degenerate** case (`det = 0`: pairs of lines, Pappus-type).
- Eliminating it requires the general **Cayley–Bacharach / Pappus-for-line-pairs** argument —
  famously deep and explicitly flagged by researcher-2 as "likely not a single-session item."
  researcher-2's next-step #2 ("phrase asymmetric theorem in terms of `C` via `det(½(C+Cᵀ))≠0
  ← condition on C") has no clean general condition (det of a symmetrization is not simply
  related to `det C`), so it is not a well-defined single-session target either.

**Disposition**: no tractable single-session contribution found that would be genuinely
additive (not cosmetic). The honest next step is the multi-session degenerate-case build, or
an Aristotle/`prove` attempt on a precisely-stated line-pair sub-lemma once the service is
reachable. Releasing without a code change rather than manufacturing a marginal result.
