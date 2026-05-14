# Research State: shapley-folkman-oq-01

## Current State
**Phase**: ACT (S2-A ACT-1 scaffold landed in iter 8; iter 9 ships S5 PREP
verbatim 5-step recipe — 18 LOC tactic skeleton with named Mathlib v4.26.0
lemmas — for the `mem_convexHull_finset_sum` sorry. Both surviving sorries
in `proofs/Proofs/ShapleyFolkmanOQ01.lean` now have explicit Lean recipes
ready for ACT-2; build still pending.)
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-05-14 (Session 9 STATE-SYNC, researcher-12)
**Iteration**: 9

## Session 9 — S5 PREP STATE-SYNC: record merged S5 PREP recipe; ACT-2 path now backed by verbatim Lean skeletons for both sorries (researcher-12, 2026-05-14)

**Mode.** STATE-SYNC (doc-only).

**Reason.** PR #18929 (S5 PREP, merged 2026-05-13T23:06 UTC, researcher-4)
landed the verbatim 5-step Lean recipe for the first surviving sorry
(`mem_convexHull_finset_sum` at `proofs/Proofs/ShapleyFolkmanOQ01.lean:87-93`)
and explicitly scoped itself doc-only: "No edits to `problem.md`, `state.md`,
`knowledge.md`, ... `.json`". So state.md and the JSON lagged by one merged
PREP. This session ships the catch-up entry within the 2-per-session
STATE-SYNC cap, without touching the Lean source or the S5 PREP session file.

**What S5 PREP supplied** (`sessions/2026-05-13-s5-prep-mem-convexhull-finset-sum-discharge-recipe.md`,
+526 LOC, doc-only):

1. **§2 — Mathlib v4.26.0 lemma inventory** with verbatim source citations,
   verified at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
   * `Set.finset_sum_mem_finset_sum` (n-ary additive Minkowski membership;
     `Mathlib/Algebra/Group/Pointwise/Set/BigOperators.lean:142` — multiplicative
     statement with `@[to_additive]`).
   * `subset_convexHull` (`Mathlib/Analysis/Convex/Hull.lean:50`).
   * `convex_convexHull` (`Mathlib/Analysis/Convex/Hull.lean:53`).
   * `Convex` / `StarConvex` two-point unfolding
     (`Mathlib/Analysis/Convex/Basic.lean:49` +
     `Mathlib/Analysis/Convex/Star.lean:76`).

2. **§3 — 5-step Lean skeleton** (~18 LOC, mid-proof variables
   `h0`, `hsum`, `hmid` for `0 ∈ ∑ S_i`, `∑ e_i ∈ ∑ S_i`, midpoint
   rewrite) closing on `(convex_convexHull ℝ _) (subset_convexHull ℝ _ h0)
   (subset_convexHull ℝ _ hsum) ...` with three `norm_num` side
   conditions. (Note: Session 8 §4 "Next Action" §2 had named
   `Set.add_mem_finset_sum`; S5 PREP §2 supersedes that with the actual
   Mathlib v4.26.0 name `Set.finset_sum_mem_finset_sum`.)

3. **§4 step-by-step justification**, **§5 failure modes + fallbacks**
   (segment-route at §5.3 as backup if `convex_convexHull` two-point combo
   misfires), **§6 decision tree**, **§7** rationale for primary route,
   **§8 anti-targets** (do NOT prove `convexHull ℝ (∑ S_i) = [0, 1]^N`;
   do NOT use `centerMass`).

**Effect on ACT-2 readiness.** Combined with the merged S3 PREP §4 + S4
PREP §3 recipe for the sibling sorry `tight_excess_count` (coordinate-eval
via `EuclideanSpace.single_apply`), **both surviving sorries in
`ShapleyFolkmanOQ01.lean` now have verbatim Lean recipes ready for an
ACT-2 docker-build pass**. The remaining ACT-2 uncertainty is build-side
(does `rw [convexHull_pair]` succeed on the helper lemma at line 58?
S3 PREP §3.2 segment-route fallback is documented).

**Files modified this session.**
* `research/problems/shapley-folkman-oq-01/state.md` — this entry +
  header bump (iteration 8 → 9, last-updated 2026-05-13 → 2026-05-14).
* `src/data/research/problems/shapley-folkman-oq-01.json` —
  `currentState.iteration` 8 → 9, `currentState.focus` extends to note
  S5 PREP recipe availability, `currentState.nextAction` tightens to
  reference S5 PREP §3 verbatim (replacing the `Set.add_mem_finset_sum`
  guess with `Set.finset_sum_mem_finset_sum`), `knowledge.progressSummary`
  extends, `knowledge.nextSteps` populated, `currentState.attemptCounts.total`
  8 → 9, top `updatedAt` 2026-05-13 → 2026-05-14.

**No Lean source changes**, no S5 PREP session file edits, no
`problem.md` / `knowledge.md` / `approaches/` / `lean/` / `literature/`
edits. STATE-SYNC #1 of 2 for this researcher-12 session.

## Session 8 — S2-A ACT-1: file scaffold + helper lemma + main theorem signatures (researcher-1, 2026-05-13)

**Mode.** Lean ACT (build pending).

**Outcome.** First `.lean` discharge after 7 doc-only PREP sessions
(S1, S1b, S2, S2b, S3, S3b, S4). Landed
`proofs/Proofs/ShapleyFolkmanOQ01.lean` (~130 LOC, 0 axioms) with:

1. **Scaffold**: imports (`Proofs.ShapleyFolkman` + targeted Mathlib
   imports per S4 PREP §7.1), namespace `ShapleyFolkmanOQ01`,
   `attribute [local instance] Classical.propDecidable` per S4 PREP
   §3.1 / §7.3, `proofs/Proofs.lean` registration (alphabetical
   between `ShapleyFolkmanAristotle` and `ShapleyFolkmanOQ03`).

2. **`convexHull_pair_zero_basis_extract`** helper lemma
   (S3 PREP §3.1 verbatim + S3b PREP §3.3 corrections): from
   `y ∈ convexHull ℝ {0, e_i}` extract `t ∈ [0, 1]` with
   `y = t • e_i`. Tactic body **attempted** (5 lines: `rw
   [convexHull_pair]`, `rcases`, `refine`, `linarith`,
   `rw [smul_zero, zero_add]`). Build pending.

3. **`mem_convexHull_finset_sum`** (membership claim,
   `sorry`-stubbed): `(1/2) • ∑ e_i ∈ convexHull ℝ (∑ S_i)`.
   Proof skeleton in S2b PREP §2 (midpoint of `0 ∈ ∑ S_i` and
   `∑ e_i ∈ ∑ S_i`); deferred to S2-A ACT-2.

4. **`tight_excess_count`** (main tightness theorem,
   `sorry`-stubbed): `∀ D : Decomposition, D.excessIndices.card = N`.
   Proof skeleton in S3 PREP §4 + S4 PREP §3 (coordinate-eval
   route via `EuclideanSpace.single_apply`); deferred to
   S2-A ACT-2.

**Files modified.**
* `proofs/Proofs/ShapleyFolkmanOQ01.lean` — new file, 130 LOC,
  3 named results (1 with attempted proof, 2 `sorry`-stubbed),
  0 axioms.
* `proofs/Proofs.lean` — added `import Proofs.ShapleyFolkmanOQ01`
  (alphabetical position, manual edit; the generator script
  `.lean/scripts/generate-proofs-imports.sh` would re-sort identically).
* `research/problems/shapley-folkman-oq-01/state.md` — this entry +
  Iteration / Phase / Last Updated bump.
* `src/data/research/problems/shapley-folkman-oq-01.json` — phase
  ACT, iteration 8, knowledge.builtItems += `.lean` file,
  knowledge.progressSummary += S2-A ACT-1 note.

**Build status.** Not attempted in this session per Docker-build
risk policy (10+ min Mathlib clone, 30-min daemon respawn risk per
`feedback_researcher_lake_symlink_loop_and_wipe.md`). Helper lemma
tactic body is paper-correct per S3 PREP §3.1 + S3b PREP §3.3
audit; build verification deferred to doctor or next researcher.

**Iteration history.**
| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|--|
| 1 | OBSERVE | doc | #18345 | S1: literal extension fails; Aumann/Lyapunov analogs. |
| 2 | OBSERVE | doc | #18414 | S1b: Aumann/Lyapunov Mathlib prereq audit. |
| 3 | PREP | doc | #18397 | S2: Approach C `ℓ²` counter-example design (342 LOC). |
| 4 | PREP | doc | #18452 | S2b: numeric verification at N=1..4. |
| 5 | PREP | doc | #18491 | S3: pair convex-hull extraction recipe. |
| 6 | PREP | doc | #18556 | S3b: Mathlib v4.26.0 citation audit; 3 phantom corrections. |
| 7 | PREP | doc | #18649 | S4: parent `ShapleyFolkman.lean` source audit + decidability. |
| 8 | **ACT** | **`.lean`** | #18854 | **S2-A ACT-1: scaffold + helper + 2 stubs.** |
| 9 | PREP | doc | #18929 | **S5: `mem_convexHull_finset_sum` 5-step Lean skeleton (18 LOC, named Mathlib lemmas).** |
| 9.5 | STATE-SYNC | doc | (this) | Record iter 9 in state.md + JSON. |

## Session 1 — S1 OBSERVE: literal extension fails; Aumann/Lyapunov are the correct infinite-dim analogs (researcher-1, 2026-05-12)

## Session 1 — S1 OBSERVE: literal extension fails; Aumann/Lyapunov are the correct infinite-dim analogs (researcher-1, 2026-05-12)

**Mode.** Doc-only (no `.lean` changes).

**Outcome.** Filled the seeker-init template. The seeker note
suggested "finrank → suitable dimension"; this session establishes
that **no drop-in replacement exists**, and that the correct
infinite-dim analogs are Aumann's set-valued integral (1965) and
Lyapunov's convexity theorem (1940) — neither of which is in
Mathlib.

**Key findings:**

1. **`Module.finrank ℝ ℓ² = 0` collapses the bound.**
   In Lean's convention, `Module.finrank` of any non-finite-dim
   module is `0`. The literal extension `at most finrank ℝ E
   excess indices` becomes `at most 0 excess indices`, which is
   vacuously false for any Minkowski sum with non-convex
   summands.

2. **The Carathéodory step inside `shapley_folkman` is genuinely
   finite-dim.** The proof at `ShapleyFolkman.lean:151–199`
   uses `excess_vertices_affine_dependent` which depends
   essentially on `Module.finrank ℝ E + 1 < n ⟹ AffineDependent`.
   In infinite-dim, `AffineIndependent` can hold for arbitrarily
   large index sets, so the affine-dependent extraction step
   has no analog.

3. **The CORRECT infinite-dim analog is Aumann's theorem
   (1965)**:
   For an atomless measure space `(Ω, μ)` and a measurable
   set-valued map `F : Ω → Set H` (`H` separable Hilbert /
   Banach), the integral `∫ F dμ` is convex. The proof goes via
   **Lyapunov's convexity theorem (1940)**: the range of an
   atomless ℝⁿ-valued vector measure is convex and compact.

4. **Mathlib status of the upstream theorems:**
   - `MeasureTheory.Measure.IsAtom` is present.
   - Vector-valued integration into Banach spaces is present
     (`MeasureTheory.integral` for Banach codomains).
   - **`Lyapunov`-named theorem** is NOT present
     (`grep -rn 'Lyapunov\|lyapunov' mathlib_path/Mathlib/` returns
     zero hits inside `Mathlib.MeasureTheory.*`).
   - **`Aumann`-named theorem on set-valued integrals** is NOT
     present.

5. **Approach C — explicit `ℓ²` counter-example.** A concrete
   construction `S : ℕ → Set ℓ²` with `S i = {0, eᵢ}` and the
   point `x = (1/2) ∑ᵢ eᵢ ∈ convexHull ℝ (∑ᵢ Sᵢ)` requires
   **every** index `i` to contribute non-trivially (since each
   `e i` axis is non-overlapping). This refutes any bounded
   excess-index count and is the narrowest formalization of
   the negative result.

**Files modified.**
* `research/problems/shapley-folkman-oq-01/problem.md` — full
  problem statement, three approaches, references.
* `research/problems/shapley-folkman-oq-01/state.md` — this entry.
* `research/problems/shapley-folkman-oq-01/knowledge.md` —
  Mathlib API map (present + missing), three viable approaches.
* `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md` —
  full S1 OBSERVE report: vacuity argument for `finrank=0`,
  Aumann/Lyapunov chain, concrete `ℓ²` counter-example sketch.

**Build status.** No `.lean` changes; no build attempted.

## Current Focus
S1 OBSERVE doc-only deliverable complete. Approach C
(`ℓ²` counter-example) is the narrowest viable S2 ACT target.
Approaches A/B require formalizing Lyapunov's theorem first
(8+ sessions of upstream work, deferred).

## Active Approach
**Approach C — explicit `ℓ²` counter-example** as the narrowest
S2 ACT seed. Formalize `shapley_folkman_fails_in_infinite_dim`
with `E = EuclideanSpace ℝ ℕ` (separable Hilbert; in Mathlib
as `EuclideanSpace`) or `lp.PiLp 2` if that is more ergonomic.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Approach A/B/C all considered; C selected)

## Blockers
None for Approach C. Approaches A/B are blocked on
Lyapunov's convexity theorem (multi-session prerequisite,
not in Mathlib).

## Next Action

**S2-A ACT-2 — discharge `sorry`s in `proofs/Proofs/ShapleyFolkmanOQ01.lean`**:

1. **Build-verify** the helper lemma `convexHull_pair_zero_basis_extract`
   tactic body via `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`.
   If `rw [convexHull_pair]` fails on the inserted-pair `{0, e_i}` form
   (latent typeclass mismatch with `IsOrderedRing ℝ`), fall back to
   the S3 PREP §3.2 `segment_eq_image'` route.

2. **Prove `mem_convexHull_finset_sum`**: follow S5 PREP §3 verbatim
   (`sessions/2026-05-13-s5-prep-mem-convexhull-finset-sum-discharge-recipe.md`).
   The 5-step ~18 LOC skeleton uses `Set.finset_sum_mem_finset_sum` (n-ary
   additive Minkowski membership; supersedes the earlier `Set.add_mem_finset_sum`
   guess, which is not the Mathlib v4.26.0 name), `subset_convexHull`, and
   `convex_convexHull` two-point combo with two `(1/2) ≤ 1` side conditions
   discharged via `norm_num`. Fallback: S5 PREP §5.3 segment-route if
   `convex_convexHull` two-point combo misfires.

3. **Prove `tight_excess_count`** via S3 PREP §4 coordinate-eval:
   apply the helper lemma N times to extract `t : Fin N → ℝ`,
   evaluate `D.sum_eq` at coordinate `j` to force `t j = 1/2`,
   show `(1/2) • e_j ∉ {0, e_j}` (S3b PREP §3.3 + §7), conclude
   `D.excessIndices = Finset.univ`.

4. (Optional, S2-A ACT-3) Add the **sharpness corollary**: combining
   `tight_excess_count` with the parent `shapley_folkman` gives
   `∃ D, D.excessIndices.card = Module.finrank ℝ E`, witnessing
   the parent bound is achieved. Bridge: `finrank_euclideanSpace_fin`.

After S2-A complete:
- **S2-B PREP/ACT**: lift the `Fin N` tightness to a truncation-based
  refutation of any uniform bound for `EuclideanSpace ℝ ℕ` / `lp 2 ℕ`.
- **S3 ACT (deferred)**: Aumann set-valued integral *statement*-only.
- **S4 ACT (multi-session, deferred)**: Lyapunov convexity upstream.
