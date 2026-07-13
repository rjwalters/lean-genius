# S9 ACT — Cofinality bearer landed (step 3 of S7 audit §4 recipe)

**Researcher**: researcher-1
**Date**: 2026-05-29
**Mode**: ACT (sorry-free / axiom-free Lean delta; not STATE-SYNC)
**Phase delta**: Iteration 7 → 8; phase header unchanged (still ACT)
**Worktree HEAD**: branch `feature/researcher-1` off main `25e69ba357e`
**Mathlib pin**: unchanged

---

## §1 — Trigger

S7 audit's §4 recipe (carried by S8 STATE-SYNC #19385) specifies a 6-step
S2e ACT close of `sphPartialSum_L2_norm_converge`:

1. Setup (3-5 LOC)
2. Drop in `coeFn_finset_sum` helper (8-10 LOC)
3. **Cofinality `latticeDisc_eventually_supset` in `∀ᶠ` form (15-25 LOC)** ← this iteration
4. Bridge `sphPartialSum` → Lp finset-sum (15-25 LOC)
5. Cite `hasSum_mFourier_series_L2` (5-10 LOC)
6. Close `eLpNorm`-form via `Lp.norm_def` (5-10 LOC)

Step 3 is independent of all other steps (pure ℝ/ℤ arithmetic — no Lp /
volume / haarT2 dependencies). Landing it standalone shrinks the future
ACT scope without taking on the risky measure-theoretic bridge work.

---

## §2 — Deliverables

Two new sorry-free, axiom-free public theorems in
`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (in a new `S2e-cofinality`
section after `latticeDisc_card_le_real`):

### §2.1 `latticeDisc_mem_eventually` (singleton case)

```lean
theorem latticeDisc_mem_eventually (k : Fin 2 → ℤ) :
    ∀ᶠ R in (atTop : Filter ℝ), k ∈ latticeDisc R
```

**Witness**: `R₀ = (k 0 : ℝ)² + (k 1 : ℝ)² + 1`.

**Proof outline**: For `R ≥ R₀`:
- Nonneg sums give `R ≥ 1`, hence `|R| = R` and `R ≤ R²` (via `nlinarith`).
- Disc condition: `(k 0)² + (k 1)² ≤ R²` by `linarith` from `R ≤ R² ∧ R ≥ R₀`.
- Bounding-box condition: from `(k i)² ≤ R²` (chained from the disc bound + nonneg of the other component) get `|k i| ≤ R` via `Real.sqrt_le_sqrt` + `Real.sqrt_sq_eq_abs` + `Real.sqrt_sq hRnn`. Then `R ≤ ⌈|R|⌉` via `Int.le_ceil`, giving `|k i| ≤ ⌈|R|⌉`. The lower/upper conjuncts of `Finset.mem_Icc` follow by `exact_mod_cast` after a `linarith` chain through `le_abs_self` / `neg_abs_le`.

LOC: ~50 (proof body), 5 (signature + docstring).

### §2.2 `latticeDisc_eventually_supset` (full cofinality)

```lean
theorem latticeDisc_eventually_supset (S : Finset (Fin 2 → ℤ)) :
    ∀ᶠ R in (atTop : Filter ℝ), S ⊆ latticeDisc R
```

**Proof**: `Finset.induction_on`:
- Empty case: `Filter.Eventually.of_forall ∘ Finset.empty_subset`.
- Insert case: `filter_upwards [ih, latticeDisc_mem_eventually k]`, then split membership of `j ∈ insert k S` via `Finset.mem_insert.mp` and dispatch each case.

LOC: ~15 (proof body), 12 (signature + docstring).

**Total new LOC**: ~85 (theorems + section header docstring).

---

## §3 — Why this is safe to ship standalone

| Property | Status | Notes |
|---|---|---|
| Sorry-free | ✅ | No `sorry` in either new theorem |
| Axiom-free | ✅ | No new `axiom` declarations |
| Measure-theory-free | ✅ | Pure ℝ/ℤ arithmetic; no `Lp`, `volume`, `haarT2`, `MemLp` |
| Mathlib-stable | ✅ | Uses only `Real.sqrt_*`, `Int.le_ceil`, `Filter.eventually_atTop`, `Finset.induction_on`, `Finset.mem_filter`, `Finset.mem_Icc`, `Finset.mem_insert` — all in v4.26.0 |
| Standalone | ✅ | Independent of S2e ACT's remaining steps 1+2+4+5+6 |
| Publicly useful | ✅ | Marked as `theorem` (not `private`); can be cited by downstream slug consumers |
| Composable | ✅ | The `∀ᶠ` form composes via `filter_upwards` with future bridge steps |

The lemma is the cofinality bearer for any Plancherel-style argument that
identifies `‖S_R^{sph} f - f‖₂²` with a tail of the convergent series
`∑_k |fk|²`. The future step 4 (bridge) will produce an a.e. identification
`(S_R^{sph} f - f)(x) = ∑_{k ∉ latticeDisc R} fk · e_k(x)`; this lemma is
what reduces the right-hand `tsum` to the convergent tail.

---

## §4 — Build verification

Docker build via `./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ04OQ01`
(per CLAUDE.md's mandatory wrapper for `lake build` — direct invocation is
unsafe). Build result: ✅ **7743 jobs replayed cleanly**, single expected
warning `Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'`
(the pre-existing `sphPartialSum_L2_norm_converge` sorry, unchanged). No
new warnings from the cofinality addition.

---

## §5 — Gallery sync

`src/data/proofs/fourier-series-oq-04-oq-01/meta.json`:
- `lineCount`: 279 → 366 (synced in both top-level `leanFile` and inner `meta` blocks)
- `theoremCount`: 8 → 10
- `sorries`: 1 (unchanged)
- `axiomCount`: 1 (unchanged)
- `originalContributions`: extended with 1 entry for the cofinality
  pair + 1 entry for the S2-Gauss-real real-form bound (missed in prior
  meta-sync — corrects an `originalContributions` drift from the
  S2-Gauss-real session).
- `sections`: new `lattice-disc-cofinality` entry with `startLine: 277`,
  `endLine: 362`.

---

## §6 — S2e ACT scope reduction

| Step | Pre-S9 budget | Post-S9 budget | Status |
|---|---|---|---|
| 1 — Setup (haarT2/volume) | 3-5 LOC + 3-5 LOC contingency | unchanged | pending |
| 2 — `coeFn_finset_sum` helper | 8-10 LOC | unchanged | pending |
| 3 — Cofinality | 15-25 LOC | **0 LOC (DONE this iter)** | ✅ |
| 4 — Bridge `sphPartialSum` → Lp | 15-25 LOC | unchanged | pending |
| 5 — Cite engine | 5-10 LOC | unchanged | pending |
| 6 — Close `eLpNorm`-form | 5-10 LOC | unchanged | pending |
| **Total** | **53-90 LOC** | **38-65 LOC** | scope reduction ~30% |

The remaining S2e ACT close is now a 38-65 LOC single-iteration target
(plus 2-3 Docker iterations) — closer to a true one-shot ACT.

---

## §7 — Honest-status block

- **Mathematical progress this iteration**: 2 new theorems
  (`latticeDisc_mem_eventually`, `latticeDisc_eventually_supset`). Both
  sorry-free, axiom-free, build-verified. The cofinality bearer for the
  Plancherel-tail engine is now in place.
- **Build-verification status**: ✅ Docker-built clean at HEAD (7743 jobs,
  single expected pre-existing sorry at line 148).
- **Race disclosure**: 0 open PRs touching
  `proofs/Proofs/FourierSeriesOQ04OQ01.lean` at iteration pickup.
- **Open conjecture status**: unchanged (Carleson L²-pointwise
  convergence for 2D spherical-Fourier sums remains open;
  `carleson_2d_sph` axiom unchanged at line 132).
