# Research State: fourier-series-oq-04-oq-01

## Current State
**Phase**: ACT
**Since**: 2026-05-15 (S6 STATE-SYNC)
**Iteration**: 6

## Current Focus

S6 STATE-SYNC (researcher-9, 2026-05-15) — **doc-only post-drain
catch-up**. The S2 build-verify drain wave (PRs #19033 MERGED
2026-05-16T00:11Z + #19055 MERGED 2026-05-15T23:27Z) left state.md
with three load-bearing drift items: S2c "still build pending" (line
106), S2d "still build pending" (line 73-82), and Operational blocker
".lake symlink loop" (line 173-176) — all retired here per the
session log of PR #19033 (whose actual diff shipped only the session
file, not the state.md/JSON updates §2 listed). Bearer drift recheck
against Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
0 drift — the rev pin is unchanged since S2d PREP and the docker
build at S2-Gauss-real ACT validated the full bearer surface
(Pi.card_Icc, Int.card_Icc, Finset.prod_const, Fintype.card_fin,
.trans_eq, Finset.filter_subset, Finset.card_le_card,
Int.toNat_of_nonneg, Int.ceil_lt_add_one, pow_le_pow_left₀,
Int.ceil_nonneg). ACT-readiness gate for next-action S2e ACT
(mFourierBasis L² discharge, 70-95 LOC budget) remains GREEN: 3 PREP
chain merged (#18446 / #18545 / #18694), baseline build-verified,
operational blocker cleared. No Lean delta; no new sorries; no new
axioms.

## Previous Focus (S2-Gauss-real)

S2-Gauss-real (researcher-8, 2026-05-14) — **ACT mini-task** bridging
S2d's `Nat`-valued explicit bound to a `Real`-form analytic bound
suitable for downstream `ℓ¹`-majorisation / Plancherel estimates on
`sphPartialSum`. Adds one sorry-free, axiom-free lemma:

- `latticeDisc_card_le_real (R : ℝ) : ((latticeDisc R).card : ℝ)
                       ≤ (2 * |R| + 3) ^ 2` — composition of S2d's
  `latticeDisc_card_le_explicit` (Nat side) with the cast bridge
  `Int.toNat_of_nonneg` + `Int.ceil_lt_add_one` + `pow_le_pow_left₀`
  (monotone squaring of nonneg). The constant 4|R|² + 12|R| + 9 is the
  expanded form; the (2|R|+3)² shape is the natural closure under the
  cited Mathlib lemmas.

The bound is **qualitative** (constant 4 vs sharp π); the sharp
constant `π` (the genuine Gauss-circle problem `card ≤ ⌈π·R²⌉ + O(R)`)
requires boundary-lattice / two-squares analysis and remains deferred
(S2-Gauss-sharp, later session). This iteration ships the analytic-form
bound usable now in `sphPartialSum` `ℓ¹`-majorisation estimates,
without waiting on the harder sharp bound.

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (234 →
~286 lines, 7 → 8 theorems; +1 sorry-free lemma at the end of the
S2-Gauss block, after `latticeDisc_card_le_explicit`).

**Build status**: ✅ **build verified** (Docker, 7743 jobs, only the
expected `sphPartialSum_L2_norm_converge` sorry warning at line 148;
new lemma's `pow_le_pow_left₀` + `Int.toNat_of_nonneg` + `push_cast`
+ `linarith` proof block elaborates cleanly). Companion to researcher-9
PR #19033 (S2 build-verify, doc-only) — this PR is the first build-
verified ACT delivering new Lean content on top of the verified
baseline.

## S2d (Previous Iteration)

S2d (researcher-4, 2026-05-13) — **ACT Path A** from S2d PREP #18393
(researcher-5). Adds two sorry-free, axiom-free helper lemmas that
sharpen S2c's qualitative subset bound to a closed-form numerical
Gauss-circle upper bound:

- `bbox_card (R : ℝ) : #(Icc (fun _ => -⌈|R|⌉) (fun _ => ⌈|R|⌉))
                       = (2*⌈|R|⌉+1).toNat ^ 2` — explicit cardinality of the
  integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]² ⊂ ℤ²` via `Pi.card_Icc` (the
  product-over-Fin-2 decomposition) + `Int.card_Icc` (the 1D `@[simp]`
  formula). Proof: `rw [Pi.card_Icc] ; simp only [Int.card_Icc] ;
  have h : ... = 2⌈|R|⌉+1 := by ring ; simp [h, Finset.prod_const,
  Fintype.card_fin]` (4 tactic lines).
- `latticeDisc_card_le_explicit (R : ℝ) : (latticeDisc R).card
                       ≤ (2*⌈|R|⌉+1).toNat ^ 2` — composition of S2c's
  `latticeDisc_card_le_bbox R` with `bbox_card R` via `.trans_eq`
  (1 line; term-mode).

Combined with the trivial estimate `⌈|R|⌉ ≤ |R| + 1`, this gives
`(latticeDisc R).card = O(R²)` — the qualitative Gauss-circle bound.
The sharp constant `π` (the genuine Gauss-circle problem
`card ≤ ⌈π·R²⌉ + O(R)`) requires boundary-lattice / two-squares
analysis and remains deferred (S2e or later).

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (204 → 234
lines, 5 → 7 theorems; +2 sorry-free lemmas at the end). Gallery
meta-json line/theorem counts synced; new `lattice-disc-explicit-card`
section added (startLine 202, endLine 230); `originalContributions`
extended.

**Build status**: ✅ **build VERIFIED** (Docker, 7743 jobs, single
expected `sphPartialSum_L2_norm_converge` sorry warning at line 148)
via researcher-9 (2026-05-14, log
`.loom/logs/researcher-9-fourier-s2d-verify.log`; companion to PR
#19033 doc-only retire-qualifier, MERGED 2026-05-16T00:11Z). The
`.lake symlink loop` worktree concern was a false alarm: the Docker
wrapper mounts `/lean/.lake` inside the container and is unaffected by
the host `.lake` directory (per MEMORY.md
`feedback_researcher_build_pending_dot_lake_symlink_false_alarm`).
Both new lemmas are direct applications of stable Mathlib lemmas
(`Pi.card_Icc`, `Int.card_Icc`, `Finset.prod_const`, `Fintype.card_fin`,
`.trans_eq`) at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). The S2d PREP §2.3 medium-risk flag on the `simp` step
closing the product evaluation was discharged at build time — no
fallback to `Fin.prod_univ_succ` + `Fin.prod_univ_zero` was needed;
the inline `simp` was specific enough.

## S2c (Previous Iteration)

S2c (researcher-1, 2026-05-12) — **ACT parallel mini-task** adding two
sorry-free helper lemmas advancing the Gauss-circle prep noted in the
S2a state.md:

- `latticeDisc_subset_bbox` — the lattice disc is a subset of the integer
  bounding box `[-⌈|R|⌉, ⌈|R|⌉]²` (1-line proof, `Finset.filter_subset`).
- `latticeDisc_card_le_bbox` — corollary cardinality bound
  (`Finset.card_le_card`).

These give the trivial pre-Gauss bound `(latticeDisc R).card ≤ (2·⌈|R|⌉+1)²`
once the bounding-box cardinality is unfolded — useful for crude ℓ¹
majorisation of the spherical partial sum. The sharper Gauss-circle bound
`card ≤ ⌈π·R²⌉ + O(R)` is deferred to S2d.

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 → 204
lines, 3 → 5 theorems; +2 sorry-free lemmas at the end). Gallery
meta-json line/theorem counts synced; new "lattice-disc-bbox" section
added; sanity-checks section line range corrected to 162-175 (was
167-178 after S2a's section-numbering drift).

**Build status**: ✅ **build VERIFIED** (transitively via the S2d
`latticeDisc_card_le_explicit` Docker run, which depends on these
S2c lemmas — `latticeDisc_subset_bbox` + `latticeDisc_card_le_bbox` —
and was confirmed clean by researcher-9, 2026-05-14, 7743 jobs).
Both proofs are direct applications of stable Mathlib lemmas
(`Finset.filter_subset`, `Finset.card_le_card`); the `.lake symlink
loop` worktree concern cited at original push time was a false alarm
(Docker wrapper mounts `/lean/.lake` inside the container, isolated
from host).

Earlier (S2a, researcher-8): ACT scaffold for the 2D Carleson
spherical-summation conjecture (axiomatized) + unconditional
L²-norm-convergence companion (sorried) + gallery entry.

Deliverables in this iteration:
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 lines) — rigorous defs
  (`T2`, `haarT2`, `multiFourierCoeff`, `latticeDisc`, `sphPartialSum`),
  1 axiom (`carleson_2d_sph`), 1 sorried companion theorem
  (`sphPartialSum_L2_norm_converge`), 2 definitional sanity-check lemmas.
- `proofs/Proofs.lean` — register new file in the umbrella.
- `src/data/proofs/fourier-series-oq-04-oq-01/{meta.json,index.ts,annotations.json}`
  — gallery entry, `status: "axiomatized"`, `badge: "axiom"`,
  `sorries: 1`, `axiomCount: 1`.

The S1 OBSERVE spec (state.md from PR #18062) was followed verbatim:
`T2 := Fin 2 → AddCircle 1`, `multiFourierCoeff` as iterated integral with
`fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1)` characters, `latticeDisc`
as a `Finset.Icc` bounding box filtered by the disc inequality, and the
`carleson_2d_sph` axiom with `MemLp f 2 haarT2` and `Tendsto ... atTop`.

**Build status**: This worktree's `proofs/.lake` symlink is recursive
(known infrastructure issue; ~25 minute fresh Mathlib clone needed for
docker build), so the file is pushed as **build pending** per the
gallery's standard convention for newly-introduced files. The
sanity-check lemmas (`multiFourierCoeff_zero`, `sphPartialSum_zero`)
are intentionally short and should compile cleanly; the companion theorem
`sphPartialSum_L2_norm_converge` is `sorry`d so a build failure there
would be a definitional / type-signature issue rather than a missing
lemma.

## Active Approach

**Axiomatize the open conjecture; formalize the partial results that are
provable unconditionally.**

The structural pattern matches sibling axiomatized open-problem entries
(`fourier-series-oq-01` for the 1D analogue with `carleson_hunt_maximal`
as a single axiom). Per the gallery's Axiom Integrity Policy, the entry
uses `status: "axiomatized"` with `badge: "axiom"` (never `"verified"`)
and reports `axiomCount: 1, sorries: 1` honestly.

## Blockers

**Mathlib gaps (carryover from S1):**
1. No named `Plancherel_ntorus` identity exposed in Mathlib (the
   orthonormal-basis tensor-product on `lp 2` exists but is implicit).
   This blocks closing the `sphPartialSum_L2_norm_converge` sorry. Future
   contribution target: ~30-50 line Mathlib PR.
2. No `Bochner-Riesz` / `ballMultiplier` API. Required for the regularised
   $\delta > 1/2$ a.e. convergence (Stein 1958) — see S2b plan.

**Operational:** None active. (Earlier S2a–S2d sessions cited a
worktree `proofs/.lake` symlink loop concern — confirmed false alarm
at S2 build-verify, MERGED 2026-05-16T00:11Z PR #19033: the Docker
wrapper mounts `/lean/.lake` inside the container, isolated from
host. ~5 min wall-clock from cold worktree on Azure cache hit.)

## Next Action

**S2b (any researcher) — ACT, slower**: Formalise Bochner–Riesz a.e.
convergence for $\delta > 1/2$ in $n=2$ (Stein 1958). This is a real
theorem to formalise, not a placeholder. Estimated 300–500 Lean lines;
likely 2–3 iterations. The proof goes through:
1. Define `bochnerRieszMultiplier δ R k := max (1 - |k|²/R²) 0 ^ δ`.
2. Define `bochnerRieszPartialSum f R δ x := ∑ k, multiFourierCoeff f k * bochnerRieszMultiplier δ R k * fourier (k 0) (x 0) * fourier (k 1) (x 1)`.
3. State the kernel decomposition: `bochnerRieszPartialSum f R δ x = (K_R^δ * f)(x)` where `K_R^δ` is a smooth kernel with $L^1$ bound $\le C_\delta$.
4. A.e. convergence for $\delta > 1/2$ via the Hardy–Littlewood maximal
   function (Stein 1958 argument).

**Alternative S2b**: Close the L²-norm sorry in
`sphPartialSum_L2_norm_converge` directly by building the
`Plancherel_ntorus` identity in this file (not Mathlib), specialised to
$n=2$. Cleaner and self-contained, and the result is a candidate for a
future Mathlib contribution. Estimated 80–150 lines.

**S2d (Path A — DONE at this iteration)**: `bbox_card` +
`latticeDisc_card_le_explicit` (sorry-free, axiom-free, ~17 LOC). The
explicit closed-form `(2⌈|R|⌉+1)²` cardinality bound is now in the
file. Combined with `⌈|R|⌉ ≤ |R|+1`, this gives `O(R²)`. The remaining
"sharp constant `π`" Gauss-circle problem proper — `card ≤ ⌈π·R²⌉ +
O(R)` — still requires boundary-lattice / two-squares analysis (S2e
or later, estimated 30–60 Lean lines).

**S2e (audit chain complete; ACT pending)**: The mFourierBasis-based
discharge of the `sphPartialSum_L2_norm_converge` sorry, with the
70–95 LOC budget refined across S2e PREP (#18446) → S2f PREP (#18545,
volume/haarT2 errata) → S2g PREP (Lp coeFn finset-sum + cofinality +
eLpNorm bridge). Three concrete Mathlib gaps documented; either build
`Lp.coeFn_finset_sum` inline (~10 LOC) or refactor at the MemLp level.
Needs docker build verification.

## Earlier Focus

S2a (researcher-8, 2026-05-12) — ACT scaffold (PR #18165 merged). Created
`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 lines) with rigorous
defs, 1 axiom (`carleson_2d_sph`), 1 sorried companion theorem
(`sphPartialSum_L2_norm_converge`), 2 sanity-check lemmas. Gallery entry
registered with `status: axiomatized`, `badge: axiom`, `sorries: 1`,
`axiomCount: 1`.

S1 (researcher-6, 2026-05-12) — OBSERVE survey. Doc-only (PR #18062
merged). See archived state.md in PR #18062 for the full S1 plan.
