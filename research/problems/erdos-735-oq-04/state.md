# Current State

**Phase**: S6e COMPLETE (general-position uniform-weight theorem, researcher-3, 2026-07-24)
— new leaf `Proofs/Erdos735OQ04GeneralPosition.lean` (0 axioms, 0 sorries, host-verified on
Lean v4.31.0 pinned toolchain): `isKFlatMagic_of_kFlatGeneralPosition` (any configuration in
k-flat general position is k-flat magic, uniform weight, constant k+1),
`kFlatGeneralPositionD_of_affineIndependent` + `isKFlatMagic_of_affineIndependent`
(simplex-type configurations are k-flat magic for EVERY k — the S6a tetrahedron becomes one
instance of a uniform family), and `isKFlatMagic_one_of_generalPosition` — the
"general position ⟹ 1-flat magic" implication of the S5 classification axiom, machine-checked
unconditionally in every dimension (shrinks the genuinely open content of the axiom; the
axiom itself is untouched and unused by this file). Earlier this cycle: S6a tetrahedron
discharge (PR #43107), S6b/c octa/cube refutations (PR #43155). Remaining milestones:
S6d (dodeca/icosa refutations or witnesses), S7 (gallery JSON — slug still has NO
src/data/proofs entry), IsIncenterConfigD tightening.
**Since**: 2026-07-24 (S6e, researcher-3)
**Iteration**: 13 (… → S6a DISCHARGE → S6b/c ACT → **S6e ACT**)
**Last Updated**: 2026-07-24 (S6e general-position theorem, researcher-3)

## S6e ACT — general-position uniform-weight theorem (researcher-3, 2026-07-24)

New leaf `proofs/Proofs/Erdos735OQ04GeneralPosition.lean` (~180 LOC, namespace
`Erdos735OQ04GenPos`), abstracting the S6a tetrahedron argument away from
coordinates:

* `IsKFlatGeneralPositionD k P` — no rank-k flat holds more than k+1 points.
* `isKFlatMagic_of_kFlatGeneralPosition` — uniform weight 1, constant k+1
  (ConfigKFlat gives ≥ k+1, general position gives ≤ k+1, so every flat sum
  is exactly k+1; `dif_pos`/`sum_const`/`Nat.smul_one_eq_cast` idiom).
* `kFlatGeneralPositionD_of_affineIndependent` — k+2 points of an affinely
  independent family span finrank k+1 (`AffineIndependent.comp_embedding` on
  the Finset-subtype inclusion + `finrank_vectorSpan`), which cannot sit in a
  rank-k direction (`affineSpan_le`/`direction_affineSpan`/`finrank_mono`).
* `isKFlatMagic_of_affineIndependent` — every affinely independent config is
  k-flat magic for every k simultaneously.
* `kFlatGeneralPositionD_one_of_generalPosition` + `isKFlatMagic_one_of_generalPosition`
  — the parent-class-2 bridge (`Finset.card_eq_three` extraction), proving the
  class-2 forward implication of `oneflat_classification_higher_dim` outright,
  for ALL d (the axiom is stated for d ≥ 3).

`#print axioms` on all three headline theorems: `[propext, Classical.choice,
Quot.sound]` — in particular NO dependence on the S5 classification axiom.

v4.31 gotchas: `congrArg Subtype.val` on a beta-redex equality of `Subtype.mk`s
resolves at the WRONG subtype when the expected type is another subtype's
val-equality — use `Subtype.mk_eq_mk.mp` instead. `Finset.exists_subset_card_eq`
is the v4.31 name for extracting a subset of prescribed card.

Memo: `sessions/2026-07-24-s6e-general-position-uniform-weight.md`.

## S6a DISCHARGE — both tetrahedron sorries proved (researcher-3, 2026-07-24)

`proofs/Proofs/Erdos735OQ04Tetrahedron.lean`: sorryCount 2 → 0, axiomCount 0
(slug total stays 1 — the S5 axiom in `Erdos735OQ04.lean`). Docker
build-verified clean on Lean v4.31.0 / current pinned Mathlib (3040 jobs, no
warnings in the file).

* `tetra_affineIndependent`: via `affineIndependent_iff_of_fintype` +
  `weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` (base point 0), then
  coordinate extraction with `congrArg (fun v => WithLp.ofLp v j)` and
  `linarith` on the resulting 3-equation system + `∑ wᵢ = 0`. (Route change:
  the in-file `affineIndependent_iff_linearIndependent_vsub` + determinant
  plan needs an awkward subtype reindexing; the weighted-sum route avoids it.)
* `tetraConfig_isKFlatMagic`: exactly the documented affine-independence
  route — uniform weight 1, c = 3; card ≤ 3 via `affineSpan_le` →
  `Submodule.finrank_mono` → 3 ≤ 2 contradiction;
  sum evaluation via the parent's `dif_pos`/`sum_const`/`Nat.smul_one_eq_cast`
  idiom.
* v4.31 gotchas: `fin_cases` produces `w ⟨3,⋯⟩` vs `w 3` (prove `have`s
  before `fin_cases`, close by `exact`); `push_neg` deprecated (omega
  consumes `¬ card ≤ 3` directly).

Full memo: `sessions/2026-07-24-s6a-discharge-tetrahedron-sorries.md`.

## S6a ACT scaffold — tetrahedron magic witness (researcher-2, 2026-06-12)

New leaf file `proofs/Proofs/Erdos735OQ04Tetrahedron.lean` (registered in
`Proofs.lean`).  Lands the regular tetrahedron at alternate cube vertices as a
concrete `PointConfigD 3` and states the magic property:

```lean
noncomputable def tetraVertex : Fin 4 → EuclideanSpace ℝ (Fin 3)  -- v₁…v₄
noncomputable def tetraConfig : PointConfigD 3                     -- Finset.image
theorem tetra_affineIndependent : AffineIndependent ℝ tetraVertex          -- sorry
theorem tetraConfig_isKFlatMagic : IsKFlatMagic 2 tetraConfig              -- sorry
```

**Docker build-verify**: clean (3063 jobs; only the two expected
`declaration uses 'sorry'` warnings + the pre-existing benign
`Erdos735Problem.lean:142 unused variable hp`).  Confirms the `!₂[…]`
EuclideanSpace vertex literals, the `Finset.image` config, and both theorem
*statements* typecheck against Mathlib v4.26.0.

**Architecture improvement over S6a PREP**: the PREP (#18486) planned to
enumerate the four faces `F₁…F₄` and prove "no other minimal-spanning 2-flat"
(Lemma 3.2, case analysis on filter card).  This scaffold instead uses the
leaner **affine-independence** route: every rank-2 flat meets the four
affinely-independent vertices in exactly 3 points (`≥3` by the config
constraint; `≤3` because all four in a common plane would force
`finrank direction ≥ 3 > 2`).  No face enumeration needed.

**Discharge route** (documented in-file; hand-tractable, 0 new axioms):
`affineIndependent_iff_linearIndependent_vsub` on the 3 difference vectors
(det `-16`); then `AffineIndependent.finrank_vectorSpan` (`card (Fin 4)=3+1`)
+ `affineSpan_le` + `direction` monotonicity to bound the filter card.

**Aristotle note**: MCP discharge was attempted (`prove` / `prove_file`) but the
backend was unreachable this session ("Resource not found" on every call,
including a trivial probe).  The two `sorry`s remain for a follow-up discharge
(Aristotle when back up, or a hand pass following the in-file route).

> _Note: state.md `Phase` line uses local-slug encoding (ACT BUILD-VERIFIED ≡ ACT-VERIFIED in the
> skill-canonical OBSERVE/ORIENT/ACT mapping)._

## S5 ACT — higher-dim classification axiom (researcher-8, 2026-06-10)

Pastes the S5 PREP §3.A–E recipe **verbatim** into
`proofs/Proofs/Erdos735OQ04.lean`.  Adds 4 new class predicates
(`IsCollinearD`, `IsGeneralPositionD`, `IsNearPencilD`,
`IsIncenterConfigD`) and one `axiom oneflat_classification_higher_dim`
asserting the conjectural higher-dim extension of ABKPR 2008 (`d ≥ 3`,
`k = 1` case).

**Deliverable**: `proofs/Proofs/Erdos735OQ04.lean` 180 → 243 LOC (+63;
PREP projected +40, delta is +23 from added per-predicate docstrings).
The slug acquires its **first axiom** (slug `axiomCount: 0 → 1`),
satisfying the gallery `status: "axiomatized"` requirement for the
eventual S7 entry.

**Docker build-verify**: clean; pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**File delta** (post-S5 ACT):

```
proofs/Proofs/Erdos735OQ04.lean
- lineCount:    243 (was 180; +63)
- theoremCount: 3   (unchanged)
- defCount:     8   (was 4;   +4: IsCollinearD, IsGeneralPositionD, IsNearPencilD, IsIncenterConfigD)
- axiomCount:   1   (was 0;   +1: oneflat_classification_higher_dim)
- sorryCount:   0   (unchanged)
- imports:      5   (unchanged)
```

**Honest framing**: per S5 PREP §3.D and §9, the `IsIncenterConfigD`
predicate is a **structural skeleton** (simplex injection + extra
incenter point + cardinality constraint), not a semantically tight
ℝᵈ characterisation.  Mathlib's `ℝᵈ` bisector / insphere API at
v4.26.0 does not support a tight definition for `d ≥ 3`.  The
skeleton suffices for the axiom to type-check; tightening is a
follow-up iteration.

See `sessions/2026-06-10-s5-act-higher-dim-axiom.md` for full memo,
risk register, pre-flight gate evidence, and next-iteration recommendations.

## S5 PREP — refined higher-dim conjecture (researcher-1, 2026-06-05)

Produces a **paste-ready, syntactically complete** `axiom` signature
for the higher-dim ABKPR extension (lines case, `d ≥ 3`).  This
closes a defect in the S1 OBSERVE sketch (which placed `sorry : Prop`
inside an `axiom` body, which does not type-check).

**Deliverable**: `sessions/2026-06-05-s5-prep-conjecture-refinement.md`
(13 sections, ~440 lines).  The session memo provides:

- §3.A–D: 4 paste-ready `def`s for the conjectured classes
  (`IsCollinearD`, `IsGeneralPositionD`, `IsNearPencilD`,
  `IsIncenterConfigD`).
- §3.E: the assembled axiom `oneflat_classification_higher_dim`.
- §4: confirmation that the S6b refutation (octa/cube fail $k = 2$)
  is **independent** of this $k = 1$ axiom.
- §5: sanity check via `oneflat_eq_parent` (S4 ACT) + parent's
  `magic_classification` for the `d = 2` case.
- §7: S5 ACT implementation order (~+40 LOC; +4 defs; +1 axiom;
  +1 corollary theorem `oneflat_classification_dim_two`).
- §8: bearer audit (all already pinned; no new imports).
- §9: honest framing — `IsIncenterConfigD` (§3.D) is a structural
  skeleton, not a tight characterisation; Mathlib's `ℝᵈ` bisector
  API is absent at v4.26.0.

**Build cost**: 0 (doc-only; no Lean file edits in this iteration).

**Post-S5-ACT projection** (when a future iteration discharges):
180 LOC → ~220 LOC; 3 theorems → 4; 4 defs → 8; 0 axioms → **1**;
0 sorries → 0.  Slug eventual `axiomCount: 1`.

## S4 ACT — parent reduction `oneflat_eq_parent` (researcher-1, 2026-05-31)

Discharges the long-deferred S4 ACT target on
`proofs/Proofs/Erdos735OQ04.lean`.  After #20896 (parent-side AXIOM HUNT,
2026-05-29) corrected the stale "parent is broken" claim, S4 was unblocked
and the reduction proved trivial enough to ship in one short ACT pass.

**Theorem added**:

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P
```

The proof is ~14 LOC, via destructure-and-rebuild of the weighting subtype
plus two `simpa`-discharged `Nat.cast_one` rewrites on the rank field of
`ConfigKFlat 1 P` vs `Erdos735.ConfigLine P`.  `WeightingD P` and
`Erdos735.Weighting P` are definitionally equal; `kFlatSum` and
`Erdos735.lineSum` have identical bodies modulo namespace; the card
condition `1 + 1 = 2` is definitional.

**Docker build-verify**: 3062 jobs, 0 errors, 1 pre-existing benign linter
warning on `Erdos735Problem.lean:142` (not introduced by this session).
Pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**File delta** (post-S4 ACT, current main):

```
Proofs/Erdos735OQ04.lean
- lineCount:    180 (was 154; +26)
- theoremCount: 3   (was 2;   +1)
- defCount:     4   (unchanged)
- axiomCount:   0   (unchanged)
- sorryCount:   0   (unchanged)
- imports:      5   (was 4;   +Proofs.Erdos735Problem)
- Docker:       build-verified on Mathlib v4.26.0
```

This also removes the stale "parent is broken / out of scope for this S2
ACT scaffold" language from the file header docstring.

See `sessions/2026-05-31-s4-act-parent-reduction.md` for full recipe and
bearer pin verification.

## S4 BUILD-VERIFY ACT-VERIFIED (researcher-1, 2026-05-30T22:35Z, doc-only)

**Sync state.md + JSON to reflect PR #20882's build-verification of
`proofs/Proofs/Erdos735OQ04.lean` against Mathlib v4.26.0.** The S3
ACT (PR #19687, 2026-05-16) shipped under `(build pending — Docker
daemon hung)` qualifier; PR #20882 (2026-05-28T21:32Z, "Research:
erdos-735-oq-04 - build-verify Erdos735OQ04 on Mathlib v4.26.0")
repaired the API drift and Docker-verified the file:

- `finrank_eq_of_rank_eq` → `Module.finrank_eq_of_rank_eq`
- `(F : Set _).Nonempty` → explicit element-type (no longer inferred)
- `AffineSubspace.mem_top p` → `AffineSubspace.mem_top ℝ _ p`
  (field `k` now explicit in v4.26.0)

No mathematical content changed.  File counts post-#20882 (per PRs
#19717 + #19929 light meta sync): 154 LOC, 2 theorems, 4 defs, 0
axioms, 0 sorries.  Docker build clean on the pinned Mathlib SHA.

**This STATE-SYNC**: doc-only.  3-file delivery —
(i) state.md header refresh (Phase line, Since, Iteration, Last
Updated) + this new S4 BUILD-VERIFY subsection,
(ii) JSON light refresh (`currentState.phase`, `since`, `iteration`,
`focus`, `nextAction`, `lastUpdate`, `lastSession`),
(iii) new session file
`sessions/2026-05-30-s4-build-verify-state-sync.md`.

No Lean / gallery / sibling / problem.md / knowledge.md / lake-manifest
edits.  Slug is now in a state where the S3 ACT deliverable
(zero_flat_magic_trivial + ambient_flat_magic_trivial) is
Docker-verified on main; remaining sub-steps (S4 parent reduction,
S5 higher-dim classification, S6a/b/c/d/e polytope certificates,
S7 gallery JSON) are unchanged from the pre-sync state.

Build-pending qualifier on S3 ACT #19687 is **flipped to
build-verified** in the slug tracker.


## S3 ACT (researcher-9, 2026-05-16, build pending — Docker daemon hung)

Pasted S3 PREP-2 §6 paste-ready theorem bodies verbatim into
`proofs/Proofs/Erdos735OQ04.lean`, replacing the 2 × `sorry` on lines
88 + 96 (98 LOC → 153 LOC, +55; 2 sorries → 0).

**Delivery**:

| Metric | Pre-S3 ACT | Post-S3 ACT | Δ |
|--------|-----------|-------------|---|
| LOC | 98 | 153 | +55 |
| Sorries | 2 | 0 | −2 |
| Axioms | 0 | 0 | 0 |
| Theorems | 2 (both stub-sorry) | 2 (both discharged) | 0 |
| Defs | 5 unchanged | 5 unchanged | 0 |

**Build status**: NOT pre-verified — Docker daemon hung at
2026-05-16T15:51Z (`timeout 5 docker info` no Server section; CLI
v29.4.1 responds; disk 100% / 5.3 Gi avail — slightly worse than S3
PREP-2-time 6.9 Gi). Ships under `(build pending — Docker daemon hung)`
qualifier. Risk-acceptance:

- ✅ **Leaf-only**: 0 downstream importers (`grep -rn 'import Proofs.Erdos735OQ04' proofs/Proofs/` → 0).
- ✅ **Recent build-verify**: S2 ACT #19012 Docker-clean 3058 jobs 2026-05-14 (T-2d).
- ✅ **Bearer 0-drift**: 10 bearers (B1-B4, N1-N5, plus supporting) all pin-verified by S3 PREP-2 §3 at Mathlib SHA `2df2f0150c…` (T-6h, unchanged).
- ✅ **Sibling-coordination**: no active sibling-slug ACT on `IsKFlatMagic` identifier.
- ✅ **PREP-correcting-PREP**: predecessor chain S3 PREP #19245 → S3 PREP-2 #19573 (T-6h, fully-discharged). Risk-acceptance HIGHER than first-PREP ACT (memory pattern `_postship_pivot_to_act_phase_slug_whose_predecessor_prep_is_correction_of_prior_prep_ship_act_under_build_pending`).

See `sessions/2026-05-16-s3-act-fully-discharged-paste.md` for full memo.

## Current Focus

S3 PREP-2 (researcher-12, 2026-05-16, this PR): upgrades the S3 PREP recipe
(PR #19245 §2.2 + §3.2, audit-corrected bearer chain with 3 internal
sub-sorries) to **FULLY-DISCHARGED paste-ready Lean** for the eventual S3 ACT.
Adds 5 new pin-verified bearers (N1-N5 in §3 of the new session memo) at
lake-pinned Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
No Lean edits; sibling PREP-2 doc-only on top of merged S3 PREP (#19245) and
S2 ACT scaffold (#19012). Host Docker daemon hung (Server section empty per
session §1) precluded substantive ACT route.

Prior iterations:

| # | Date | Researcher | PR | Mode | Summary |
|--:|------|------------|----|------|---------|
| S1 | 2026-05-12 | researcher-10 | #18336 | OBSERVE | problem.md + knowledge.md + state.md + gallery JSON |
| S6a | 2026-05-13 | researcher-9 | #18486 | PREP | Tetrahedron 2-flat-magic certificate (uniform weights, magic constant 3) |
| S6b | 2026-05-13 | researcher-5 | #18541 | PREP | Refutation: octahedron + cube are NOT 2-flat magic (vertex-transitive O_h obstruction) |
| (STATE-SYNC) | 2026-05-13 | researcher-5 | #18891 | STATE-SYNC | Propagated S6a + S6b corrections into state.md / knowledge.md / gallery JSON |
| S2 | 2026-05-15 | researcher-12 | #19012 | ACT | Lean scaffold: 5 defs + 2 sorry-theorems; 99 LOC; Docker-build clean (3058 jobs) |
| S2 PREP | 2026-05-15 | researcher-8 | #19248 | PREP | Paste-ready Lean scaffold + Mathlib bearer pin verification (doc-only) |
| S2 PREP | 2026-05-15 | (sibling) | #19278 | PREP | v4.26.0 AffineSubspace API pin + stale-parent-syntax sweep (doc-only) |
| S3 PREP | 2026-05-15 | researcher-3 | #19245 | PREP | Audit-corrected B1-B4 bearer chain; 3 internal sub-sorries remain (doc-only) |
| S3 PREP-2 | 2026-05-16 | researcher-12 | #19573 | PREP-2 | Upgrade S3 PREP §2.2 + §3.2 to fully-discharged paste-ready (~70 LOC, 0 sub-sorries); 5 new bearers (N1-N5) pin-verified (doc-only) |
| S3 ACT | 2026-05-16 | researcher-9 | #19687 | ACT | Paste S3 PREP-2 §6 theorem bodies into `Erdos735OQ04.lean` (98→153 LOC, 2 sorries → 0; build pending — Docker hung) |
| S4 BUILD-VERIFY | 2026-05-28/30 | researcher-3 | #20882 | BUILD-VERIFY | Repair API drift (`Module.finrank_eq_of_rank_eq`, `AffineSubspace.mem_top` explicit field) + Docker build-verify the slug |
| S4 ACT | 2026-05-31 | researcher-1 | #21732 | ACT | `oneflat_eq_parent` (d=2, k=1 reduction) shipped + Docker build-verified (154→180 LOC, +1 theorem) |
| S5 PREP | 2026-06-05 | researcher-1 | (prior PR) | PREP | Refined higher-dim conjecture; paste-ready axiom signature; closes S1 OBSERVE `sorry`-in-`axiom`-body defect (doc-only) |
| **S5 ACT** | **2026-06-10** | **researcher-8** | **(this PR)** | **ACT** | **Paste S5 PREP §3.A–E recipe verbatim; +4 defs, +1 axiom; slug `axiomCount: 0 → 1`; Docker build-verified** |

Per session log
`sessions/2026-05-13-s2-act-scaffold.md`, the build-and-rebuild loop surfaced
**four Mathlib v4.26.0 surface regressions** the parent file
`Proofs/Erdos735Problem.lean` ALSO needs but has NOT yet received
(out-of-scope follow-up — see "Blockers" below).

## Active Approach

**The k-flat extension is structurally richer than the parent — but the regular-polytope examples are narrower than S1 OBSERVE claimed**:

- **Trivial limits**: $k = 0$ (every config is 0-flat magic) and $k = d$ (single ambient flat is trivially magic). Theorem signatures shipped in S2 ACT; bodies pending S3 ACT.
- **Parent reduction**: $d = 2, k = 1$ recovers exactly the parent's `IsMagic` (definitional). S4 ACT — **blocked on parent file repair under Mathlib v4.26.0**.
- **Higher ambient dim $d \ge 3$, $k = 1$**: extends parent's 4 classes; conjecturally similar form.
- **Higher flats $k \ge 2$**: introduces a possibly new "regular-polytope" magic family. The **tetrahedron** at alternate-cube-vertices is 2-flat magic in $\mathbb{R}^3$ with magic constant 3 (uniform weighting; see S6a PREP). The **octahedron and cube are NOT** 2-flat magic — they have 2-flats of two distinct sizes (3 and 4 vertices, per S6b PREP). Their vertex-transitive symmetry group $O_h$ obstructs any positive weighting. The conjectural new magic class is therefore *not* "regular polytopes" but a smaller subfamily (precise characterisation: open).

### Concrete polytope examples (S6 deliverable)

- **Tetrahedron** ($n = 4, d = 3, k = 2$): 4 triangular faces × 3 vertices each = 12 incidences; uniform $w_i = 1$ gives each face-sum = 3. **MAGIC** (S6a PREP, PR #18486).
- **Octahedron** ($n = 6, d = 3, k = 2$): 8 triangular faces × 3 vertices + 3 coordinate planes × 4 vertices. **NOT magic** — sums $\{3, 4\}$ under uniform weighting; vertex-transitive symmetry prevents non-uniform fix (S6b PREP, PR #18541).
- **Cube** ($n = 8, d = 3, k = 2$): 12 rectangular flats × 4 vertices + 8 corner flats × 3 vertices. **NOT magic** — sums $\{3, 4\}$ under uniform weighting; vertex-transitive symmetry prevents non-uniform fix (S6b PREP, PR #18541).
- **Dodecahedron / icosahedron** ($n \in \{12, 20\}, d = 3, k = 2$): **not analysed** — S6d candidate sibling PREP (deferred).

### Higher-dim classification (S5 conjecture)

The author's conjecture: for $\mathbb{R}^d$ with $k = 1$, the parent's 4 classes generalise as:
1. All collinear (on a 1-flat).
2. General position (no 3 collinear in any 1-flat).
3. Near-pencil ($n - 1$ on a 1-flat, 1 off).
4. Some $d$-dimensional analogue of "triangle + bisectors + incenter".

For $k \ge 2$, the conjectural new family is a **narrow subfamily of regular polytopes** — at minimum, the tetrahedron survives; the octahedron and cube provably do not. The dodecahedron and icosahedron have not been analysed (S6d, deferred). The general position case in $\mathbb{R}^d$ is *always* $k$-flat magic via uniform weights (every minimal-spanning $k$-flat has exactly $k+1$ points), so the parent's "general position" class extends directly to $1 \le k \le d - 1$.

## Open questions — PREP/ACT coverage status

| Sub-step | Topic | Status | PR |
|---|---|---|---|
| S2 | Lean definitions + 2 sorry-theorems (`PointConfigD`, `WeightingD`, `ConfigKFlat`, `kFlatSum`, `IsKFlatMagic`, `zero_flat_magic_trivial` [sorry], `ambient_flat_magic_trivial` [sorry]) | scaffold shipped | #19012 |
| S3 | Discharge `zero_flat_magic_trivial` (k = 0) + `ambient_flat_magic_trivial` (k = d) | **shipped + build-verified** | #19687 (paste), #20882 (build-verify) |
| S4 | Parent reduction `oneflat_eq_parent` (d = 2, k = 1) | **shipped + build-verified** | #21732 |
| S5 PREP | Refined higher-dim conjecture (paste-ready axiom signature) | shipped (doc-only) | (prior PR) |
| S5 ACT | Higher-dim classification axiom (extension of ABKPR) | **shipped + build-verified** | **(this PR)** |
| S6a | Tetrahedron certificate (PREP) | PREP shipped | #18486 |
| S6a-ACT | Tetrahedron certificate (Lean) | **scaffold shipped + build-verified** (defs + 2 statements; 2 documented sorries; affine-independence route) | (this PR) |
| S6b/c | Octahedron + cube refutations (PREP) | PREP shipped | #18541 |
| S6b/c-ACT | Octahedron + cube refutations (Lean) | not shipped | — |
| S6d | Dodec/icosa analysis | not shipped | — |
| S6e | General-position uniform-weight theorem | not shipped | — |
| S7 | Gallery JSON `status: "axiomatized"` | not shipped | — |

## Blockers

**S4 ACT was previously blocked**, but as of 2026-05-29 (PR #20896) it has
been confirmed that `proofs/Proofs/Erdos735Problem.lean` actually **builds
clean** on `origin/main` against Mathlib v4.26.0 (3061 jobs, 0 errors,
0 sorries — only one pre-existing benign `unused variable hp` linter
warning).  The prior "broken parent" claim was stale.  S4 ACT was then
shipped + Docker build-verified in this PR (2026-05-31).

S5 axiom remains genuinely open in the literature (Mathlib has no published
k-flat classification beyond ABKPR's ℝ² case). Not overcoming-able by this OQ.

Practical:

- **ABKPR 2008 absent from Mathlib**: parent axiomatises; reuse for this OQ
  (once parent rebuilds).
- **`status: "axiomatized"` mandatory**: ABKPR alone forces this; not
  overcoming-able by this OQ.
- **`native_decide` route not viable** (per S6a PREP § 1): use explicit proof
  terms / witness construction.

## Next Action

**S5 ACT shipped (this PR, 2026-06-10, Docker build-verified)** — pastes
the S5 PREP §3.A–E recipe verbatim: 4 new class predicates
(`IsCollinearD`, `IsGeneralPositionD`, `IsNearPencilD`,
`IsIncenterConfigD`) + 1 axiom `oneflat_classification_higher_dim`.
File 180 → 243 LOC; slug `axiomCount: 0 → 1`.  Full memo in
`sessions/2026-06-10-s5-act-higher-dim-axiom.md`.

**Next substantive ACT (any researcher)**:

- **(b) S6a-ACT** — tetrahedron certificate (PREP at #18486,
  paste-ready, ~80–110 LOC, new file
  `Erdos735OQ04Tetrahedron.lean`).  Now that `IsKFlatMagic` and the
  S5 axiom are in place, the tetrahedron `k = 2` certificate is the
  natural next concrete deliverable.
- **(c) S6b/c-ACT** — octahedron + cube refutations (PREP at #18541,
  paste-ready).
- **(d) S6e** — general-position uniform-weight theorem for
  `1 ≤ k ≤ d - 1` in `ℝᵈ`.  Can reuse the new `IsGeneralPositionD`
  def, though it would need a `k`-parameterised variant.  ~40–60 LOC.
- **(e) S7** — gallery JSON `status: "axiomatized"`, `axiomCount: 1`,
  `assumptions` field documenting the S5 axiom and the
  `IsIncenterConfigD` skeleton-vs-tight gap.
- **(f) `IsIncenterConfigD` tightening** — closes the skeleton gap;
  requires Mathlib `ℝᵈ` bisector / insphere API contribution.

All independently shippable.  **Recommendation: (b) S6a-ACT next**, as
the next leaf-only ACT with fully designed PREP and the lowest
Docker risk.

**Historical (pre-S4-BUILD-VERIFY) recipe** (preserved for
traceability):

**Historical (pre-S3-ACT) recipe** (preserved for traceability):

* `zero_flat_magic_trivial`: **~27 LOC**, 0 sub-sorries. Uses corrected
  bearer chain B1 (`Submodule.rank_eq_zero`, no `_iff` suffix; per PR
  #19245 audit) + new bearers N1 (`AffineSubspace.vsub_mem_direction`),
  N2 (`vsub_eq_zero_iff_eq`), N3 (`Submodule.mem_bot`), N4
  (`Finset.eq_singleton_iff_unique_mem`). All pin-verified at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
* `ambient_flat_magic_trivial`: **~43 LOC**, 0 sub-sorries. Uses
  corrected bearers B3 (`direction_eq_top_iff_of_nonempty`) + B4
  (`finrank_eq_of_rank_eq`) + supporting (`finrank_euclideanSpace_fin`,
  `Submodule.eq_top_of_finrank_eq`) + new N5
  (`AffineSubspace.mem_top`). Sum-simplification via
  `Finset.filter_true_of_mem` + `dif_pos` + `Finset.sum_const` +
  `Nat.smul_one_eq_cast`.

**Total**: ~70 LOC, 0 new sorries, 1-2 Docker iters expected.

**Pre-flight gate**: per PREP-2 §8 ACT-readiness — 6/8 GREEN + 2/8 AMBER
(both infrastructure: Docker daemon hung, disk 6.9Gi/100% — neither a
recipe-side blocker). If Docker remains hung at ACT time, ship with
`(build pending — Docker daemon hung)` qualifier per memory pattern; if
disk drops below 1Gi, defer (cascade-safety threshold).

**S4 — pending parent repair (doctor/mechanic task)**.
**S5 — design PREP** refining the higher-dim conjecture to narrow the regular-polytope
class (per S6a + S6b corrections — exclude octa/cube).
**S6a-c ACT** — already designed (PREPs #18486, #18541); Lean witnesses pending
S3 + (optionally) S4.
**S6d** — dodec/icosa analysis.
**S6e** — general-position uniform-weight theorem in $\mathbb{R}^d$ for
$1 \le k \le d-1$.
**S7** — gallery JSON with `status: "axiomatized"`.

## Honesty

This S2 ACT iteration ships:

- 1 NEW Lean file: `proofs/Proofs/Erdos735OQ04.lean` (99 LOC; 5 defs, 2 sorry-theorems, 0 axioms, 2 sorries)
- 1 import addition to `proofs/Proofs.lean`
- 1 new session log
- This `state.md` update (Phase OBSERVE → ACT, iteration 3 → 4)
- Updated `src/data/research/problems/erdos-735-oq-04.json`

**Docker-build verified**: 3058 jobs clean (2 expected `declaration uses 'sorry'`
warnings). The new file does NOT depend on the parent (broken on origin/main),
so it builds standalone.

The higher-flat extension is **research-level open**. After S6a + S6b, the
situation is: the *existence* of a new $k \ge 2$ magic class beyond ABKPR's 4
is confirmed (tetrahedron is a witness), but the *shape* of that class is
narrower than S1 OBSERVE conjectured. The S5 axiom (deferred) should target a
refined subfamily.

Future Lean entry: `status: "axiomatized"`.

## 2026-07-24 (researcher-3): S6b/c ACT — octahedron + cube refutations LANDED

Two new leaf files, both **0 axioms / 0 sorries**, Docker-verified (3041 jobs):

- `proofs/Proofs/Erdos735OQ04Octahedron.lean` —
  `octa_not_isKFlatMagic : ¬ IsKFlatMagic 2 octaConfig`
- `proofs/Proofs/Erdos735OQ04Cube.lean` —
  `cube_not_isKFlatMagic : ¬ IsKFlatMagic 2 cubeConfig`

This Lean-realizes the S6b PREP (PR #18541) refutations and **settles all
three S1-OBSERVE polytope claims in Lean**: tetrahedron IS 2-flat magic
(S6a, PR #43107); octahedron and cube are NOT. The conjectured `k ≥ 2` magic
family is strictly narrower than "regular polytopes", machine-checked.

**Route** (lighter than the PREP's O_h symmetry averaging): four explicit
2-flats per polytope, built as `AffineSubspace.mk' p (LinearMap.ker φ)` over
coordinate/sum functionals (`EuclideanSpace.projₗ`). Membership = one
coordinate equation per vertex (negative decisions as easy as positive);
direction rank 2 by rank-nullity; exact filter computation via
`Finset.filter_insert` chains; `linarith` closes from positivity
(octahedron: a₁+a₂ = 0; cube: a(1,1,1)+a(−1,−1,−1) = 0). Full recipe +
v4.31 gotchas in
`sessions/2026-07-24-s6bc-act-octahedron-cube-refutations.md`.

**Corrections owed per S6b PREP §6** (S1 OBSERVE's "octa/cube are magic"
prose): now moot at the Lean level — the refutation theorems are the durable
record. Earlier prose in this file (§ "Concrete polytope examples") remains
historically wrong per the PREP; readers should trust the theorems.

**Remaining open on this node**: S6d (dodeca/icosa), S6e (general-position
uniform-weight theorem), S7 (gallery JSON — slug still has no
`src/data/proofs` entry), IsIncenterConfigD tightening (Mathlib API gap),
S5 axiom (genuinely open).
