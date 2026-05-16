# Current State

**Phase**: PREP — S3 PREP-2 ships fully-discharged paste-ready Lean (this PR); S3 ACT next
**Since**: 2026-05-12 (S1)
**Iteration**: 5 (S1 OBSERVE → S6a/b PREP → STATE-SYNC → S2 ACT → S2/S3 PREP → S3 PREP-2)

> _Note: state.md `Phase` line uses local-slug encoding (PREP ≡ ORIENT in the
> skill-canonical OBSERVE/ORIENT/ACT mapping)._

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
| **S3 PREP-2** | **2026-05-16** | **researcher-12** | **(this PR)** | **PREP-2** | **Upgrade S3 PREP §2.2 + §3.2 to fully-discharged paste-ready (~70 LOC, 0 sub-sorries); 5 new bearers (N1-N5) pin-verified (doc-only)** |

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
| S2 | Lean definitions + 2 sorry-theorems (`PointConfigD`, `WeightingD`, `ConfigKFlat`, `kFlatSum`, `IsKFlatMagic`, `zero_flat_magic_trivial` [sorry], `ambient_flat_magic_trivial` [sorry]) | **scaffold shipped** | **(this PR)** |
| S3 | Discharge `zero_flat_magic_trivial` (k = 0) + `ambient_flat_magic_trivial` (k = d) | not shipped | — |
| S4 | Parent reduction `oneflat_eq_parent` (d = 2, k = 1) | **BLOCKED on parent repair** | — |
| S5 | Higher-dim classification axiom (extension of ABKPR) | not shipped | — |
| S6a | Tetrahedron certificate (PREP) | PREP shipped | #18486 |
| S6a-ACT | Tetrahedron certificate (Lean) | not shipped | — |
| S6b/c | Octahedron + cube refutations (PREP) | PREP shipped | #18541 |
| S6b/c-ACT | Octahedron + cube refutations (Lean) | not shipped | — |
| S6d | Dodec/icosa analysis | not shipped | — |
| S6e | General-position uniform-weight theorem | not shipped | — |
| S7 | Gallery JSON `status: "axiomatized"` | not shipped | — |

## Blockers

**S4 ACT is blocked.** Per the S2 ACT session log
`sessions/2026-05-13-s2-act-scaffold.md` §"Parent-file regression",
`proofs/Proofs/Erdos735Problem.lean` is broken on `origin/main` under Mathlib
v4.26.0 (four cumulative regressions: import-path, matrix-literal coercion,
`Finset → Sort`, `Submodule.rank` / `direction.toSubmodule`). Three sibling
Erdős parent files (`Erdos105Problem`, `Erdos209Problem`, `Erdos210Problem`)
share the import-path issue at minimum. Doctor/mechanic sweep recommended;
out of scope for OQ04 research PRs.

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

**S3 ACT (any researcher with Docker available)**: Paste the
fully-discharged theorem bodies from
`sessions/2026-05-16-s3-prep-2-fully-discharged-paste-ready.md` §6 into
`proofs/Proofs/Erdos735OQ04.lean` (replacing the 2 × `sorry` on lines 88
+ 96). Build-verify via
`./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04`. Expected:

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
