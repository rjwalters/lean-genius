# Current State

**Phase**: ACT — S2 ACT scaffold shipped (Lean file exists); S3 ACT discharges trivials
**Since**: 2026-05-12 (S1)
**Iteration**: 4 (S1 OBSERVE → S6a PREP → S6b PREP → STATE-SYNC → S2 ACT scaffold)

## Current Focus

S2 ACT (researcher-12, 2026-05-13, this PR): the first Lean file under this slug
ships — `proofs/Proofs/Erdos735OQ04.lean` (99 LOC) — declaring the parameterised
definitions and the two trivial-case theorem signatures (both with `sorry`s
pending S3 ACT).

Prior iterations:

| # | Date | Researcher | PR | Mode | Summary |
|--:|------|------------|----|------|---------|
| S1 | 2026-05-12 | researcher-10 | #18336 | OBSERVE | problem.md + knowledge.md + state.md + gallery JSON |
| S6a | 2026-05-13 | researcher-9 | #18486 | PREP | Tetrahedron 2-flat-magic certificate (uniform weights, magic constant 3) |
| S6b | 2026-05-13 | researcher-5 | #18541 | PREP | Refutation: octahedron + cube are NOT 2-flat magic (vertex-transitive O_h obstruction) |
| (STATE-SYNC) | 2026-05-13 | researcher-5 | #18891 | STATE-SYNC | Propagated S6a + S6b corrections into state.md / knowledge.md / gallery JSON |
| **S2** | **2026-05-13** | **researcher-12** | **(this PR)** | **ACT** | **Lean scaffold: 5 defs + 2 sorry-theorems; 99 LOC; Docker-build clean (3058 jobs)** |

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

**S3 (any researcher)**: Discharge the two trivial-case theorems. Approach
(per S2 ACT session log §"Next iteration"):

* `zero_flat_magic_trivial`: constant-1 weighting + `c = 1`; for each
  `F : ConfigKFlat 0 P`, show `F.val` is a singleton containing exactly one
  point of `P` (rank-0 + filter cardinality ≥ 1), then `kFlatSum = 1 = c`.
  ~15-20 LOC; uses `Submodule.rank_eq_zero_iff` /
  `Module.rank_eq_zero_iff`.
* `ambient_flat_magic_trivial`: case split on `P.card ≥ d + 1`. Vacuous case
  picks `c = 1`. Non-vacuous case picks `c = P.card` with uniform weight.
  ~20-30 LOC; uses `AffineSubspace.direction_eq_top_iff` or
  `Module.rank_eq_finrank_iff` for `Fin d → ℝ`.

Total: ~35-50 LOC, 0 new sorries.

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
