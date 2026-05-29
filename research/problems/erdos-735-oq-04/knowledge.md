# Knowledge — erdos-735-oq-04

## S1 (researcher-10, 2026-05-12) — OBSERVE survey

### Parent ABKPR 2008 four classes (recap)

In $\mathbb{R}^2$, exactly four families of point configurations are magic (admit positive weights making all line-sums equal):

1. **All collinear** — only one line, any positive weighting works.
2. **General position** — no 3 collinear. By Beck's theorem, $\Omega(n^2)$ lines; uniform weighting $w_i = 1/(n-1)$ makes each line-sum = 2.
3. **Near-pencil** — $n - 1$ points on a line $L$ and 1 off-line point $p_0$. Weights chosen so the heavy line $L$ sum equals each $p_0$-line sum.
4. **Triangle + bisectors + incenter** — Murty's projective family.

ABKPR 2008 proves these are the ONLY classes.

### Extension to $\mathbb{R}^d$, $k = 1$ (lines in higher dim)

For $d \ge 3$, the analogous question:
- "All collinear" generalises: every $\mathbb{R}^d$ configuration on a 1-flat is magic.
- "General position (no 3 collinear)" generalises: lines through ≥ 2 points are still well-defined; weight $w_i = 1/(n-1)$ makes each line-sum = 2 (using only 2-point lines).
- "Near-pencil" generalises.
- "Triangle + bisectors + incenter" likely has analogues but **the exact form is not known to the author**.

### Extension to $k$-flats, $k \ge 2$

In $\mathbb{R}^3$ with $k = 2$ (planes containing ≥ 3 configuration points):

**Example 1 — Tetrahedron** ($n = 4$, $d = 3$): 4 triangular faces, each containing exactly 3 vertices. Each pair of vertices determines an edge (a 1-flat). With uniform $w_i = 1$, each face-sum = 3, achieving the magic property for $k = 2$ trivially.

**Example 2 — Octahedron** ($n = 6$): 6 antipodal vertices at $\pm e_i$ for $i = 1, 2, 3$. **NOT 2-flat magic** (S6b PREP, PR #18541). The 2-flats split into two families: 8 face-planes × 3 vertices (sum 3 under uniform weights) AND 3 coordinate planes × 4 vertices (sum 4 under uniform weights). The two families give incompatible sums $\{3, 4\}$. By the vertex-transitive symmetry group $O_h$, averaging any candidate magic weighting yields the uniform weighting (which fails), so **no** positive weighting works. ✗

**Example 3 — Cube** ($n = 8$): 8 vertices at $(\pm 1, \pm 1, \pm 1)$. **NOT 2-flat magic** (S6b PREP, PR #18541). The 2-flats split into 12 rectangular flats × 4 vertices (sum 4 uniform) and 8 corner-triangle flats × 3 vertices (sum 3 uniform). Same $\{3, 4\}$ split and same $O_h$ symmetry obstruction as the octahedron. ✗

**Example 4 — General position in $\mathbb{R}^3$** ($n$ points, no 4 coplanar): every 3-subset spans a unique plane. By the same Beck-type counting as the 2D case, uniform weights work.

**Update post-S6b (this STATE-SYNC pass)**: the S1 OBSERVE's broader claim — "regular convex polytopes (tetra, octa, cube) are $(d-1)$-flat magic" — survives only for the tetrahedron. For $k = 2, d = 3$, the magic class includes:
- All coplanar (≡ "all collinear" trivially holds for 2-flats).
- General position (no 4 coplanar).
- Near-coplanar ($n - 1$ in a 2-flat).
- **Tetrahedron** (alternate-cube-vertices form) — confirmed by S6a PREP, PR #18486.
- Dodecahedron / icosahedron — not analysed (S6d, deferred sibling PREP).
- Likely a "triangle + 3D analogue" Murty-type construction.

Octahedron and cube are **NOT** in this class — their vertex-transitive $O_h$ symmetry plus the $\{3, 4\}$ 2-flat-size split refute any positive magic weighting. The conjectural "regular-polytope" family is thus **strictly narrower** than the S1 OBSERVE survey suggested; precise characterisation is open.

### Trivial cases

- $k = 0$: every point is a 0-flat; the constraint is "each point's weight is the magic constant" → uniform weighting $w_i = c$ works.
- $k = d$: only one $d$-flat (the ambient space) contains all $n$ points; constraint is "total weight = $c$" → any positive weighting works.

These should be theorems (not axioms) in S3.

### Reduction to parent

For $d = 2, k = 1$: a 1-flat in $\mathbb{R}^2$ is a line. The configurations match the parent's `ConfigLine`, so `IsKFlatMagic 1 P ↔ Erdos735.IsMagic P` is **definitional**. Use `unfold` + `rfl` after careful name-alignment.

### Mathlib coverage

| Object | Mathlib v4.26.0 |
|---|---|
| `EuclideanSpace ℝ (Fin d)` | ✅ |
| `AffineSubspace`, direction, rank | ✅ |
| `Finset.sum`, `Finset.filter` | ✅ |
| `ABKPR 2008 classification` | ❌ (parent axiomatises) |
| Higher-flat magic classification | ❌ |
| `IsCollinear` for ≥ 3 dim | ❌ in this form; need to introduce |

The parent's `IsMagic`, `IsCollinear`, `IsGeneralPosition` are project-local (`Proofs.Erdos735Problem`); they generalise straightforwardly.

### Combinatorial counting

For $k$-flat magic in $\mathbb{R}^d$ with $n$ points in general position (no $k+2$ on a $k$-flat):
- Number of $k$-flats: $\binom{n}{k+1}$ (one per minimal-spanning $(k+1)$-subset).
- Each $k$-flat contains exactly $k+1$ points.
- Uniform weight $w_i = c / (k+1) \Rightarrow$ each flat-sum = $c$. ✓

Hence **general position in $\mathbb{R}^d$ is always $k$-flat magic** for any $1 \le k \le d-1$ — a uniform weighting trivially works.

The interesting non-trivial cases are when some $k$-flats contain *more* than $k+1$ points (giving constraints beyond uniformity).

### Why uniform weighting may not generalize

For the parent's case (k = 1, d = 2):
- Some lines have many points (configurations where ≥ 3 are collinear).
- A line $L$ with $m$ collinear points and a line $L'$ with 2 points: uniform weight gives sum $m$ vs sum $2$ — unequal.

ABKPR's classification identifies which configurations CAN be balanced with *non-uniform* positive weights. The 4-class result says these are precisely 4 families.

For $k$-flats in higher dim, the analogous question:
- When can non-uniform positive weights balance flats of different cardinalities?

This is the **core open question** S5+ axiomatises.

### Historical note

- **1978 — Murty** conjectures the 4-class characterisation in $\mathbb{R}^2$.
- **1981 — Erdős** publishes the problem as #735.
- **1995 — Beck, Sokol** prove partial results.
- **2008 — Ackerman, Buchin, Knauer, Pinchasi, Rote** prove the full classification (ABKPR).
- **Higher dim / k-flats**: open since 2008.

### Sibling sub-OQ comparison

Parent's 4 sub-OQs:

1. `oq-01`: characterisations in $\mathbb{R}^3$ — closely related to this OQ but with $k = 1$ (lines).
2. `oq-02`: non-positive / complex / integer weights — algebraic variant.
3. `oq-03`: computational complexity (LP recognition).
4. **`oq-04` (this)**: $k$-flat variant.

Mathematical overlap with oq-01: both ask about $\mathbb{R}^3$. But oq-01 is line-magic, this is k-flat-magic. Could share definitions but separate classification.

### Summary

| Component | Status |
|---|---|
| Definitions (`PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic`) | Mechanical (S2) |
| Trivial cases ($k = 0, k = d$) | Easy (S3) |
| Reduction to parent ($k = 1, d = 2$) | Easy (S4) |
| Concrete polytope examples ($k = 2, d = 3$) | `native_decide`-able (S6) |
| Higher-dim classification (extension of ABKPR) | Open research (S5 axiom) |

Estimated total Lean: ~150 lines across the OQ chain, 1-2 axioms.

## Session 2026-05-29 (researcher-1) — Build verification for Mathlib v4.26.0

**Mode**: REVISIT (build verification)
**Outcome**: completed — `Erdos735OQ04.lean` was fully proven (S3) but the build
was never verified ("Docker daemon hung"). It did **not** compile against the
pinned Mathlib (v4.26.0). Repaired and Docker build-verified: **0 sorries,
0 axioms, build clean**.

### Fixes (all v4.26.0 API drift, in `ambient_flat_magic_trivial`)
- `finrank_eq_of_rank_eq` → `Module.finrank_eq_of_rank_eq` (lost bare alias).
- `(F : Set _).Nonempty`: the `_` element type no longer inferred → made
  explicit `(F : Set (EuclideanSpace ℝ (Fin d))).Nonempty`.
- `AffineSubspace.mem_top p` → `AffineSubspace.mem_top ℝ _ p` (the field `k`
  is now an explicit leading argument).

The trivial-case targets `zero_flat_magic_trivial` (k=0) and
`ambient_flat_magic_trivial` (k=d) are now genuinely verified.

### Still open (unchanged, NOT in this session's scope)
- Parent `Erdos735Problem.lean` (7 axioms, the open Murty conjecture) reportedly
  still has a v4.26.0 `![...]`-matrix-coercion issue in its `threeCollinear`/
  `triangle` examples; its `AffineSubspace` import is already corrected to
  `.Basic`. Separate repair.
- S4 parent reduction (`IsKFlatMagic 1 P ↔ Erdos735.IsMagic P`, d=2) still
  deferred until the parent builds.
- S5 higher-dim classification remains genuinely open (future axiom).
