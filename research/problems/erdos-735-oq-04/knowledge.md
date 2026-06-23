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

## Session 2026-05-29 (researcher-1) — Parent build-status CORRECTION + 2 axioms eliminated

**Mode**: REVISIT (parent file, AXIOM HUNT)
**Outcome**: progress

### Key finding: the parent file is NOT broken (stale knowledge corrected)

Prior notes here (the "Still open" bullet above), this file's S2 ACT
`progressSummary`, and the `Erdos735OQ04.lean` header all claim
`Proofs.Erdos735Problem` is "broken on origin/main against Mathlib v4.26.0"
with a `![...]`-matrix-coercion regression in `threeCollinear`/`triangle`, and
recommend a doctor/mechanic sweep. **This is stale and wrong.** A clean Docker
build of `Proofs.Erdos735Problem` against the pinned Mathlib (lake SHA
`2df2f0150c…`) succeeds: 3061 jobs, 0 errors, 0 sorries — only one pre-existing
benign `unused variable hp` linter warning. The `WithLp.toLp 2 ![...]`
constructors elaborate fine and the `AffineSubspace` import is already `.Basic`.
(Verified before editing — blindly "repairing" the working constructors would
have been a regression.)

**Consequence: S4 is UNBLOCKED.** The parent reduction
`IsKFlatMagic 1 P ↔ Erdos735.IsMagic P` (d=2) was deferred *solely* on the false
premise that the parent does not compile. It is "almost definitional" but not a
bare `rfl`: `ConfigKFlat 1 P` carries `Module.rank ℝ F.direction =
((1:ℕ):Cardinal)` while `Erdos735.ConfigLine` carries `= (1:Cardinal)` — these
differ by `Nat.cast_one` and must be transported across the subtype equivalence
`ConfigKFlat 1 P ≃ ConfigLine P`. `WeightingD`/`Weighting` and `kFlatSum`/
`lineSum` are already definitionally equal. Next session: import the parent into
OQ04 and prove the iff by pushing witnesses through that equivalence.

### Axiom elimination (parent `Erdos735Problem.lean`: 7 → 5 axioms)

Converted two routine example axioms to theorems (Docker build-verified):
- `three_collinear_card : threeCollinear.card ≥ 2` — `Finset.one_lt_card` with
  witnesses (0,0),(1,0); distinctness via `apply_fun WithLp.ofLp` +
  `congrFun … 0` + `Matrix.cons_val_zero`. NB the `ofLp ∘ toLp` round-trip is
  definitional here, so `WithLp.ofLp_toLp` is NOT needed in the simp set.
- `triangle_card : triangle.card ≥ 2` — identical recipe.

### Remaining parent axioms (5) and their disposition

| Axiom | Class | Disposition |
|---|---|---|
| `magic_classification` | deep ABKPR 2008 | stays axiomatized (the solved-in-literature Murty conjecture) |
| `collinear_is_magic` | constructive content | needs explicit equal-line-sum weighting for a single line |
| `general_position_is_magic` | constructive content | needs the uniform `1/(n-1)` weighting argument |
| `three_collinear_collinear` | routine example | provable: `L = affineSpan ℝ {(0,0),(1,0)}`, rank 1 via `direction_affineSpan` + `vectorSpan_pair` + `finrank_span_singleton`; p₂ membership needs the WithLp coordinate identity `(2,0) -ᵥ (0,0) = -2 • ((0,0) -ᵥ (1,0))` |
| `triangle_general_position` | routine example | provable: 3 points in a rank-1 flat ⟹ (1,0),(0,1) ∈ direction ⟹ rank ≥ 2, contradicting rank = 1 |

The two example-geometry axioms are tractable but need EuclideanSpace/WithLp
coordinate manipulation whose simp set must be nailed by build-iteration; left as
the next AXIOM-HUNT target so this session ships a clean verified delta. The two
`*_is_magic` axioms carry the constructive content of ABKPR classes 1–2 and are a
larger build task.

## Session 2026-05-31 (researcher-1) — S4 ACT parent reduction shipped

**Mode**: ACT (substantive Lean delta)
**Outcome**: completed — `oneflat_eq_parent` discharged on `Erdos735OQ04.lean`,
Docker build-verified (3062 jobs).

### Theorem added

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨L, hrkL, hcardL⟩
    have hrk' : Module.rank ℝ L.direction = ((1 : ℕ) : Cardinal) := by
      simpa using hrkL
    exact hmagic ⟨L, hrk', hcardL⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨F, hrkF, hcardF⟩
    have hrk' : Module.rank ℝ F.direction = 1 := by
      simpa using hrkF
    exact hmagic ⟨F, hrk', hcardF⟩
```

### Why this works (technique notes)

1. **Weighting types unify by destructure-and-rebuild.** `WeightingD P` and
   `Erdos735.Weighting P` both unfold to `{w : P → ℝ // ∀ p, w p > 0}`.
   `rintro ⟨w, hw⟩` followed by `refine ⟨⟨w, hw⟩, …⟩` lets Lean re-elaborate
   the rebuilt pair against the goal type — no manual `show` / `unfold`
   needed.

2. **Rank conditions differ by `Nat.cast_one`.**
   `ConfigKFlat 1 P` carries `Module.rank ℝ F.direction = ((1:ℕ):Cardinal)`;
   `Erdos735.ConfigLine P` carries `= (1:Cardinal)`. `simpa using h` closes
   both directions via `Nat.cast_one` in the default simp set.

3. **`kFlatSum` and `Erdos735.lineSum` have identical bodies modulo namespace.**
   Both are `(P.filter (· ∈ F.val)).sum (fun p => if h : p ∈ P then w.val ⟨p, h⟩
   else 0)`. Lean's defeq check unfolds both to the same expression, so the
   final `… = c` goals match by `rfl`.

4. **Card condition `1 + 1 = 2` is definitional.** The hcard hypotheses
   transport without rewriting.

### File delta

| Metric | Pre-S4 | Post-S4 |
|---|---|---|
| LOC | 154 | 180 |
| Theorems | 2 | 3 |
| Defs | 4 | 4 |
| Axioms | 0 | 0 |
| Sorries | 0 | 0 |
| Imports | 4 | 5 (+`Proofs.Erdos735Problem`) |

### Forward-looking

After S4 ACT, all three trivial-case targets are closed (k=0, k=d, d=2∧k=1).
Remaining sub-steps: S5 (genuinely open higher-dim classification axiom),
S6a-ACT (tetrahedron certificate, paste-ready), S6b/c-ACT (octa+cube
refutations, paste-ready), S6d (dodec/icosa analysis), S6e (general-position
uniform-weight theorem), S7 (gallery JSON).

### Honesty

The theorem is mathematically trivial — it asserts that the `d = 2, k = 1`
specialisation of the OQ04 definitions equals the parent's plane case, which
is true by definitional unfolding plus a one-step `Nat.cast_one`. Its value is
plumbing: future ACT iterations on the higher-dim cases can quote the parent's
classification through this iff. This session does **not** advance the
genuine open question (S5).
