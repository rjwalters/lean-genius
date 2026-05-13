# Current State

**Phase**: OBSERVE — S6 PREP partially shipped; S2 ACT pending
**Since**: 2026-05-12 (S1)
**Iteration**: 3 (S1 OBSERVE → S6a PREP → S6b PREP)

## Current Focus

S1 (researcher-10, 2026-05-12, PR #18336): OBSERVE survey for `erdos-735-oq-04` — the seeker-extracted child of the verified gallery entry `erdos-735` ("Magic Configurations"). Parent's `conclusion.openQuestions[3]`:

> Does the classification extend to configurations where the equal-sum constraint is imposed on k-flats instead of lines?

Three iterations have shipped, all doc-only:

| # | Date | Researcher | PR | Mode | Summary |
|--:|------|------------|----|------|---------|
| S1 | 2026-05-12 | researcher-10 | #18336 | OBSERVE | problem.md + knowledge.md + state.md + gallery JSON |
| S6a | 2026-05-13 | researcher-9 | #18486 | PREP | Tetrahedron 2-flat-magic certificate (uniform weights, magic constant 3) |
| S6b | 2026-05-13 | researcher-5 | #18541 | PREP | Refutation: octahedron + cube are NOT 2-flat magic (vertex-transitive O_h obstruction) |
| (STATE-SYNC) | 2026-05-13 | researcher-5 | (this PR) | STATE-SYNC | Propagate S6a + S6b corrections into state.md / knowledge.md / gallery JSON |

S2 ACT (the Lean scaffold for `PointConfigD` / `WeightingD` / `ConfigKFlat` / `IsKFlatMagic`) **has not yet shipped**; `proofs/Proofs/Erdos735OQ04.lean` does not exist on `origin/main`.

## Active Approach

**The $k$-flat extension is structurally richer than the parent — but the regular-polytope examples are narrower than S1 OBSERVE claimed**:

- **Trivial limits**: $k = 0$ (every config is 0-flat magic) and $k = d$ (single ambient flat is trivially magic).
- **Parent reduction**: $d = 2, k = 1$ recovers exactly the parent's `IsMagic` (definitional).
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

## Open questions — PREP coverage status

| Sub-step | Topic | Status | PR |
|---|---|---|---|
| S2 | Lean definitions (`PointConfigD`, `ConfigKFlat`, `IsKFlatMagic`) | not shipped | — |
| S3 | Trivial cases $k = 0$, $k = d$ | not shipped | — |
| S4 | Parent reduction $d = 2, k = 1$ | not shipped | — |
| S5 | Higher-dim classification axiom (extension of ABKPR) | not shipped | — |
| S6a | Tetrahedron certificate | PREP shipped | #18486 |
| S6b/c | Octahedron + cube refutations | PREP shipped | #18541 |
| S6d | Dodec/icosa analysis | not shipped | — |
| S6e | General-position uniform-weight theorem | not shipped | — |
| S7 | Gallery JSON `status: "axiomatized"` | not shipped | — |

## Blockers

None mathematical for the S2 ACT scaffold. Practical:

- **ABKPR 2008 absent from Mathlib**: parent axiomatises; reuse for this OQ.
- **Higher-flat classification absent from published literature**: S5 axiom is genuinely open.
- **`status: "axiomatized"` mandatory**: ABKPR alone forces this; not overcoming-able by this OQ.
- **`native_decide` route not viable**: per S6a PREP § 1, the tetrahedron certificate uses explicit proof terms, not `decide`. The S1 OBSERVE's S6 plan ("`native_decide` certificates") needs revising during S2 ACT.

## Next Action

**S2 (any researcher)**: Define `PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic` in `proofs/Proofs/Erdos735OQ04.lean`. Approach: parameterise parent's definitions on $(d, k)$, using `EuclideanSpace ℝ (Fin d)` and `AffineSubspace`. Prove trivial cases $k = 0$, $k = d$.

Concrete plan (unchanged from S1):

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Proofs.Erdos735Problem  -- parent

namespace Erdos735OQ04

def PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
    F.direction.toSubmodule.rank = k ∧ (P.filter (· ∈ F)).card ≥ k + 1 }

def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P)
    (F : ConfigKFlat k P) : ℝ := ...

def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop := ...

theorem zero_flat_magic_trivial : IsKFlatMagic 0 P := ...
theorem ambient_flat_magic_trivial : IsKFlatMagic d P := ...
theorem oneflat_eq_parent : IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := ...

end Erdos735OQ04
```

Expected ~50 Lean lines, ~3 sorries on the trivial-case theorems (mechanical to discharge).

**S3** — S4: prove trivial cases and parent reduction.
**S5** — axiomatise the conjectured higher-dim classification (NB: narrow the "regular-polytope" family to the tetrahedron + dodec/icosa-pending; do NOT include octa/cube).
**S6a-c** — already designed (PREPs #18486, #18541); ACT (Lean certificates) pending.
**S6d** — dodec/icosa analysis (Python script in PR #18541 § 3 generalises).
**S6e** — general-position uniform-weight theorem in $\mathbb{R}^d$ for $1 \le k \le d-1$.
**S7** — gallery JSON with `status: "axiomatized"`.

## Honesty

This STATE-SYNC iteration is **doc-only**. It produces:

- 0 new Lean theorems
- 0 sorry/axiom deltas
- 0 new design memos
- Updated `state.md` (this file) reflecting S6a (PR #18486) + S6b (PR #18541) corrections
- Updated `knowledge.md` retracting octahedron + cube magic claims
- Updated `src/data/research/problems/erdos-735-oq-04.json` `currentState.focus`, `attemptCounts`, `knowledge.progressSummary`, and first insight

It applies the "corrections owed to upstream text" listed in PR #18541 § 6, which were explicitly deferred to "a future doctor/curator/researcher pass".

The higher-flat extension is **research-level open**. After S6a + S6b, the situation is: the *existence* of a new $k \ge 2$ magic class beyond ABKPR's 4 is confirmed (tetrahedron is a witness), but the *shape* of that class is narrower than S1 OBSERVE conjectured — octahedron and cube provably do not belong. The S5 axiom should target a refined subfamily.

Future Lean entry: `status: "axiomatized"`.
