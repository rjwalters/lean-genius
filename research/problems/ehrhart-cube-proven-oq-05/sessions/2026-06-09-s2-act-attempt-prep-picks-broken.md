# S2 ACT-attempt → PREP — PicksTheorem.lean broken at HEAD

**Date**: 2026-06-09 (UTC)
**Researcher**: researcher-6
**Iteration**: 4 (first attempt at S2 ACT scaffold)
**Outcome**: PREP-bank — scaffold authored + Docker-attempted; sibling
`Proofs/PicksTheorem.lean` fails to build on `origin/main` HEAD
`162265bae2c` (pre-existing Mathlib v4.26.0 breakage at line 329
`picks_additive`). Scaffold cannot land until the sibling is repaired.

## 1. Plan Followed

Per the state.md "Next Action" and the iter-1 S2 PREP blueprint
(`knowledge.md` §"Lean Skeleton Sketch for S2"), the S2 ACT
deliverable is:

1. Create `proofs/Proofs/EhrhartCubeProvenOQ05.lean` (~80 LOC):
   imports `Proofs.EhrhartPolynomials` + `Proofs.PicksTheorem`;
   three theorem stubs (`ehrhartPoly_2d_explicit`,
   `simpleLatticePolygon_to_latticePolygon`, `picks_theorem_derived`)
   each closed by `sorry`.
2. Register file in `proofs/Proofs.lean`.
3. Minimal gallery entry `src/data/proofs/ehrhart-cube-proven-oq-05/`.
4. JSON + state.md update.
5. Docker-verify with `./proofs/scripts/docker-build.sh
   Proofs.EhrhartCubeProvenOQ05`.

## 2. What Actually Happened

Step 1-2 done; step 5 attempted.

The Docker build at HEAD `162265bae2c` (clean checkout, no other
changes) progressed through 3059/3060 jobs, then failed at the
import-resolution of `Proofs.PicksTheorem`. Concretely:

```
ℹ [3059/3060] Built Proofs.EhrhartPolynomials (181s)
error: Proofs/PicksTheorem.lean:329:61: unsolved goals
i₁ i₂ b₁ b₂ e : ℕ
he : 2 ≤ e
hb₁ : e ≤ b₁
hb₂ : e ≤ b₂
h2e : 2 * e ≤ b₁ + b₂
⊢ -2 + ↑i₁ + ↑b₁ * (1 / 2) + ↑i₂ + ↑b₂ * (1 / 2) =
    ↑b₁ * (1 / 2) + ↑b₂ * (1 / 2) + ↑(i₁ + i₂ + e - 2) + ↑(e * 2) * (-1 / 2)
warning: Proofs/PicksTheorem.lean:333:27: This simp argument is unused:
  Nat.cast_sub he
Some required targets logged failures:
- Proofs.PicksTheorem
```

The failing tactic in `picks_additive` (lines 326-334):

```lean
theorem picks_additive (i₁ i₂ b₁ b₂ : ℕ) (e : ℕ) (he : 2 ≤ e)
    (hb₁ : e ≤ b₁) (hb₂ : e ≤ b₂) :
    picks_formula i₁ b₁ + picks_formula i₂ b₂ =
    picks_formula (i₁ + i₂ + e - 2) (b₁ + b₂ - 2 * e + 2) := by
  unfold picks_formula
  have h2e : 2 * e ≤ b₁ + b₂ := by omega
  simp only [Nat.cast_add, Nat.cast_sub he, Nat.cast_sub h2e]
  ring
```

Diagnosis: `Nat.cast_sub he` (where `he : 2 ≤ e`) rewrites
`↑(e - 2)`, but the goal contains `↑(i₁ + i₂ + e - 2)` — the
hypothesis is `2 ≤ e`, not `2 ≤ i₁ + i₂ + e`. The Mathlib v4.26.0
linter now flags this as `unused` (warning at 333:27); previously
`ring` could close anyway by some Mathlib-internal cast unfolding,
but at v4.26.0 it cannot. The expression `↑(i₁ + i₂ + e - 2)` is
left un-cast, and `ring` does not handle the truncated-subtraction
boundary.

This is a **pre-existing breakage on `origin/main`** with no nexus
to `ehrhart-cube-proven-oq-05`. Confirmed by running
`./proofs/scripts/docker-build.sh Proofs.PicksTheorem` on a clean
checkout: identical failure.

## 3. Verification That the Blocker Is Pre-existing

1. The branch `research/ehrhart-cube-proven-oq-05-s2-act` was created
   from `origin/main` at `162265bae2c` with no Lean modifications
   prior to the failed build.
2. `./proofs/scripts/docker-build.sh Proofs.PicksTheorem` on the
   pre-modification worktree (zero diff from `origin/main`) produces
   the identical failure.
3. Recent gallery commit messages reference the same Mathlib v4.26.0
   class of breakage (e.g. `162265bae2c research(fundamental-theorem-
   calculus-oq-01-incomplete-01): S6 ACT-attempt → PREP — iter-5
   plan has circular import; sibling broken at HEAD (3 pre-existing
   Mathlib v4.26.0 errors)`).
4. `PicksTheorem.lean` itself was last touched on 2026-05-16
   (`ecb47b35601`), well before the Mathlib v4.26.0 upgrade. No
   `picks-theorem-oq-XX` sibling that lands cleanly imports
   `Proofs.PicksTheorem` — they all import only `Mathlib` and
   redeclare polygon structures locally (e.g.
   `PicksTheoremOQ01.lean:1` `import Mathlib`).

## 4. Banked Scaffold

The S2 ACT scaffold (80 LOC, ready for re-attempt once the sibling
is unblocked) is reproduced below verbatim. Future iterations
should `Write` this content to
`proofs/Proofs/EhrhartCubeProvenOQ05.lean` and add the import line
`import Proofs.EhrhartCubeProvenOQ05` to `proofs/Proofs.lean` between
`Proofs.EhrhartCubeProvenOQ04` and `Proofs.EhrhartPolynomialOQ03`.

```lean
import Proofs.EhrhartPolynomials
import Proofs.PicksTheorem

/-
# Pick's Theorem Derived from Ehrhart Polynomial Existence
# (ehrhart-cube-proven-oq-05, S2 ACT scaffold)

## What This Will Prove

The standalone `picks_theorem` axiom in `PicksTheorem.lean` is
*redundant* given the three Ehrhart axioms already declared in
`EhrhartPolynomials.lean`:

* `ehrhart_theorem`              — existence of a degree-d polynomial
                                    counting lattice points in dilations,
* `ehrhart_leading_coeff_volume` — leading coefficient = volume of P
                                    (per-polytope, pinned by `P.volume`),
* `ehrhart_macdonald_reciprocity`— interior count = (-1)^d L_P(-n).

The target identity is Pick's formula `A = i + b/2 - 1` for any
simple lattice polygon, derived purely from the three Ehrhart axioms
+ the gallery's already-proven conditional `picks_from_ehrhart`
(line 237 of `EhrhartPolynomials.lean`).

## S2 ACT Scope (this file)

This scaffold introduces three theorem stubs corresponding to stages
S3, S4, S5 of the R1 (conditional Pick's theorem via Ehrhart) route:

| Stub                                    | Future Stage | Approx. discharge |
|-----------------------------------------|--------------|------------------|
| `ehrhartPoly_2d_explicit`               | S3          | ~200 lines     |
| `simpleLatticePolygon_to_latticePolygon`| S4          | ~150 lines     |
| `picks_theorem_derived`                 | S5          | ~80 lines      |

Each stub is closed by `sorry` in this scaffold; the discharges are
the subject of later iterations.

## Status

- 3 sorries (one per stub, each marking a future stage's deliverable).
- 0 new axioms; 3 inherited Ehrhart axioms from `EhrhartPolynomials`.
- 0 new structures.

After all three stubs discharge to `0 sorries`, the deliverable is a
**conditional Pick's theorem**: 3 inherited Ehrhart axioms, no new
axioms — a meaningful axiom-dependency reduction in the gallery.

## References

- S2 PREP blueprint: `research/problems/ehrhart-cube-proven-oq-05/knowledge.md`
  §"Lean Skeleton Sketch for S2".
- AXIOM-FIX (PR #22648, merged 2026-06-09): added the
  `LatticePolytope.volume`, `LatticePolytope.volume_pos`, and
  `LatticePolygon.interior_at_one` fields that the discharges in
  S3-S5 will rely on.
-/

namespace EhrhartCubeProvenOQ05

open EhrhartPolynomials Polynomial

/-- **Q1 / S3 target**: the Ehrhart polynomial of a 2D lattice polygon
has the explicit closed form `A·n² + (b/2)·n + 1`, where `A = P.area`
and `b = P.boundaryPoints`.

The S3 discharge will:
1. Use `ehrhart_leading_coeff_volume` to pin the leading coefficient
   to `P.area` (after identifying `P.volume = P.area` for 2D polygons).
2. Use `ehrhart_constant_term` (already proved) for the constant term `1`.
3. Use `ehrhart_macdonald_reciprocity` at `n = -1` together with
   `P.interior_at_one` to extract the linear coefficient as `b/2`,
   via the 4-line algebraic argument in knowledge.md §"The Q1 Polynomial
   Identity". -/
theorem ehrhartPoly_2d_explicit (P : LatticePolygon) :
    ∀ n : ℚ, (ehrhartPoly P.toLatticePolytope).eval n =
      P.area * n ^ 2 + (P.boundaryPoints : ℚ) / 2 * n + 1 := by
  sorry

/-- **Q2 / S4 target**: every `PicksTheorem.SimpleLatticePolygon`
arises from a `LatticePolygon`. The bridge identifies the two
parallel polygon structures.

`SimpleLatticePolygon` carries `(interior_count, boundary_count, area)`;
`LatticePolygon` carries the same data plus the underlying
`LatticePolytope 2` (lattice point count function, volume, ...).

The S4 discharge will construct the underlying counting function via
the existential supplied by `ehrhart_theorem` and verify the structure
laws (`nonempty`, `count_zero`, `total_eq`, `interior_at_one`) from
the corresponding Ehrhart axioms. -/
noncomputable def simpleLatticePolygon_to_latticePolygon
    (P : PicksTheorem.SimpleLatticePolygon) : LatticePolygon :=
  sorry

/-- **Q2 close / S5 target**: Pick's formula `A = i + b/2 - 1` for
any simple lattice polygon, derived from the three Ehrhart axioms.

The S5 discharge will:
1. Apply `simpleLatticePolygon_to_latticePolygon` to obtain the
   companion `LatticePolygon`.
2. Apply `ehrhartPoly_2d_explicit` at `n = 1` to obtain
   `L_P(1) = A + b/2 + 1`.
3. Combine with `LatticePolygon.total_eq` (`L_P(1) = i + b`) and the
   conditional `picks_from_ehrhart` (line 237 of `EhrhartPolynomials.lean`)
   to conclude `A = i + b/2 - 1`. -/
theorem picks_theorem_derived (P : PicksTheorem.SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1 := by
  sorry

end EhrhartCubeProvenOQ05
```

## 5. Suggested Repair Path for the Blocker

The `picks_additive` failure is a small, localized Mechanic-class
fix (~5-10 LOC). Sketch:

```lean
theorem picks_additive (i₁ i₂ b₁ b₂ : ℕ) (e : ℕ) (he : 2 ≤ e)
    (hb₁ : e ≤ b₁) (hb₂ : e ≤ b₂) :
    picks_formula i₁ b₁ + picks_formula i₂ b₂ =
    picks_formula (i₁ + i₂ + e - 2) (b₁ + b₂ - 2 * e + 2) := by
  unfold picks_formula
  have h2e   : 2 * e ≤ b₁ + b₂ := by omega
  have h_ie2 : 2 ≤ i₁ + i₂ + e := by omega
  push_cast [Nat.cast_sub h2e, Nat.cast_sub h_ie2]
  ring
```

The change replaces the un-applicable `Nat.cast_sub he` rewrite
with the correctly-applicable `Nat.cast_sub h_ie2` (the missing
`2 ≤ i₁ + i₂ + e` hypothesis), and uses `push_cast` (the v4.26
idiomatic replacement for the manual `simp only [Nat.cast_*]`
recipe). This is a one-file, one-theorem change with no axiom or
structure ripple.

This Mechanic fix is **out of scope for `ehrhart-cube-proven-oq-05`**
since the slug's deliverable is the OQ-05 scaffold, not gallery
infrastructure. Recommended path: a dedicated Mechanic PR repairs
`PicksTheorem.picks_additive`, after which the S2 ACT scaffold can
re-attempt cleanly.

## 6. Net Delta for This PREP-Bank PR

| Touched | Type | Reason |
|---------|------|--------|
| `research/problems/ehrhart-cube-proven-oq-05/sessions/2026-06-09-s2-act-attempt-prep-picks-broken.md` | NEW | This journal — banks scaffold + documents blocker |
| `research/problems/ehrhart-cube-proven-oq-05/state.md` | MOD | Phase ACT → PREP (blocked); iteration 3 → 4 |
| `src/data/research/problems/ehrhart-cube-proven-oq-05.json` | MOD | Mirror phase/iteration; nextAction → "S2 ACT re-attempt after Picks repair"; blockers field populated |

- 0 Lean files modified.
- 0 axioms / 0 sorries added.
- 0 lineCount change.
- doc-only PR.

## 7. Iteration Log Append (for state.md)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| **S2 ACT-attempt → PREP** | **2026-06-09** | **researcher-6** | **(this PR)** | **scaffold authored (80 LOC) + Docker-attempted; sibling `Proofs/PicksTheorem.lean` broken at HEAD (`picks_additive` line 329, Mathlib v4.26.0 `ring` regression after un-applicable `Nat.cast_sub he`); pre-existing breakage unrelated to OQ-05; banked scaffold + suggested 5-LOC Mechanic repair in §4-5; S2 ACT re-attempts cleanly after Picks repair** |
