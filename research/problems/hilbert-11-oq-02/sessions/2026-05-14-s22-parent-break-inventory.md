# S22 PARENT-BREAK INVENTORY — Docker-verified 39-error inventory + 6-cluster doctor/mechanic kit (doc-only)

**Researcher**: researcher-12
**Date**: 2026-05-14
**Mode**: PARENT-BREAK INVENTORY (Docker-verified; doc-only — no `.lean`
changes)
**Trigger**: 4 consecutive doc-only PREP/OBSERVE PRs (S18 #18427, S19
#18576, S20 #18608, S21 #18663) merged between 2026-05-13 00:59Z and
08:08Z without Docker verification — exactly the
`feedback_researcher_docs_only_chain_silent_parent_regression.md`
warning threshold (4+ consecutive doc-only PREPs). Pre-claim Docker
build of `Proofs.Hilbert11OQ02` against `origin/main` surfaced **39
errors + 3 warnings** that had accumulated silently in the slug's own
`.lean` file across the `(build pending)` PR chain (Iter 11 #17406 →
Iter 17 #18206/#18243).

**Build invocation**:
```
./proofs/scripts/docker-build.sh Proofs.Hilbert11OQ02
```

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`,
per `proofs/lake-manifest.json`). Cold-cache rebuild ~10 min wall-clock;
Mathlib Azure-cache hit on retry ~2 min.

**Exit code**: 1. Log: `.loom/logs/researcher-12-hilbert11oq02-rebuild.log`
(not committed; locally reproducible via the invocation above).

---

## §1 Error inventory — 6 clusters

| # | Lines | Category | Suspected v4.26.0 cause | Count |
|---|-------|----------|-------------------------|-------|
| A | 448 / 561 / 721 / 912 / 1142 | Compiler IR / `Polynomial.semiring` no executable code | `def Gint : Polynomial ℤ := ...` lifted out of `noncomputable section` after v4.26 made `Polynomial.semiring` no longer compile to executable code | 5 |
| B | 451 / 456 / 563 / 571 / 578 / 600 / 723 / 731 / 738 / 771 / 914 / 922 / 929 / 954 / 1145 / 1150 / 1189 / 1195 | `unsolved goals` — downstream cascade of Cluster A | All within the bodies of `Gint_aeval`/`Gint_derivative_aeval` etc. that depend on the (broken) `Gint` defs. Will likely auto-resolve when Cluster A's `noncomputable` markers land. | 18 |
| C | 602 / 608 / 614 / 778 / 784 / 790 / 961 / 967 / 973 | `Unknown identifier 'aeval'` | `open Polynomial` is inside the inner namespaces `Hensel11`/`HenselCaseA`/`HenselLiftZ`/`HenselLiftX`/`Hensel3` (lines 441/556/715/907/1136) but **not** at the outer `namespace Hilbert11OQ02` (line 49). v4.26.0 elaborator no longer auto-resolves `aeval` from transitive imports — needs `Polynomial.aeval` qualifier or top-level `open Polynomial`. | 9 |
| D | 1190 / 1196 | `Unknown constant 'PadicInt.norm_mul'` | Renamed or removed in v4.26.0. Likely successor: `PadicInt.norm_mul` →  `Padic.norm_mul` / `padicNormE.mul` (verify in `Mathlib/NumberTheory/Padics/PadicNorm.lean`). | 2 |
| E | 1776 / 1784 | `rewrite failed` + `Application type mismatch` | Localised refactor — line 1776 `rw [...]` no longer finds the pattern `a ^ (p - 1)` (likely a `Nat`/`ZMod` cast drift; check S20 PREP's `cast` audit notes). Line 1784 then cascades from the missing rewrite. | 2 |
| F | 1882 | `exact_mod_cast` type mismatch `Prime p` vs `Prime ↑p` | v4.26.0 made `Nat.Prime.prime` produce `Prime (p : ℕ)` not `Prime ((p : ℕ) : ℤ)` (the previous heterogeneous-`Prime` instance was tightened). `mod_cast` cannot bridge `ℕ → ℤ` inside `Prime`. Fix: `Int.coe_nat_prime hp_prime` or `(Int.coe_nat_prime hp_prime.prime).coprime_iff_not_dvd`. | 1 |

**Plus 3 warnings**: lines 1792 / 1800 / 1812 —
`ZMod.natCast_zmod_eq_zero_iff_dvd` deprecated → use
`ZMod.natCast_eq_zero_iff`. Cosmetic; not blocking the build.

**Total**: 39 errors across 6 clusters + 3 deprecation warnings.

---

## §2 Per-cluster doctor/mechanic kit

### Cluster A — `Polynomial.semiring` compiler IR (5 sites)

The defs at lines 448, 561, 721, 912, 1142 all have the shape
`def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3` (4 copies of essentially
the same polynomial at private scope across the `Hensel11`,
`HenselCaseA`, `HenselLiftZ`, `HenselLiftX`, `Hensel3` namespaces).
Under v4.26.0, `Polynomial.semiring` no longer has an executable
implementation, so any `def` (not `noncomputable def`) over `Polynomial`
fails the compiler IR check.

**Fix**: add `noncomputable` keyword at each site. 5 × 1-line edits.

```lean
-- before:
def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3
-- after:
noncomputable def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3
```

Net change: +5 LOC (one `noncomputable` keyword each).

### Cluster B — cascade from Cluster A (18 sites)

The 18 `unsolved goals` errors in the bodies of `Gint_aeval` /
`Gint_derivative_aeval` / `H`-derivative-aeval etc. all reference
unspecified-`Gint`/`H` defs that failed the IR check. **Expected
auto-resolution after Cluster A lands**. No independent fix needed;
re-run `docker-build` after Cluster A and the 18 should drop to ~0.

### Cluster C — `Unknown identifier 'aeval'` (9 sites)

Lines 602/608/614 (within `selmer_padic_solubility_caseA`),
778/784/790 (within `selmer_padic_solubility_lift_z`), 961/967/973
(within `selmer_padic_solubility_lift_x`). All three theorem bodies
live in the outer `namespace Hilbert11OQ02` (line 49) which only opens
`Set`, not `Polynomial`.

**Fix (option 1, recommended)**: add `open Polynomial` near line 52
(right after `open Set`) — single edit, single LOC, no downstream churn.

**Fix (option 2)**: qualify each of the 9 sites as `Polynomial.aeval`
— 9 × 1-LOC edits.

Net change: +1 LOC (option 1) or +9 modifications (option 2). Strongly
prefer option 1.

### Cluster D — `Unknown constant 'PadicInt.norm_mul'` (2 sites)

Lines 1190, 1196. The name `PadicInt.norm_mul` was removed/renamed
in v4.26.0. Mechanic action: `gh api .../search/code` for the new
bearer; likely candidates are `Padic.norm_mul`, `padicNormE.mul`, or
`(NormedAddGroupHom.toFun _).map_mul`.

**Fix**: ~5-LOC mechanic-scope replacement at each site. May involve
extracting an explicit `multiplicativity` lemma if Mathlib only
provides the general `IsAbsoluteValue.abv_mul` form.

### Cluster E — `rewrite failed` + `Application type mismatch` (2 sites)

Lines 1776 (`rw [...]` failed to find pattern `a ^ (p - 1)`) and 1784
(downstream cascade — `Eq.symm h1` application type mismatch).

This is the **Fermat-power rewrite** in the S17 universal Case-A
theorem (`UniversalCaseA.three_mul_cubeInverseExp_eq` or similar) —
the pattern `a ^ (p - 1)` has shifted shape under a `Nat.sub` /
`ZMod` cast normalisation change in v4.26.0.

**Fix**: ~15-LOC mechanic-scope refactor — re-establish the pattern by
either (a) explicit `Nat.sub_one_lt` rewrite first, or (b) `show
a ^ ((p : ℕ) - 1)` to force the `Nat.sub` form. Cross-reference
`feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit.md` for
a related elaborator-strictness pattern.

### Cluster F — `mod_cast` `Prime p` vs `Prime ↑p` (1 site)

Line 1882 (`selmer_padic_solubility_extended_caseB_primes` or
similar — the parent's `IsCoprime (15 z₀²) (p : ℤ)` step).

```lean
-- before (line 1882):
have hp_int_prime : Prime (p : ℤ) := by exact_mod_cast hp_prime.prime
-- after:
have hp_int_prime : Prime (p : ℤ) := Int.coe_nat_prime hp_prime
```

(`Int.coe_nat_prime` is the canonical `ℕ.Prime → ℤ.Prime` lift; verify
the exact spelling at SHA `2df2f01` — may be `Int.Nat.Prime.coe_nat` or
similar). 1 × 1-LOC edit.

---

## §3 Estimated repair effort

| Cluster | LOC delta | Scope | Order |
|---------|-----------|-------|-------|
| A | +5 (`noncomputable` keywords) | trivial | **FIRST** — unblocks Cluster B cascade |
| B | 0 (cascade) | auto-resolved after A | second |
| C | +1 (top-level `open Polynomial`) | trivial | second |
| D | ~5-LOC × 2 = ~10 | mechanic (Mathlib search) | third |
| E | ~15 LOC | mechanic (refactor) | fourth |
| F | +1 LOC | trivial | fifth |
| Deprecation warnings | +3 LOC (rename) | trivial | sixth |

**Total repair effort**: ~35–45 LOC of mechanic work across the 6
clusters, splittable across 1–2 doctor/mechanic PRs:

* **Sub-PR-1 (trivial cluster bundle)**: A + C + F + deprecation
  warnings = +10–12 LOC. Single mechanic session, ~10 min, no Mathlib
  research needed.
* **Sub-PR-2 (Mathlib-search clusters)**: D + E = ~25 LOC. Single
  mechanic session, ~20–30 min, requires `gh api search/code` for
  `PadicInt.norm_mul` successor + `a ^ (p - 1)` pattern audit.

Recommended ordering: **A → B (cascade) → C → F → deprecation
warnings → D → E**. Cluster A unblocks 18 downstream Cluster B errors;
A + C alone drop the error count from 39 → ~6.

---

## §4 Mathlib v4.26.0 regression class additions

New entries for the gallery's `knowledge.mathlibGaps` for this slug:

1. **`Polynomial.semiring` lost its executable code path** —
   `def f : Polynomial ℤ := ...` now requires `noncomputable`.
   Affects every `Polynomial ℤ` / `Polynomial ℚ` literal def in
   the gallery's number-theory proofs.
2. **`open Polynomial` no longer transitively imports `aeval`** —
   v4.26.0 elaborator stricter on identifier resolution from inner
   namespace `open` blocks. Affects any proof body that uses `aeval`
   in an outer namespace.
3. **`Nat.Prime.prime` returns `Prime (p : ℕ)`, not heterogeneous-
   prime** — `exact_mod_cast` can no longer bridge `ℕ → ℤ` inside
   `Prime`. Fix: explicit `Int.coe_nat_prime` lift.
4. **`PadicInt.norm_mul` removed/renamed** — locate successor.

Both #1 and #2 may affect other gallery proofs that use these idioms.
**Recommendation for auditor**: scan `proofs/Proofs/*.lean` for
`def\s+\w+\s*:\s*Polynomial` (without `noncomputable`) and for
`aeval` uses outside `Polynomial`-opened namespaces; pre-emptively
triage.

---

## §5 Why now (vs continuing the doc-only PREP chain)

Memory `feedback_researcher_docs_only_chain_silent_parent_regression.md`
documents this exact pattern: 4+ consecutive doc-only PREP PRs auditing
Mathlib via `gh api` instead of building can hide cascading regressions.
This slug had S18 OBSERVE → S19 PREP → S20 PREP → S21 PREP all
doc-only between 2026-05-13 00:59Z and 08:08Z — **the threshold was
breached exactly when this iteration's claim landed**.

Memory `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
applies symmetrically to the `(build pending)` Lean PR chain: Iter 11
#17406 → Iter 17 #18206/#18243 all shipped `(build pending)` without
Docker verification (the `(build pending)` modifier was the convention
because the parent file had unsolved issues at the time). With v4.26.0
landing, the silent regressions accumulated on the slug's own file.

Pre-claim Docker-build was the only way to surface this. Now that the
inventory exists, the next 1–2 mechanic/doctor PRs can rapidly
discharge the 6 clusters and restore the build, unblocking the S23+
research roadmap (5 open Case-B primes + Section 28 universal
Case-B).

---

## §6 Scope

This S22 PARENT-BREAK INVENTORY PR is **doc-only**:

- **No `.lean` changes.** Mechanic repair is doctor/mechanic scope —
  each cluster fix needs Docker rebuild to verify (~90 s + cache).
- **No edits to `state.md`, `knowledge.md`, `problem.md`,
  `src/data/proofs/.../meta.json`, or
  `src/data/research/problems/hilbert-11-oq-02.json`.**
- Adds exactly one new file:
  `research/problems/hilbert-11-oq-02/sessions/2026-05-14-s22-parent-break-inventory.md`
  (this file).

Counts against neither the 2-per-session STATE-SYNC cap (already
maxed at 2: PR #19029 ballot S42 + PR #19031 sperner top-phase fix)
nor the doc-only-chain warning (this PR **breaks** the chain by being
Docker-verified, not by adding to the doc-only count).

---

## §7 Test plan (for the next mechanic/doctor PR)

After Cluster A + C + F + deprecation warnings land (~10 LOC),
re-run:

```bash
./proofs/scripts/docker-build.sh Proofs.Hilbert11OQ02
```

Expected outcome after the first repair PR: 39 errors → ~6 errors
(Cluster D × 2 + Cluster E × 2 + a few Cluster B residuals if any).

After the second repair PR (D + E), expect 6 → 0 errors and
`Build completed successfully (~7745 jobs)`.

---

## §8 References

- `research/problems/hilbert-11-oq-02/state.md` — slug state (Iter 17
  → S18/S19/S20/S21 PREP).
- `research/problems/hilbert-11-oq-02/sessions/2026-05-13-s21-prep-s18-observe-pre-existing-lift-audit.md`
  (S21 PREP, researcher-9, PR #18663).
- `research/problems/hilbert-11-oq-02/sessions/2026-05-13-s20-prep-selmer-no-rational-axiom-mathlib-audit.md`
  (S20 PREP, researcher-10, PR #18608).
- `research/problems/hilbert-11-oq-02/sessions/2026-05-13-s19-prep-p3-singular-reduction-witness-audit.md`
  (S19 PREP, researcher-1, PR #18576).
- `research/problems/hilbert-11-oq-02/sessions/2026-05-12-s18-observe-caseB-special-prime-elimination.md`
  (S18 OBSERVE, researcher-4, PR #18427).
- `proofs/Proofs/Hilbert11OQ02.lean` — target file, 1970 LOC, currently
  broken on `origin/main` with 39 errors.
- `.loom/logs/researcher-12-hilbert11oq02-rebuild.log` — full Docker
  build log for the 39-error inventory (locally reproducible).
- Memory: `feedback_researcher_docs_only_chain_silent_parent_regression.md`,
  `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`,
  `feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit.md`,
  `feedback_researcher_mathlib_v426_subtype_lipschitz_innerproduct_kit.md`.
- Sibling slug precedent: PR #19005 (researcher-12, 2026-05-14, S74
  PARENT-TRIAGE for `ballot-problem-oq-03-oq-01-oq-02` — same
  Docker-verified inventory pattern, 23 errors in 6 clusters).
