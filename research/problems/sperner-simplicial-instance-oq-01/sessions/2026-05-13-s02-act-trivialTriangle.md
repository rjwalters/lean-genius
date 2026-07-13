# Session 3 — S2 ACT: `trivialTriangle : Triangulation ℕ 2` (Candidate A, build pending)

**Researcher.** researcher-1, 2026-05-13.

**Mode.** S2 ACT (Lean code). Build pending.

**Outcome.** Shipped the verbatim §3 snippet from the S2 PREP
(`sessions/2026-05-12-s02-prep-candidate-a.md`, merged as PR #18578
at 2026-05-13T04:48Z) into
`proofs/Proofs/SpernerSimplicialInstance.lean`. The file went from
994 → 1022 LOC (+28, including the `/-! ## Trivial 2-Simplex
Triangulation` docstring header). **0 sorries, 0 axioms.**

## 1. Patch summary

Inserted between `end Interval` (line 973 in origin/main) and the
`/-! ## Interval Sperner's Lemma` docstring (was line 975, now
shifted), at the namespace `Triangulation` level:

| Field / obligation | Discharge | LOC |
|---|---|---|
| `Cell := Fin 1` | — | 1 |
| `cellDecEq := inferInstance` | core | 1 |
| `cellFintype := inferInstance` | core | 1 |
| `vertex := fun _ k => k.val` | term | 1 |
| `vertex_injective := fun _ => Fin.val_injective` | Mathlib | 1 |
| `adj := fun _ _ => none` | term | 1 |
| `adj_symm := fun _ _ _ _ h => Option.noConfusion h` | core | 1 |
| `adj_vertex := fun _ _ _ _ h => Option.noConfusion h` | core | 1 |
| `adj_ne := fun _ _ _ _ h => Option.noConfusion h` | core | 1 |

Plus a 15-LOC `/-! ... -/` introductory docstring framing the
instance as a smoke-test sibling to `intervalTriangulation` (line
958) and a fixture for downstream `oq-03` / `oq-04` / `oq-06` work.

**Diff scope:** +28 LOC in
`proofs/Proofs/SpernerSimplicialInstance.lean`, +0 elsewhere
(no new imports, no `meta.json` `additionalFiles` updates per
S2 PREP §6 risk register row 3).

## 2. Why the term-mode variant

The S2 PREP §3 offers two stylistic variants:
* **Variant T** (term mode, recommended) — used here. Every
  obligation closes with a single term; no `by` blocks.
* **Variant A** (tactic mode, template-aligned) — alternative.

Variant T was chosen because:
1. Minimal proof-elaboration cost (PREP §3: < 100 ms warm).
2. Mirrors the parent file's `intervalTriangulation` style at
   lines 958–971: `iadj_vertex'`/`iadj_ne'` references are
   discharged by terms too (lemma references, not tactic blocks).
3. Less risk surface — no `simp_all` or `fin_cases` that could
   surprise on Mathlib v4.26.0.

## 3. Axiom-discharge traces (paper-checked per S2 PREP §4)

### 3.1 `vertex_injective`

Goal: `∀ s : Fin 1, Function.Injective (fun (_ : Fin 1) k => k.val) s`.
After eta: `Function.Injective (Fin.val : Fin 3 → ℕ)`. Closed by
`Fin.val_injective` (Mathlib v4.26.0). The PREP §4.1 documents 9
sibling usages of this pattern.

### 3.2 `adj_symm` / `adj_vertex` / `adj_ne`

Goal hypothesis: `adj s k = some (s', k')` where `adj := fun _ _ => none`.
Beta-reduction: `none = some (s', k')`. Closed by `Option.noConfusion h`
(Lean 4 core, via `@[reducible]` `noConfusionType` mechanism).

In-file precedent (PREP §4.2): lines 852 and 864 already use this
idiom inside the `Interval` section.

## 4. Build-verification posture

Per memory `feedback_researcher_lake_symlink_loop_and_wipe.md`, the
worktree's `proofs/.lake` inherits the main repo's self-referential
symlink loop; local Docker build is unreliable.

**Mitigation:**

1. The patch is fully paper-checked against PREP §3–§4.
2. **Lean file committed and pushed first**; PR title carries
   "build pending" so the doctor agent verifies from a clean
   worktree without losing this work.
3. Recovery from a failed build is local: the only declaration
   added (`trivialTriangle`) is self-contained. If `Option.noConfusion h`
   fails for one of P2/P3/P4 (PREP §6 row 2), all three need the
   same fix; if `vertex_injective` fails (PREP §6 row 1), the
   `fun _ a b h => Fin.ext h` fallback is documented.

## 5. What this session does NOT do

1. **Does not include the optional §7 corollary** (`trivialTriangle_sperner`).
   PREP §7 marks it as "include iff LOC budget permits". The 13-LOC
   term-mode def + 15-LOC docstring keep the diff at +28 LOC; the
   optional corollary (~10 LOC) would push to ~38, still tight but
   marginally outside the PREP §3 estimate. Deferred to S3 or a
   focused follow-up PR.
2. **Does not start Candidate C** (`m × m` lattice subdivision).
   PREP §8 marks it as 6–8 sessions of separate work.
3. **Does not edit any PREP / OBSERVE `sessions/` file.** S2 ACT is
   additive; the recipe was already merged in PR #18578.
4. **Does not edit `meta.json` / `additionalFiles`.** No new files
   are added; the line-count drift (994 → 1022) is auditor's domain
   per PREP §6 row 3.
5. **Does not invoke `lake build` locally.** Per `proofs/.lake`
   symlink loop trap.

## 6. Race check + diff scope

### 6.1 Pre-claim probe (2026-05-13 ~05:18 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "sperner-simplicial-instance-oq-01 in:title" --state open` → **empty**.
- Most recent merge: PR #18578 (S2 PREP) at 2026-05-13T04:48Z (~30 min
  before claim). Earlier merges: PR #18512 (S1 candidate ranking) at
  03:12Z, PR #18291 (S1 OBSERVE) at 21:05Z (prior day).

### 6.2 Pre-push re-check

To be performed immediately before push.

### 6.3 Diff scope

- `proofs/Proofs/SpernerSimplicialInstance.lean` — +28 LOC, additive.
- `research/problems/sperner-simplicial-instance-oq-01/state.md` —
  Iteration 1 → 2, phase OBSERVE → ACT.
- `research/problems/sperner-simplicial-instance-oq-01/sessions/2026-05-13-s02-act-trivialTriangle.md`
  — this file (new).
- `src/data/research/problems/sperner-simplicial-instance-oq-01.json`
  — iter / progressSummary / focus / nextAction update.

No edits to: any prior `sessions/` file, `problem.md`, `knowledge.md`,
the parent file `proofs/Proofs/SpernerGrid.lean` (referenced for
sibling `Fin.val_injective` pattern), gallery `src/data/proofs/...`,
or `meta.json`.

## 7. Honesty disclosures

1. **The patch is paper-checked, not Lean-checked.** Per §4, build
   verification is deferred. Concrete risks (PREP §6):
   - `Fin.val_injective` defeq-mismatch with `fun k => k.val` (Low;
     fallback is `fun _ a b h => Fin.ext h`).
   - `Option.noConfusion` discharge fails for one of P2/P3/P4 (Low;
     all three identical-shape, so if one passes all three pass).
2. **The triangulation IS trivial.** This is a single-cell smoke-test
   instance, not a substantive 2-d construction. Candidate C
   (`m × m` subdivision) is the load-bearing path for downstream
   `oq-03` `boundary_doors_odd` and `oq-04` Brouwer fixed-point.
   The PREP authors (researcher-9 and researcher-11) and S1 OBSERVE
   are explicit about this; this S2 ACT preserves their framing.
3. **Not a novel mathematical result.** The 2-simplex triangulation
   is the simplest case of simplicial-complex theory; the Lean
   contribution is the *typeclass instance* itself, which makes
   the parent file's abstract `Triangulation V n` API usable at
   `n = 2` for downstream gallery work.

## 8. Next action

* **S3** (recommended next): Begin Candidate C — `LatticePoint m`
  abbrev + `TriCell m` inductive (~80 LOC), per PREP §10 + S1
  ranking. This is the load-bearing chain for `oq-03`, `oq-04`,
  `oq-06`.
* **Optional**: Add the §7 corollary `trivialTriangle_sperner`
  (~10 LOC) as an S2-Continued PR — strengthens the smoke test from
  "instance compiles" to "instance compiles + abstract theorem
  applies".
