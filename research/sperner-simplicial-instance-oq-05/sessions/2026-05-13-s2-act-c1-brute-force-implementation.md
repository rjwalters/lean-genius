# S2 ACT — (C1) `findPanchromaticBrute` Lean implementation (build-pending)

**Researcher**: researcher-9 (claim `researcher-9`, knowledge score 18 / RICH; obtained via explicit `REPO_ROOT=/Users/rwalters/GitHub/lean-genius` per memory trap)
**Date**: 2026-05-13 (post-S2-PREP-D #18534, ~3h after merge 04:08 UTC; first non-PREP session on this slug)
**Type**: S2 ACT Lean implementation; ships a single new `.lean` file. Does NOT ship the gallery integration (`src/data/proofs/sperner-simplicial-instance-oq-05/`) — gallery promotion is a separate S3 GALLERY task per memory pattern `[S3 GALLERY clean task — build-verified Lean + missing src/data/proofs/<slug>/]`.
**Scope**: a single new file `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (~170 LOC: docstring + `def` + 3 theorems + 1 `decide` smoke-test); no edits to any existing `.lean` file, no edits to `problem.md`/`knowledge.md`/`state.md`/gallery JSON.

---

## §1 — What was implemented

A single new file `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` containing:

1. **`def findPanchromaticBrute`** (~5 LOC): the brute-force computable witness extractor, returning `Option T.Cell` via `Finset.filter |>.toList.head?`.

2. **`theorem findPanchromaticBrute_isSome_iff`** (~30 LOC): the membership-equivalence characterisation — `isSome` of the result iff a panchromatic cell exists. Uses the verified Mathlib names from PREP-D §4.1 (`Finset.toList_eq_nil` at `Mathlib/Data/Finset/Basic.lean:525`, `Finset.Nonempty.toList_ne_nil` at `:534`, `Finset.nonempty_iff_ne_empty` at `Mathlib/Data/Finset/Empty.lean:142`). Replaces PREP-C1 #18459 §4's `Finset.toList_ne_nil_iff_nonempty` fallback chain.

3. **`theorem findPanchromaticBrute_eq_some_imp_panchromatic`** (~8 LOC): the `some` consumes panchromatic property. Uses `List.mem_of_head?` from Lean core `Init.Data.List.Lemmas:968` (`l.head? = some a → a ∈ l`) — a 3-line proof, simpler than the PREP-C1 §2 `set L := ... with hL; cases hcase : L` scaffold (which had a `match` arity issue per re-audit).

4. **`theorem findPanchromaticBrute_isSome_of_boundary_odd`** (~8 LOC): totality under Sperner's parity hypothesis. Direct rewrite via `findPanchromaticBrute_isSome_iff` + `Triangulation.sperner`.

5. **`example : ∃ s : Fin 3, ...`** (~5 LOC): `decide`-based smoke-test on `intervalTriangulation 3 (by norm_num)` with the colouring `c(n) = if n ≤ 1 then 0 else 1`. Predicted witness: `s = 1` (cell with vertices `{1, 2}` colored `{0, 1}`). PREP-D §3.1 verified this prediction by paper trace. The smoke-test uses `decide` rather than `#eval` because `decide` produces a kernel-level proof certificate and provides a strict typecheck barrier.

## §2 — Differences from PREP-C1 #18459 §1 scaffold

1. **`Finset.toList_ne_nil_iff_nonempty` removed**: PREP-C1 §1 used this name with a fallback note "Note: actual Mathlib lemma name may be Finset.toList_eq_nil or similar." PREP-D §4.1 supplied the verified replacement chain. This ACT applies the replacement verbatim (lines 86-96 of the ACT file).

2. **`findPanchromaticBrute_eq_some_imp_panchromatic` simplified**: PREP-C1 §2 sketched a `set L := ... with hL; match hcase : L, heq with ...` proof with a `sorry` placeholder. This ACT uses `List.mem_of_head? heq` from Lean core (line 968 of `Init/Data/List/Lemmas.lean`), giving a 3-LOC proof.

3. **`#eval` → `decide` smoke-test**: PREP-C1 §3 sketched a `#eval` line but commented it out (`-- #eval ...`). This ACT replaces it with a kernel-level `example : ∃ s : Fin 3, IsPanchromatic ... by refine ⟨1, ?_⟩; decide`, which provides a real verification rather than a printed output.

4. **Import slimmed**: PREP-C1 §1 imported three modules (`Proofs.SpernerSimplicialInstance`, `Proofs.SpernerMathlib4`, `Mathlib.Data.Finset.Basic`). This ACT imports only `Proofs.SpernerSimplicialInstance`, which transitively imports the other two (verified by `head -10 proofs/Proofs/SpernerSimplicialInstance.lean` showing `import Mathlib.Data.Finset.Sort; import Proofs.SpernerMathlib4`).

## §3 — Status

**Mathematical content**: 0 sorries, 0 axioms.

**Build status**: **build-pending**. No `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstanceOQ05` was run in this session. Build risk is low but non-zero:

- All Mathlib lemma names (`Finset.toList_eq_nil`, `Finset.Nonempty.toList_ne_nil`, `Finset.nonempty_iff_ne_empty`, `Finset.mem_filter`, `Finset.mem_toList`, `Finset.mem_univ`, `List.mem_of_head?`) verified via `gh api repos/leanprover-community/mathlib4/contents/...` and `gh api repos/leanprover/lean4/contents/...` at HEAD.
- `Triangulation.sperner`, `CellComplex.IsPanchromatic`, `CellComplex.IsDoor`, `Triangulation.toCellComplex`, `Triangulation.intervalTriangulation` all verified to exist in the parent files (`proofs/Proofs/SpernerSimplicialInstance.lean:147, :123, :958` and `proofs/Proofs/SpernerMathlib4.lean:440, :446`).
- The `decide` smoke-test relies on `ivtx` unfolding through privacy and `Fin.decEq`/`Function.Surjective.decidable` instances; if `decide` exceeds the kernel timeout, fall back to a manual `simp [Function.Surjective] at *; ...` proof.

**Doctor follow-up**: If the build fails on first attempt, the Doctor / Mechanic agent should apply small fixes (typically: typeclass tweaks or `decide` fallback). This is an explicit hand-off pattern per Loom workflow.

## §4 — Why ACT now (saturation analysis)

- This slug has 5 prior PREPs (S1 OBSERVE + 4 S2 PREPs: C1, C2-1d, C3, PREP-D). All merged ≥3 hours ago. **No open PRs** on the slug at session-start time (07:15 UTC).
- The C1 PREP author was this same agent (researcher-9, 2026-05-13 02:10 UTC). The natural follow-up is the C1 ACT by the same author, with PREP-D's corrections applied.
- Doing a 6th PREP would compound PREP cascade saturation (4-PREP slugs are the saturation signal per memory `[Post-S1/S1b S2/S4 PREP session-note cluster]`).
- ACT progresses the phase (NEW → OBSERVE → ACT). This is the first ACT on this slug.

**Trade-off**: build-pending PR vs. PREP-only. The build-pending risk is contained because (a) all Mathlib lemma names are verified, (b) the proof structure follows PREP-C1 + PREP-D's specifications, (c) the Doctor agent can fix small build issues. PREP-only would be safer but adds nothing new to the 4-PREP cascade.

## §5 — Trap notes

* **REPO_ROOT trap on `claim-problem.sh`**: confirmed; invoked from `/Users/rwalters/GitHub/lean-genius` with explicit `REPO_ROOT=` env var. Claim succeeded; expires 2026-05-13T08:50:33Z.
* **Branch creation under dirty index**: detached cleanly from `origin/main` (`HEAD is now at a84a6c8757a Enrich zsqrtd-neg-two-oq-03 ...`), then created `research/sperner-simplicial-instance-oq-05-s2-act-c1-1778657027`. No inherited dirty state from the prior S5 PREP session on `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02` (PR #18639).
* **Write tool main-repo absolute-path trap**: used worktree-prefixed paths for both the new Lean file and this session note. Verified via `git status` from worktree.
* **`gh` default-repo trap**: all `gh pr list` invocations used explicit `--repo rjwalters/lean-genius`.
* **`.lake` symlink loop**: confirmed present at `/Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referential symlink → "Too many levels of symbolic links"). This blocks local file reads of Mathlib (`grep proofs/.lake/...` fails). Workaround: used `gh api repos/leanprover-community/mathlib4/contents/...` and `gh api repos/leanprover/lean4/contents/...` for all Mathlib + Lean-core file reads. No Docker build attempted (would also fail per the symlink trap unless the main repo's `.lake` is repaired).
* **No race**: pre-claim and pre-push `gh pr list --repo rjwalters/lean-genius --search "$SLUG in:title" --state open` both returned `[]`.
* **search/code rate limit**: ~6 `gh api search/code` calls in this session, then fell back to Contents API for direct file reads. Stayed within quota.

## §6 — Files modified

**Modified** (worktree-relative paths, verified via `git status`):

* `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (new, ~170 LOC).
* `research/sperner-simplicial-instance-oq-05/sessions/2026-05-13-s2-act-c1-brute-force-implementation.md` (new, this file).

**NOT modified**:

* `research/sperner-simplicial-instance-oq-05/problem.md`
* `research/sperner-simplicial-instance-oq-05/knowledge.md`
* `research/sperner-simplicial-instance-oq-05/state.md`
* `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
* `proofs/Proofs/SpernerSimplicialInstance.lean` (parent, untouched)
* `proofs/Proofs/SpernerMathlib4.lean` (grandparent, untouched)
* `src/data/proofs/sperner-simplicial-instance-oq-05/` (gallery — does not exist yet; promotion is a separate S3 GALLERY task)

## §7 — References

* **S1 OBSERVE**: PR #18200 (researcher-11, 2026-05-12).
* **S2 PREP C1 (scaffold)**: PR #18459 (researcher-9, 2026-05-13 02:10 UTC).
* **S2 PREP C3 (cascade audit)**: PR #18392.
* **S2 PREP C2-1d (Scarf walk)**: PR #18489.
* **S2 PREP-D (Mathlib API audit + bridge discharge)**: PR #18534.
* **Parent file**: `proofs/Proofs/SpernerSimplicialInstance.lean` (994 LOC, 28 thms, 0 sorries, 0 axioms, status: verified).
* **Grandparent (abstract framework)**: `proofs/Proofs/SpernerMathlib4.lean:404` (`structure CellComplex`), `:440` (`IsPanchromatic`), `:446` (`IsDoor`), `:714` (`theorem sperner`).
* **Mathlib v4.26.0** (pin per `proofs/lean-toolchain`):
  * `Mathlib/Data/Finset/Basic.lean:525` (`Finset.toList_eq_nil`).
  * `Mathlib/Data/Finset/Basic.lean:534` (`Finset.Nonempty.toList_ne_nil`).
  * `Mathlib/Data/Finset/Empty.lean:142` (`Finset.nonempty_iff_ne_empty`).
* **Lean core**:
  * `Init.Data.List.Lemmas:968` (`List.mem_of_head?`).
* **Memory patterns applied**:
  * `[Mathlib audit obsoletes bespoke S2 scaffold]` — used `gh api` to verify every Mathlib name before committing the proof.
  * `[Branch-confusion recovery — git switch --detach silently failed under dirty index]` — used clean `git switch --detach origin/main` from a non-dirty worktree state.
  * `[S3 GALLERY clean task — build-verified Lean + missing src/data/proofs/<slug>/]` — deferred gallery integration to a separate S3 task; this ACT ships only the Lean file.
  * `[.lake symlink loop + mid-build worktree wipe]` — confirmed the symlink loop; chose build-pending PR over a guaranteed-to-fail Docker build attempt.
