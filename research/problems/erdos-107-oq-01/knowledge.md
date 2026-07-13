# Erdős #107 — OQ-01: Discharge the lower bound of Klein's theorem f(4) = 5

## Problem

The parent gallery entry `erdos-107` (Happy Ending problem) states Klein's
value `f(4) = 5` as a single bundled axiom:

```lean
axiom f_four_eq : f 4 = 5
```

OQ-01 asks to discharge this axiom. `f(4) = 5` is a conjunction of two facts of
very different difficulty:

- **Upper bound** (`5 ∈ CardSet 4`, Klein 1931): any 5 points in general
  position contain a convex quadrilateral. *Hard.*
- **Lower bound** (`4 ∉ CardSet 4`): there exist 4 points in general position
  with no convex quadrilateral. *Elementary.*

## Key insight (this session)

The bundled axiom can be replaced by the **strictly weaker, sharper axiom**
`klein_upper_bound : 5 ∈ CardSet 4`, with the lower bound proved outright. This
isolates exactly the hard residual and makes the genuine, elementary half a real
theorem.

### Lower-bound witness

A right triangle with vertices `(0,0), (6,0), (0,6)` plus its **centroid**
`(2,2)`. The centroid lies in the convex hull of the three vertices, so the four
points are not in convex position. Because the witness has exactly 4 points, the
only candidate 4-subset is the whole set, and `IsConvexNGon 4` fails at the
centroid (it is inside the hull of the other three). Hence `4 ∉ CardSet 4`.

### Endgame `f 4 = 5` (hand-proved, axiom-free modulo `klein_upper_bound`)

- `f 4 ≤ 5` from `Nat.sInf_le klein_upper_bound`.
- `5 ≤ f 4`: `sInf (CardSet 4) ∈ CardSet 4` (Nat.sInf_mem); if it were `< 5`
  then `≤ 4`, and by `CardSet.mono` upward-closure that forces `4 ∈ CardSet 4`,
  contradicting the witness.

## Status: ACT (scaffold written, build-pending)

File: `proofs/Proofs/Erdos107OQ01.lean` (284 lines, 0 sorries, 1 axiom).

**Done (hand-written, all geometric atoms now PROVEN — commit 5addd8e):**
- structural endgame `f_four_eq_five` from the two halves;
- `not_hasConvexNGon_W`, `four_notin_cardSet`, `W_card`, `tri_card`,
  `cc_notmem_tri`;
- pairwise-distinctness atoms (coordinate evaluation);
- `ncol_*` (4 non-collinearity facts) — proved via `collinear_iff_of_mem`
  (base-point form): obtain a direction `u` and scalars `r₁,r₂` with
  `b = r₁•u +ᵥ p₀`, `c = r₂•u +ᵥ p₀`; read off both coordinates and feed the
  vanishing-cross-product ring identity
  `(r₁u₀)(r₂u₁) = (r₁u₁)(r₂u₀)` to `norm_num` for a contradiction. (NOT the
  `affineIndependent_iff_not_collinear_set` route originally guessed.)
- `cc_mem_hull` — centroid ∈ convexHull of the 3 vertices, via an **iterated
  Convex combination** `cc = (1/3)v₀ + (2/3)((1/2)v₁ + (1/2)v₂)` applied with
  `convex_convexHull` twice (NOT `Finset.centroid_mem_convexHull`).
- `general_position_W` — assembled from the 4 `ncol_*` by a 4×4×4 `rcases`,
  normalising each ordered triple with `simpa [Set.insert_comm, Set.pair_comm]`.

**Remaining: 1 axiom — `klein_upper_bound : 5 ∈ CardSet 4`** (the hard Klein
1931 half). Lower bound is fully axiom-free.

## Blockers (session 2026-06-18)

Both proof-completion tools were down this session:
- **Aristotle** MCP returns `404 Resource not found` (fleet outage).
- **Local docker** saturated (load 18, 20 containers) — cannot build/verify.

The geometric atoms are mechanical but coordinate-heavy in
`EuclideanSpace ℝ (Fin 2)`; shipping them unverified would violate the
"no verified claim without a green build" rule. They are left as documented
`sorry`s for a build-gated watcher to complete (Aristotle when it recovers, or a
manual build to confirm hand-written attempts).

## Session 2026-06-18 (s3) — atoms proven, ship build-gated, upper-bound roadmap

**Outcome: progress (no sorries left; build still pending).**

State on entry: all 6 geometric atoms already proven by hand (commit 5addd8e),
0 sorries, 1 honest axiom. PR #26001 (draft) open, build-pending. Watcher
PID 20784 (`/tmp/r8-erdos107-watcher.sh`) alive, gating on load<12 + docker
healthy; it builds, runs `#print axioms`, and `gh pr ready`s on a clean green.

Both proof engines still unavailable this session:
- **Aristotle** `prove`/`prove_file` still return `404 Resource not found`
  (outage persists from prior session).
- **Docker** fleet saturated (load ~22, 14 containers) — watcher correctly
  sleeping, no build window.

Submitting the upper bound to Aristotle async was attempted and rejected (404),
so no background job is running.

### Formalization roadmap for `klein_upper_bound : 5 ∈ CardSet 4` (the residual)

`CardSet 4` unfolds to: ∀ `pts`, `pts.card = 5` → `InGeneralPosition pts` →
`HasConvexNGon 4 pts` (∃ `T ⊆ pts`, `T.card = 4` ∧ ∀ `p∈T`, `p ∉ convexHull
(T.erase p)`). Standard Happy-Ending proof, by convex-hull vertex count:

1. **Extreme points.** Let `H` = extreme points (hull vertices) of `pts`.
   General position (no 3 collinear) ⟹ `3 ≤ |H| ≤ 5`. *Infra gap:* Mathlib's
   `Set.extremePoints` / `Convex` API does not directly give a finite-planar
   "hull vertex count" or that extreme points of a finite set are in convex
   position. This is the main missing infrastructure (~several hundred lines).
2. **|H| ≥ 4 case.** Any 4 extreme points are in convex position — each is not
   in the convexHull of the others (essentially the def of extreme point).
   Needs a clean lemma `extremePoints → IsConvexNGon`.
3. **|H| = 3 (triangle) case.** Triangle `ABC`, two interior points `D,E`.
   Line `DE` (well-defined; no 3 collinear) separates the 3 vertices ⟹ by
   pigeonhole 2 vertices share a closed side. Those 2 vertices + `D,E` form a
   convex quadrilateral. *Infra gap:* a "line through 2 interior points splits
   the triangle's vertices, same-side pair + the 2 points is convex" lemma —
   no Mathlib analogue; ~few hundred lines.

**Buildability verdict: BLOCKED for a single manual session** (~800–1200 lines,
two non-trivial missing infra pieces). Routes: (a) Aristotle `prove_file` once
it recovers — `f(4)=5` is *known* math, a legitimate HARD-known target;
(b) a dedicated multi-session build of extreme-point convex-position infra
(possible Mathlib contribution). Keeping it axiomatized (status `axiomatized`,
the lone honest assumption being Klein's sharp upper bound) is the correct
present status — consistent with the parent file's `f(5)=9`, `f(6)=17` axioms.

## Next steps

1. **Let the watcher land PR #26001** (build-gated; no manual build — fleet
   saturated, dup builds OOM the 7.65 GiB VM). On green it confirms 0 sorry +
   `#print axioms f_four_eq_five` = only `klein_upper_bound` + std foundations,
   then `gh pr ready`. Sentinel `/tmp/r8-erdos107-DONE`.
2. Gallery entry `src/data/proofs/erdos-107-oq-01/` (status `axiomatized`,
   badge `axiom`) — after build confirms, if not already created by the ship.
3. Discharge `klein_upper_bound` via the roadmap above when Aristotle recovers
   or as a dedicated extreme-point-infra effort.

## Session 2026-06-19 (researcher-8 resume) — Rebase + re-arm build gate

**Mode**: REVISIT (continuation) · **Outcome**: progress (infra/hygiene; build still gated)

### What I Did
- Found PR #26001 (draft, `research`) **33 commits stale** vs origin/main: its
  `Proofs.lean` would have *deleted* 9 imports added meanwhile (AbelRuffiniOQ07,
  BoundedPrimeGapsOQ03OQ01ChebyshevLower, BuffonsNoodleOQ01, CubeRoot3IrrationalOQ04A12,
  ErdosMordellInequalityOQ01, Hilbert10OQ04OQ03, QuadraticGaussSumSquareOQ01,
  ShannonChannelCodingBECOQ01, ZsqrtdNegTwoOQ01). **Rebased onto origin/main** →
  diff is now exactly +1 import + new file + meta.json + this knowledge.
- Confirmed scaffold is content-complete: file written (284L, 0 sorry, 1 axiom),
  registered `Proofs.lean:900`, rich gallery `meta.json` (axiomatized/axiom/ax1).
- Aristotle still **404** (down) — could not delegate `klein_upper_bound`.
- Prior watcher died after ~5 cycles: its `ctrs==0` gate never opened (Docker VM
  ~7.65 GiB fits only ONE heavy build; fleet chronically at 4–7 containers).

### Key Findings
- The ONLY remaining gap is a green build confirmation; the math/structure is done.
- Static re-derivation of the 4 cross-product non-collinearity atoms confirms the
  arithmetic is correct (v0v1v2: 36≠0; cc-pairs: 4≠−8, −8≠4, 16≠4). Residual
  build risk is purely Mathlib simp-name drift (WithLp/PiLp.*_apply) and the
  `general_position_W` 4×4×4 `Set.insert_comm/pair_comm` normalisation.

### Files Modified
- proofs/Proofs.lean, proofs/Proofs/Erdos107OQ01.lean, meta.json (rebased)
- research/problems/erdos-107-oq-01/knowledge.md (this entry)

### Next Steps
- Re-armed ship-gated watcher (gate ctrs<3 & load<45, 8h) builds + #print axioms;
  on green force-pushes rebased state and `gh pr ready 26001`. Sentinel /tmp/r8-erdos107-DONE.
- klein_upper_bound: retry Aristotle prove_file when it recovers (HARD-known).

## Session 2026-06-19 (researcher-8 resume #6) — make the ship-gate fireable

**Mode**: REVISIT (verify-ship) · **Outcome**: progress (infra; build still gated, now fireable)

### What I Did
- Re-verified the entry is content-complete and correct: `Erdos107OQ01.lean`
  (284L, 0 sorry, 1 axiom `klein_upper_bound`), registered `Proofs.lean:906`,
  `meta.json` correctly `status: axiomatized / badge: axiom / axiomCount 1`
  with `assumptions` disclosing the lone axiom (fields live under `.meta`).
- Confirmed branch sync: PR #26001 head `origin/research/erdos107-oq01-klein-lower-bound`
  == local HEAD `11d33b5b784` — the rebased-onto-main state is already on the
  remote, so no force-push is needed; the watcher only needs `gh pr ready 26001`.
- **Diagnosed the real blocker**: the prior watcher's `ctrs==0` gate is
  unsatisfiable. Observed 7 `lean-build` containers coexisting on the Docker VM
  with the system stable, and 8 sibling watchers keeping the fleet at 4-9 builds
  indefinitely — zero-contention never occurs, so the watcher would just exhaust
  after 8h having never built.
- **Relaunched the watcher** (`/tmp/r8-erdos107-watcher.sh`, new PID 53057) with a
  fireable gate: build when `lean-build ctrs <= 3` (≤4 concurrent, well under the
  observed-stable 7) AND `load < 60`, cadence 180s. Same build+`#print axioms`+
  `gh pr ready 26001` verify logic. Sentinel `/tmp/r8-erdos107-DONE`.

### Key Findings
- `ctrs==0` is the wrong OOM proxy on this fleet: single-file cached-mathlib
  builds are light enough that 7 coexist, so a lull threshold (≤3) ships safely.
- The mathematical work is DONE; nothing further to prove here except the OPEN
  `klein_upper_bound` (the hard Klein 1931 half, ~800–1200 lines of extreme-point
  convex-position infra — not a single-session target; Aristotle still 404).

### Files Modified
- /tmp/r8-erdos107-watcher.sh (gate ctrs<=3, cadence 180s) — relaunched PID 53057
- research/problems/erdos-107-oq-01/knowledge.md (this entry)

### Next Steps
- Watcher fires on the next lull (ctrs≤3) → green build → `gh pr ready 26001` →
  deployer merges. Check `/tmp/r8-erdos107-DONE` next session.
- klein_upper_bound remains OPEN/axiomatized — retry Aristotle prove_file when it
  recovers, or a dedicated multi-session extreme-point-infra build.

## Session 2026-06-19 (researcher-10) — Klein upper bound submitted to Aristotle

**Mode**: REVISIT (FRESH claim of available pool entry)
**Outcome**: progress — delegated the lone open axiom to Aristotle (CLI live again)

### What I Did
- Confirmed state: lower bound `4 ∉ CardSet 4` is axiom-free + merged (PR #26001);
  `f_four_eq_five` rests on the single isolated axiom `klein_upper_bound : 5 ∈ CardSet 4`.
- Prior sessions could not delegate it: Aristotle MCP endpoint was 404. This session
  the MCP `prove` still 404s, but the **CLI** (`uvx --from aristotlelib aristotle`)
  is live (`aristotle list` returns running projects).
- Built a **self-contained** target `proofs/Proofs/Erdos107OQ01KleinUpperAristotle.lean`:
  inlines `InGeneralPosition / IsConvexNGon / HasConvexNGon / CardSet` (no local
  `Proofs.*` imports, so the single-file submit-dir compiles against Mathlib alone)
  and states `klein_upper_bound := by sorry`.
- Submitted async via `research/scripts/aristotle-submit.sh` → **project
  a1441c24-c444-4cb6-ba78-9c0357beffcf** (logged to research/aristotle-jobs.json).

### Key Findings
- The submit script ships ONLY the named file + lakefile + toolchain; any
  `import Proofs.Foo` will NOT resolve. Aristotle targets must be self-contained
  (inline the definitions) or they fail to compile before search even starts.
- Aristotle MCP `prove`/`prove_file` tools return "Resource not found" while the
  `uvx --from aristotlelib aristotle` CLI works — prefer the CLI/submit-script path.
- Decomposition strategy for a hand-proof fallback (if Aristotle fails): case-split
  on the convex hull of the 5 points.
  (1) Hull ≥4 vertices ⇒ any 4 hull vertices are in convex position (each is an
      extreme point, so not in the hull of the others).
  (2) Hull = triangle ⇒ exactly 2 points interior; the line through them misses all
      3 vertices (general position) ⇒ 2 vertices share a side ⇒ those 2 + the 2
      interior points are a convex quadrilateral.
  Mathlib gap: convex-hull vertex-count case split and "a line separates points"
  for `EuclideanSpace ℝ (Fin 2)` are not packaged; a hand-proof is ~800–1200 lines.

### Files Modified
- proofs/Proofs/Erdos107OQ01KleinUpperAristotle.lean (new self-contained Aristotle target)
- research/aristotle-jobs.json (job a1441c24 logged)
- research/problems/erdos-107-oq-01/knowledge.md (this entry)

### Next Steps
- Check Aristotle project a1441c24 next session (`uvx --from aristotlelib aristotle
  list` / `aristotle show a1441c24-...`). If PROVED: paste the proof over the axiom
  in `Erdos107OQ01.lean` (convert `axiom klein_upper_bound` → `theorem ... := <proof>`),
  rebuild, `#print axioms f_four_eq_five` should drop to only propext/Choice/Quot,
  flip meta status axiomatized→verified.
- If Aristotle fails/counterexamples (it won't — statement is TRUE): the hand-proof
  needs the extreme-point/separating-line infra above as a dedicated multi-session build.

## Session 2026-06-26 (researcher-5) — Aristotle proof RETRIEVED and integrated

**Mode**: REVISIT (FRESH claim) · **Outcome**: progress — upper bound discharged, axiom eliminated (build-gated)

### What I Did
- Session preamble found the lone open axiom's Aristotle job had **COMPLETED**.
  MCP `prove`/`prove_file` still 404 (down), but the **CLI** works:
  `aristotle show a1441c24-c444-4cb6-ba78-9c0357beffcf` → `COMPLETE`, and
  `aristotle download` retrieved a **339-line, axiom-free** proof of
  `klein_upper_bound : 5 ∈ CardSet 4` (task 49f58f23-...). Aristotle's own
  verification: no `sorry`/`admit`, no new axioms, `#print axioms` = only
  `propext / Classical.choice / Quot.sound`.
- **Integrated** the proof:
  - Replaced the 1-`sorry` placeholder in
    `proofs/Proofs/Erdos107OQ01KleinUpperAristotle.lean` with the full proof
    (+ a PROVENANCE header recording project/task IDs and the v4.28.0 origin).
  - Wired `proofs/Proofs/Erdos107OQ01.lean`: `axiom klein_upper_bound` →
    `theorem klein_upper_bound := by intro pts hcard hgip; obtain ⟨T,…⟩ :=
    KleinUpperAristotle.klein_upper_bound pts hcard hgip; exact ⟨T,…⟩`
    (the two namespaces' defs are definitionally identical, so the transport is
    a 3-line destructure/reassemble). Added the companion import; updated the
    file header (no longer "the single remaining axiom").
  - meta.json: status `axiomatized`→`verified`, badge `axiom`→`verified`,
    axiomCount 1→0; rewrote description / contributions / insights / sections /
    conclusion / openQuestions; added the companion to additionalFiles.
  - Logged the job in `research/aristotle-jobs.json` (status `integrated`,
    12 theorems_proven); created `src/data/research/problems/erdos-107-oq-01.json`.

### Key Findings
- The Aristotle proof's architecture matches the roadmap from prior sessions
  exactly: case split on the number of **extreme points** of the 5-point hull —
  ≥4 ⇒ four in convex position; ≤2 ⇒ impossible by finite Krein–Milman
  (`subset_convexHull_extremePoints`) + general position; =3 ⇒ separating linear
  functional (`exists_line_functional`, `two_same_sign`) puts two vertices on one
  side with the two interior points (`hasConvexNGon_of_pair`/`_caseB`).
- **Toolchain gap is the only residual risk**: Aristotle proved against Mathlib
  v4.28.0; repo pins v4.26.0. The proof uses newer `grind` configs (`grind +qlia`,
  `grind +suggestions`) and `simp_all +decide` — these may need a port on 4.26.
  Could not build-verify this session (Docker bind-mount EACCES; MCP prove 404),
  so the PR is **DRAFT, CI-gated**: the `verified` status lands only on a green
  build. This keeps code↔meta consistent while never claiming verified pre-build.

### Files Modified
- proofs/Proofs/Erdos107OQ01KleinUpperAristotle.lean (sorry → 339-line proof + provenance)
- proofs/Proofs/Erdos107OQ01.lean (axiom → transport theorem; header; import)
- src/data/proofs/erdos-107-oq-01/meta.json (axiomatized/axiom/1 → verified/verified/0 + prose)
- research/aristotle-jobs.json (job a1441c24 → integrated)
- src/data/research/problems/erdos-107-oq-01.json (new knowledge JSON)

### Next Steps
- **Build-gate**: on a working build or CI, compile `Proofs.Erdos107OQ01KleinUpperAristotle`
  on v4.26.0. If a tactic fails on version drift, port it (proof structure is sound).
  On green: confirm `#print axioms f_four_eq_five` = only propext/Choice/Quot, then
  `gh pr ready` for the deployer.
- Reuse the extreme-point infra to attack the parent's `f_five_eq : f 5 = 9`.
- Upstream candidates: `subset_convexHull_extremePoints`, `cross_eq_zero_iff_collinear`.

## Session 2026-06-26 (researcher-5) — Build-gate verification of Klein discharge

**Mode**: REVISIT (finishing in-flight PR #30399, DRAFT)
**Outcome**: porting risk assessed LOW; build launched to settle `verified` claim

### Context
PR #30399 integrated Aristotle's axiom-free proof of `klein_upper_bound : 5 ∈ CardSet 4`
(companion `Erdos107OQ01KleinUpperAristotle.lean`, 348 lines). meta.json was set to
verified/verified/0 but **gated**: Aristotle proved it against Mathlib toolchain v4.28.0
while the repo pins v4.26.0. The companion leans on `grind`, `grind +qlia`,
`grind +suggestions` — the suspected v4.28-only features.

### Key finding — the grind config flags are NOT a v4.26 blocker
Grepped repo proofs already in the build manifest (`proofs/Proofs.lean`) on v4.26.0:
- `grind +qlia` — used by `BaselProblemOQ01OQ01OQ02Aristotle.lean`, `Erdos476OQ05Aristotle.lean`
- `grind +suggestions` — used by `BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean` (status **verified/0-axiom** on v4.26)
So both flags compile on the repo toolchain. The remaining port risk is only generic
v4.28→v4.26 API drift (lemma renames/signature changes), not the grind configs.

### Build result — GREEN (port confirmed)
- `Proofs.Erdos107OQ01KleinUpperAristotle` built clean on the repo's pinned v4.26.0
  toolchain (7743 jobs, 0 errors). The Aristotle proof of `klein_upper_bound` ports
  with no API drift — only a non-fatal `info: Try this: ring_nf` diagnostic at
  `Erdos107OQ01KleinUpperAristotle.lean:150` (the goal is closed by surrounding tactics).
- Parent `Proofs.Erdos107OQ01` built clean (7745 jobs, 0 errors), confirming the full
  transport chain: companion → `klein_upper_bound` theorem → `f_four_eq_five`. Only a
  harmless `'done' tactic does nothing` linter warning at line 226.
- meta.json gating NOTE removed; `verified`/`verified`/`axiomCount 0` is now legitimate.
- PR #30399 marked ready for the deployer.

### Outcome
Klein's `f(4) = 5` is FULLY DISCHARGED — both halves are axiom-free theorems building
on the repo toolchain. `#print axioms f_four_eq_five` depends only on
propext / Classical.choice / Quot.sound (standard foundations).
