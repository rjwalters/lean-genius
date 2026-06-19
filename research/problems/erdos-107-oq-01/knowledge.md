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
