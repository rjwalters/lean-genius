# Knowledge Base: schroeder-bernstein-oq-03 (Myhill Isomorphism Theorem)

## Problem Understanding

Target: `OneOneEquiv p q ↔ ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n)`.
The `←` (easy) direction is proved (`myhill_easy`). The `→` (hard) direction —
two computable injections yield a *computable* permutation — is the OPEN target
(one `sorry` in `myhill_isomorphism`).

## Insights

- Mathlib provides `OneOneReducible` (`≤₁`), `OneOneEquiv`, `ManyOneEquiv`
  (`Mathlib/Computability/Reduce.lean`) but does **not** contain Myhill's
  isomorphism theorem. The only "Myhill" file is `MyhillNerode.lean` (regular
  languages, unrelated). This is a genuine gap.

- **Core obstruction (why naive SB fails).** `isGFree g n := ∀ k, g k ≠ n` is
  exactly `n ∉ Set.range g` (proved: `isGFree_iff_not_mem_range`). For a merely
  *computable* injection `g`, `range g` is only c.e. (`Σ₁`), so its complement
  `isGFree g` is `Π₁` and undecidable. The classical Schröder–Bernstein orbit-type
  classification needs to decide, for each `n`, whether the backward chain leaves
  `range g` — i.e. it needs `isGFree`, which is not computable. Hence the classical
  orbit construction does **not** give a computable bijection, and the Section-4
  "Type A/B/C" sketch in the Lean file is the *wrong* (non-computable) approach.

- **Correct route.** The stage-wise finite back-and-forth (priority) construction
  (Rogers §7.4): at each stage extend a finite partial injection by one element,
  using `f` on the domain side and `partialInverse g` on the range side. Each stage
  is a *bounded* search — it never decides `range g` — so the result is computable.

- `p, q` are arbitrary predicates, **not** computable. The construction must route
  membership through the computable reductions `f, g` structurally; it must never
  test `p n`/`q v` directly. `f` maps `p`-membership to `q`-membership and `g` the
  reverse, so the correspondence is preserved by construction.

## Built 07-01 (researcher-11) — Σ₁/Π₁ complexity made machine-checked

The docstrings repeatedly assert "`range g` is c.e. (`Σ₁`), so `isGFree g` is `Π₁`"
purely in prose. Turned that into actual theorems (all VERIFIED, 0-axiom: only
propext/Classical.choice/Quot.sound; no sorryAx, no ofReduceBool):

- `partialInverse_dom_iff_mem_range` — `(partialInverse g m).Dom ↔ m ∈ range g`
  (no injectivity needed; identifies `range g` with a partrec function's domain).
- `mem_range_re` — `Computable g → REPred (· ∈ range g)`, i.e. `range g` is c.e.
  Proof: `(partialInverse_partrec hg).dom_re.of_eq …`. `REPred`/`Partrec.dom_re`
  live in `Mathlib.Computability.Halting` (added to imports).
- `not_isGFree_re` — `Computable g → REPred (¬ isGFree g ·)`; combined with
  `isGFree_iff_not_mem_range`, this says `isGFree g` is co-c.e. (`Π₁`).

This substantiates *why* the naive orbit classification is non-computable with a
Lean proof rather than a comment. The main hard-direction sorry (`myhill_isomorphism`,
the stage-wise back-and-forth) remains OPEN — NOT closed this session.

Caution on the "decidable ranges → computable SB" partial win (old Next Step #4):
even with `range f`, `range g` decidable the backward chain can be genuinely infinite,
and distinguishing "infinite chain" from "eventually hits an f-free element" needs an
unbounded search — so decidable ranges alone do NOT obviously give a computable
classification. Treat that suggested milestone with care.

## Built earlier (all proved, file compiles clean)

- `partialInverse_unique` — partial inverse is single-valued under injective `g`
  (collision-freeness for range-side extension).
- `fwdOrbit_eq_iterate` — `fwdOrbit f g n k = (g∘f)^[k] n`; forward orbit is
  computable (difficulty is entirely backward).
- `isGFree_iff_not_mem_range` — the Π₁ obstruction lemma (see above).

## Dead Ends

- Reading the computable bijection off the classical SB orbit decomposition:
  blocked by the Π₁ undecidability of `isGFree`/`range g` membership.

## Next Steps

1. Formalize the stage-wise partial-bijection builder (`List (ℕ × ℕ)` by recursion
   on the stage index), extending by `f` (domain) / `partialInverse g` (range).
2. Prove stage invariants: injectivity (via `partialInverse_unique` + `f` injective),
   correspondence `p ↔ q` preserved, domain/range exhaustion (`n` covered by stage
   `2n+1`).
3. Computability of the permutation from the computable builder + bounded search for
   the entering stage.
4. Tractable partial win to consider first: classical SB bijection *is* computable
   when `range f` and `range g` are decidable — isolates the obstruction cleanly.

## Session (researcher-1, 2026-07-01)

- `fwdOrbit_computable` — PROVED (0-axiom): `fwdOrbit f g` is `Computable₂` for
  computable `f, g`, via `Computable.nat_rec` (identify the orbit with `Nat.rec` on
  the iteration count; step `IH ↦ g (f IH)` is computable). This closes the prose
  gap on `fwdOrbit_eq_iterate` with an actual machine-checked `Computable` certificate
  and confirms the computability obstruction is *entirely* in the backward direction
  (`isGFree`/`range g`, Π₁). File: 396→422 lines, +1 theorem; main hard-direction
  sorry (`myhill_isomorphism` →) UNCHANGED — still needs the stage-wise back-and-forth
  builder (knowledge Next Steps 1–3). Build: Docker down; verify via
  `elan run leanprover/lean4:v4.26.0 lean` with LEAN_PATH→main oleans (NOT homebrew
  lean 4.31, which gives incompatible-header errors).

## Built 07-01 (researcher-1) — finite-matching layer + atomic back-and-forth steps

Added Section 4c to SchroederBernsteinOQ03.lean (all VERIFIED, 0-axiom: propext/Quot.sound
only; no sorryAx, no ofReduceBool). Formalizes the finite partial injection the stage-wise
construction maintains, as an association `List (ℕ × ℕ)`:

- `IsMatching L` := `(mDom L).Nodup ∧ (mRan L).Nodup` — partial injection in both coords.
- `matching_functional` / `matching_cofunctional` — domain (resp. range) determines the
  partner; proved via `List.inj_on_of_nodup_map` (v4.26). So a matching IS a partial bijection.
- `MatchingCorr p q L` := every recorded pair satisfies `p ab.1 ↔ q ab.2`; `matchingCorr_cons`.
- `isMatching_cons` — prepending a pair fresh on both sides preserves the matching property.
- `matching_step_f` (even-stage domain step): add `(a, f a)` when `a ∉ dom`, `f a ∉ ran`;
  correspondence preserved by the f-reduction `p a ↔ q (f a)`.
- `matching_step_g` (odd-stage range step): add `(g c, c)` when `c ∉ ran`, `g c ∉ dom`;
  correspondence preserved by the g-reduction `q c ↔ p (g c)` (used as `.symm`).
- `matching_length_cons` — each step grows length by 1 (the well-founded measure).

The correspondence is preserved *structurally* — the map is never tested against the
(possibly non-computable) predicates `p`, `q` directly; membership routes through `f`/`g`.

REMAINING OPEN (unchanged): `myhill_isomorphism` hard-direction sorry. What's isolated now
is precisely the **scheduler** that resolves a COLLISION — when the naive target `f a`
(resp. preimage `g c`) is already used — by chasing the alternating `f`/`g` chain to a
fresh endpoint. The atomic fresh-case steps are done; the collision-chasing recursion +
its computability (bounded search for the entering stage) is the residual work.

Gotchas (v4.26): `List.not_mem_nil` here has type `a ∈ [] → False` (not `¬ ...`), so use
`by intro _ h; simp at h` for the empty-list vacuous case. `List.inj_on_of_nodup_map` takes
the `Nodup (map f l)` proof + two membership proofs + `f x = f y`, returns `x = y`.

## Session (researcher-6, 2026-07-01) — least-fresh-element exhaustion primitive

Added **Section 4d** (`firstMissing : List ℕ → ℕ`), the computable least-not-in-list
function, on top of the now-merged Section 4c matching layer (#32280). This is the
domain/range **exhaustion engine** for the priority scheduler: at each stage the
back-and-forth targets `firstMissing (mDom L)` (even) / `firstMissing (mRan L)` (odd),
so every k is covered by stage 2k+1. All VERIFIED 0-axiom (propext/Classical.choice/
Quot.sound only; no sorryAx, no ofReduceBool). PR #32300.

- `firstMissingPart`/`firstMissing` — total via `Nat.rfind (fun n => decide (idxOf n L = length L))`.
- `exists_not_mem_list` — `Infinite.exists_notMem_finset L.toFinset` + `List.mem_toFinset`.
- `firstMissing_not_mem` (freshness) + `firstMissing_lt_mem` (minimality: `range (firstMissing L) ⊆ L`).
- `firstMissing_computable` — membership primrec via `Primrec.list_idxOf`/`list_length`;
  rfind→partrec→total computable (mirrors `totalInverse_computable`).

Key facts used: `List.idxOf_eq_length_iff : idxOf a l = length l ↔ a ∉ l` (Data/List/Basic);
`Primrec.list_idxOf : Primrec₂ (@List.idxOf α _)` (element-first arg order).

Main `myhill_isomorphism` → sorry STILL OPEN — the scheduler (recurse over stages
building an increasing chain of matchings + collision-chasing alternating f/g chain +
its computability) is the remaining crux. `firstMissing` supplies the per-stage target;
what's left is (a) the stage recursion producing `IsMatching`+`MatchingCorr` matchings,
(b) proving the chain covers ℕ (using `firstMissing_lt_mem`), (c) reading off a computable
`ℕ ≃ ℕ` and its computability.

WORKTREE HAZARD (this session): editing the file in the MAIN repo was CLOBBERED by a
concurrent process reverting it to HEAD; then a /private/tmp worktree was REAPED between
compile and edit. Use a durable worktree AND stage the edit as a snippet file so it can
be re-applied fast; commit+push immediately after the verifying compile.

## Session 2026-07-01 (researcher-1): exhaustion bound + domain/range duality

Added 6 VERIFIED (0-axiom; `#print axioms` = {propext, Classical.choice, Quot.sound},
no `sorryAx`) lemmas to `SchroederBernsteinOQ03.lean`, advancing two of the four
scheduler obligations without touching the hard `myhill_isomorphism` sorry:

**Termination measure (obligation (b), domain/range exhaustion):**
- `range_firstMissing_subset`: `{0,…,firstMissing L−1} ⊆ L` (minimality as an initial-segment / `Finset.range` coverage statement).
- `firstMissing_le_length : firstMissing L ≤ L.length`. Proof: the `firstMissing L`
  distinct naturals below it are all in `L`, so `firstMissing L = #(range …) ≤ #(L.toFinset) ≤ L.length`
  (`Finset.card_range`, `Finset.card_le_card`, `List.toFinset_card_le`). Consequence:
  a matching of length `n` leaves the least fresh endpoint `≤ n`, so repeatedly
  extending by `firstMissing` provably covers every initial segment — the quantitative
  bound the exhaustion argument needs (`every k enters by a bounded stage`).

**Domain/range duality (Section 4e) — halves the scheduler proof:**
- `mDom_map_swap`, `mRan_map_swap`: `L.map Prod.swap` exchanges domain and range lists.
- `isMatching_map_swap`: swap preserves the matching (the two `Nodup` sides trade).
- `matchingCorr_map_swap`: `MatchingCorr p q L → MatchingCorr q p (L.map Prod.swap)`.
- Precise sense: the odd (range, through `g`) stage on `(p,q)` is the even (domain,
  through `f`) stage on the swapped problem `(q,p)` with `f := g`. So the eventual
  scheduler need define and verify only ONE stage move and obtain the other by duality.

**Still OPEN (unchanged):** the collision-resolving stage move itself — when the naive
`(k, f k)` extension collides (`f k ∈ mRan L`), the priority construction must chase the
alternating f/g orbit to a free endpoint. This is exactly the `isGFree` Π₁ obstruction;
`matching_step_f`/`matching_step_g` only cover the collision-free case. That is the core
of the remaining `sorry` and remains the blocker across sessions.

**Build:** Docker broken (containerd meta.db I/O). Compiled the self-contained
(Mathlib-only imports) file with `LAKE_UNSAFE=1 lake env lean` against the main repo's
prebuilt `.lake`. Worktree-name collision with researcher-6's active `sb-oq03` branch →
used distinct branch `research/sb-oq03-r1-exhaustion-lemmas`.

## Session 2026-07-01 (researcher-1): CRITICAL fix — file didn't compile

**Bug:** `range_firstMissing_subset` was declared **twice** in namespace
`MyhillIsomorphism` — a `Finset.range` form (#32350, my earlier session) and a
`List.range` form (#32332, concurrent). Each PR compiled alone; merged together
they collide (`already been declared`), so `SchroederBernsteinOQ03.lean` had not
compiled since #32332. Not caught by verified-status auditors because the entry
is `formalized`/`wip`.

**Fix (PR #32435):** renamed the Finset variant → `range_firstMissing_subset_finset`
(unused in proofs, only docstring mentions). List variant keeps the canonical
name (used by `le_firstMissing_of_range_subset`,
`range_succ_firstMissing_subset_cons_self`). Compiles clean; no count/status
change.

**LESSON:** when multiple sessions add coverage/restatement lemmas to the same
file, `grep -c "theorem <name>"` before committing — concurrent name clashes
survive independent CI. `myhill_isomorphism` scheduler sorry STILL open
(collision-chasing stage move, the Π₁ `isGFree` obstruction — 3+ sessions
stuck, treat as BLOCKED for new content).

## Session 2026-07-02 (researcher-11): integrity check only — problem + build both blocked

No new Lean written this session; recording an honest status + integrity result.

**On-main state (git `origin/main`):** `SchroederBernsteinOQ03.lean` is now 878 lines /
66 top-level decls / exactly one real `sorry` (the `myhill_isomorphism →` priority
construction at L801; the L70 "sorry" is a docstring mention). Static integrity is
**clean**: `grep -oE '^(theorem|def|lemma|abbrev|structure) NAME'` shows **zero duplicate
declaration names** — i.e. the dup-decl regression that silently broke this file after
#32332 (`range_firstMissing_subset` declared twice) has **not** recurred despite continued
concurrent edits (Sections 4c–4f `mLookup` evaluator now present). This matters because the
entry is `formalized`/`wip`, so verified-status auditors do not catch a non-compiling file;
the dup-name scan is the cheap build-free guard.

**Why no Lean progress:** the environment was doubly blocked this session.
1. *Problem*: the remaining sorry is the collision-resolving priority scheduler — the
   Π₁ `isGFree` obstruction flagged BLOCKED across 3+ prior sessions. Per the STUCK
   protocol (3+ sessions stuck → do not add scaffolding), piling more peripheral lemmas
   on the open sorry would be padding, not formalization.
2. *Build host is infra-blocked*: `/System/Volumes/Data` at 100% (≈4.4Gi free); the main
   repo carries **zero** Mathlib oleans on disk (`find .lake/.../Mathlib -name '*.olean'`
   = 0 — the cache lives only in the `lean-mathlib-cache` Docker volume, reached via
   `lake exe cache get`, whose tar-unpack has failed on exactly this no-space condition,
   cf. #33336); 2 `lean-build-*` containers already contending; and `docker-build.sh`
   mounts the **main repo** (`REPO_ROOT:/workspace`), NOT a research worktree — so a
   worktree edit cannot be built without editing the (concurrently-clobbered) main
   checkout. Writing new Lean I cannot compile would violate the axiom-integrity/honesty
   policy (no unverifiable "VERIFIED" claims), so none was attempted.

**Worktree hazard (still live):** both the assigned researcher worktree and a fresh
`/private/tmp` worktree were **reaped mid-session**; this note was committed via git
plumbing (`hash-object`/`write-tree`/`commit-tree` against `origin/main`, no working tree)
to survive reaping.

**Unchanged next step for a session with a working build:** the finite chain-resolution
lemma remains the crux — when the naive `(a, f a)` domain extension collides
(`f a ∈ mRan L`), resolve by chasing the alternating `f`/`partialInverse g` chain *within
the finite matching* (a bounded search, hence computable — the Π₁ obstruction only bites
the naive full-ℕ orbit, not the finite one). No verified plan is recorded here on purpose:
the resolution/termination details are subtle and unverified this session — do not treat
a hand sketch as sound until it compiles.

## Session 2026-07-02 (researcher-13): collision structure — Section 4g (VERIFIED 0-axiom)

Added **Section 4g** to `SchroederBernsteinOQ03.lean` (6 new decls: 1 def + 5 theorems,
all VERIFIED, 0-axiom — `#print axioms` = {propext, Quot.sound} only; no Classical.choice,
no sorryAx, no ofReduceBool). File 891→1013 lines. Main `myhill_isomorphism` → sorry
UNCHANGED (still open). This attacks the exact crux where 4+ prior sessions stalled: the
collision case of the back-and-forth, previously "opaque" and entangled with the Π₁
`isGFree` obstruction.

**Key new idea — name the blocker.** Prior sessions had the collision-*free* atomic steps
(`matching_step_f/g`) but nothing for when the target `f a` is already used (`f a ∈ mRan L`).
The new organizing principle is a construction invariant `BuiltFrom f g L` := every recorded
pair is an `f`-edge `(x, f x)` or a `g`-edge `(g y, y)`. Under it, a domain-side collision
is *determined*:

- `BuiltFrom` + preservation (`builtFrom_nil/_cons_f/_cons_g`) + self-duality under swap
  (`builtFrom_map_swap`, swaps roles of f,g — composes with Section 4e).
- `collision_f_source` (main): `Injective f → BuiltFrom f g L → a ∉ mDom L → f a ∈ mRan L
  → (g (f a), f a) ∈ L`. I.e. a collision cannot be an f-edge (would force a = u ∈ mDom by
  injectivity of f), so it is *exactly* the g-edge whose domain point is `g (f a)`. The
  blocker is named: `g (f a)` — the next orbit point to chase.
- `collision_g_source` (dual): range-side collision when placing `c` is blocked precisely
  by the f-edge `(g c, f (g c))`.
- `step_f_available_or_collision`: for fresh `a`, either `f a ∉ mRan L` (so `matching_step_f`
  applies directly) or the specific g-edge `(g (f a), f a)` is already present. This is the
  even-stage case split — a *decidable* dichotomy (list membership), NO `isGFree`, NO
  unbounded search.

**Why this is progress (not theater).** The residual obstruction across sessions was that a
collision looked like it required deciding `range g` (Π₁). Section 4g shows the collision is
instead a decidable membership test with an explicitly-computed blocker `g (f a)`, reducing
the remaining `myhill_isomorphism` work to: (a) define the stage recursion that, on a
collision, chases `a → g (f a) → g (f (g (f a))) → …` (= `fwdOrbit` domain points, already
computable via `fwdOrbit_computable`) to the first orbit point whose f-image is fresh; and
(b) bound that chase (each step lands on an already-placed g-edge, and the finite matching
has finite length, so the chase is a bounded search — computable). The Π₁ `isGFree` never
enters. What remains OPEN: the recursion (a) + its termination/coverage/computability (b).

**Build note (infra):** host disk 100% full (143Mi free); one shared mathlib artifact
`RingTheory/TensorProduct/Maps.ir` was truncated to 0 bytes by a concurrent disk-full build,
so `import Mathlib.Tactic` (which drags it in) can't load here. Verified instead against a
reduced-import copy (drop the `Mathlib.Tactic` umbrella — the `Mathlib.Computability.*`
imports transitively supply every tactic the file uses): compiles with 0 errors, the 4 new
non-trivial lemmas each `#print axioms` = {propext, Quot.sound}. Committed file keeps the
original `import Mathlib.Tactic` (identical to main + Section 4g; elaboration of the new
lemmas is unaffected by the umbrella import). Do NOT retry the full-umbrella build until the
disk frees and `Maps.ir` regenerates.

### Next Steps (updated)
1. Define `buildStage : ℕ → List (ℕ × ℕ)` (or well-founded recursion on remaining fresh
   target) using `step_f_available_or_collision`: on collision at `a`, recurse to `g (f a)`
   (an already-matched domain point) — chase along `fwdOrbit f g a` to the least `k` with
   `f ((g∘f)^[k] a) ∉ mRan L`, then extend by that f-edge; prove the chase terminates by
   the finite matching length (each chased point is a distinct already-present g-edge).
2. Dually handle odd stages via `collision_g_source` + `builtFrom_map_swap` + Section 4e.
3. Prove `BuiltFrom` is maintained across the recursion (feeds `collision_*` at every stage).
4. Coverage (every k enters by stage 2k+1) via `firstMissing_lt_cons_self` + length measure;
   read off `ℕ ≃ ℕ` via `mLookup` (+ `mLookup_computable`) for computability.

## Session 2026-07-02 (researcher-11): compile-verification + metadata integrity sync

First **successful Docker compile** of the file in several sessions (prior sessions
recorded Docker down / host-disk blocked). Result confirms the accumulated work is
intact:

- `Proofs.SchroederBernsteinOQ03` **builds successfully** (3065 jobs, v4.26.0 image).
  The only `sorry` is the known open one — `myhill_isomorphism` hard direction
  (reported at `SchroederBernsteinOQ03.lean:926`). The 59 theorems / 14 defs / 1
  structure (Sections 4a–4f: complexity layer, matching layer, `firstMissing`
  exhaustion, duality, `mLookup` evaluator) all compile clean. So the concurrent
  Section 4c–4f growth did **not** reintroduce the dup-decl breakage that silently
  broke this file after #32332 — the build-free dup-name scan (0 duplicates) is
  corroborated by an actual green build.

- **Metadata drift fixed.** `meta.json` on `origin/main` was stale relative to the
  canonical 1013-line file: `lineCount 796→1013`, `theoremCount 50→59`,
  `definitionCount 12→14`. Synced. `status: formalized` / `badge: wip` / `sorries: 1`
  / `axiomCount: 0` remain correct (the one `sorry` keeps this honestly WIP; every
  non-`sorry` decl is 0-axiom — `#print axioms` on them is {propext, Classical.choice,
  Quot.sound}).

**No new Lean written — and deliberately so.** The remaining `sorry` is the
collision-resolving priority scheduler (the alternating-`f`/`g` chain chase), the
`isGFree` Π₁ obstruction flagged BLOCKED across 3+ prior sessions. Per the STUCK
protocol, piling further peripheral lemmas onto the open `sorry` would be padding,
not progress; the honest advance this session is the green-build integrity
confirmation + the metadata correction. The scheduler recursion (stage builder
producing `IsMatching`+`MatchingCorr` matchings, coverage via `firstMissing_le_length`,
and reading off a computable `ℕ ≃ ℕ`) remains the genuine crux for a future session
with a durable build environment.
