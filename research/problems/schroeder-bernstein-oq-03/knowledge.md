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

## Session 2026-07-02 (researcher-9): correspondence half of the collision step + escape-existence obstruction

Added 2 VERIFIED lemmas (`#print axioms` = `[propext]` only — no `sorryAx`, no
`ofReduceBool`, not even `Classical.choice`; green build via pinned toolchain
`elan run leanprover/lean4:v4.26.0 lake env lean`, Docker Desktop was crashed):

- `fwdOrbit_corr` — **the collision chase preserves the source predicate**:
  `p (fwdOrbit f g a k) ↔ p a` for all `k`, given the reductions `hfpq`/`hgpq`.
  Clean induction: `p (g (f x)) ↔ q (f x) ↔ p x` per step. Holds for *arbitrary*
  (non-computable) `p, q` — routed structurally through `f, g`, never testing `p`/`q`.
- `chase_target_corr` — corollary `p a ↔ q (f (fwdOrbit f g a N))` for every `N`.
  So routing a blocked fresh domain point `a` to the escape target `f (fwdOrbit f g a N)`
  records a pair satisfying `MatchingCorr`. This is the **correspondence obligation** of
  the even-stage collision move; the *bounded-termination* obligation was already covered
  by `fwdOrbit_chase_length_le`. Modest (both are short), but a genuinely-absent
  ingredient rather than a restatement.

**Obstruction found (important for future sessions).** `fwdOrbit_chase_length_le` does
**not** by itself give escape-existence (`∃ N ≤ L.length, f (fwdOrbit f g a N) ∉ mRan L`).
Its hypothesis — *every* chase point `fwdOrbit f g a k` (`1 ≤ k ≤ N`) lies in `mDom L` —
is exactly the gap, and the naive "keep colliding ⟹ stay in mDom L" induction **fails**:
from `f x ∈ mRan L` and `BuiltFrom`, the blocking pair is an `f`-edge OR a `g`-edge
(generalizing `collision_f_source` by dropping the freshness hypothesis):
  - `g`-edge ⟹ `g (f x) = fwdOrbit …(k+1) ∈ mDom L` (chain continues, good);
  - `f`-edge ⟹ only `x ∈ mDom L` (no control on the *next* point `g (f x)`).
So once the orbit re-enters an `f`-edge domain point, the counting bound no longer forces
the successor into `mDom L`, and escape-existence is not free. Establishing escape (hence
that the even-stage collision move is total) likely needs a **stronger construction
invariant** than `BuiltFrom` — e.g. one guaranteeing the matched domain is closed under
the relevant orbit step, or a different chase that stops at the first `f`-edge re-entry.
This is the residual crux, and it is finer than the earlier "`isGFree` Π₁" framing:
the `isGFree` obstruction is avoided (blockers are named), but *termination of the
routing* is the real open point. `myhill_isomorphism` → sorry UNCHANGED.

## Session 2026-07-02 (researcher-14): escape-existence RESOLVED — Section 4i (VERIFIED 0-axiom)

Added **Section 4i** (3 theorems, all VERIFIED — host `lake env lean` v4.26.0, EXIT 0;
`#print axioms` = {propext, Classical.choice, Quot.sound} for `escape_exists`/`domain_step_exists`,
{propext, Quot.sound} for `chase_gedge_chain` — no `sorryAx`, no `ofReduceBool`). File
1299→1435 lines. Main `myhill_isomorphism` → sorry UNCHANGED. This closes the exact
"escape existence is not free" obstruction that researcher-9 documented as the residual crux.

**The obstruction (r9's finding).** The even-stage domain step routes a fresh anchor `a` to
the escaped target `f (fwdOrbit f g a N)` for the least `N` with that target range-fresh. r9
showed `fwdOrbit_chase_length_le` does NOT by itself give such an `N`: its hypothesis "every
chase point stays in `mDom L`" fails pointwise — when the orbit re-enters an `f`-edge domain
point, the counting bound loses control of the successor.

**The resolution.** Do the induction on the *stage bound* `t`, not pointwise. Then the IH gives
*all* earlier g-edges at once. Concretely `chase_gedge_chain`: if every green candidate before
stage `N` is used (`f (fwdOrbit f g a j) ∈ mRan L`, `j < N`), then for every `1 ≤ m ≤ N` the
matching contains the **g-edge** `(fwdOrbit f g a m, f (fwdOrbit f g a (m-1)))`. The `f`-edge
alternative is killed by **matching functionality**: an f-edge `(o_m, f o_m)` would share the
domain point `o_m` with the previous stage's g-edge `(o_m, f o_{m-1})`, forcing (functionality
+ f injective) `o_m = o_{m-1}` — an orbit repeat — which via `fwdOrbit_prefix_distinct` (fed the
`[1..m]` mDom-membership from the same IH) forces `a ∈ mDom L`, contradicting freshness. Hence
every chase point lies in `mDom L`, `fwdOrbit_chase_length_le` bounds the chase by `L.length`,
and a chase surviving `L.length + 1` collisions is impossible — `escape_exists`:
`∃ N ≤ (mDom L).length, f (fwdOrbit f g a N) ∉ mRan L`. `domain_step_exists` then makes the
even-stage step **total** (preserving `IsMatching` + `MatchingCorr`).

**The finer residual crux (newly named).** The resolution edge `(a, f (o_N))` is in general
**neither an f-edge nor a g-edge** (when `N > 0`), so `matching_step_chase` does NOT preserve
`BuiltFrom` — the very invariant `collision_f_source`/`escape_exists` need to re-run at the next
stage. So `domain_step_exists` is a *one-step* result; iterating the scheduler needs the
**augmenting-path rewrite**: replace the chased g-edges `(o_k, f o_{k-1})` (1≤k≤N, from
`chase_gedge_chain`) by the f-edges `(o_k, f o_k)` (0≤k≤N, o_0=a), shifting the chain by one and
consuming the fresh target `f(o_N)`. That produces an all-f-edge matching (BuiltFrom preserved),
covers `a`, and preserves `IsMatching` (f(o_N) fresh by `escape_exists`) and `MatchingCorr` (via
`fwdOrbit_corr`). This list surgery + its three preservation proofs (~150 lines) is the genuine
remaining work; the termination heart of it is `escape_exists`, now done.

**Build note.** Host disk 100% full; `import Mathlib.Tactic` segfaults locally (corrupted olean
in its closure from the disk-full condition, exit 139 reproducibly). Verified against a targeted
import (`Mathlib.Order.Interval.Finset.Nat` supplies the `Finset.Icc` API the file's
`fwdOrbit_chase_length_le` needs; the `Mathlib.Computability.*` imports supply everything else) —
the committed file keeps `import Mathlib.Tactic` (superset; Docker has it intact), so the new
lemmas (verified under the smaller set) elaborate identically there. Do NOT retry the full-umbrella
host build until the disk frees.

## Session 2026-07-02 (researcher-4): augmenting-path object built + VERIFIED

Added **Section 4j** to `SchroederBernsteinOQ03.lean` (8 decls, all VERIFIED —
`#print axioms` = {propext, Classical.choice, Quot.sound}; no `sorryAx`, no
`ofReduceBool`). This constructs the **augmenting path**, the object the
`BuiltFrom`-preserving domain step re-labels into — explicitly named as "the
remaining piece" by the `domain_step_exists` docstring but never before built.

- `augPath f g a N := (range (N+1)).map (fun k => (fwdOrbit f g a k, f (fwdOrbit f g a k)))`
  — the `f`-edges `(oₖ, f oₖ)` for `k = 0..N`.
- `mem_augPath_iff`, `mDom_augPath` (= orbit prefix), `mRan_augPath` (= its `f`-image).
- `augPath_builtFrom` — every pair is an `f`-edge ⇒ `BuiltFrom` preserved. THIS is the
  point: `domain_step_exists` places `(a, f(oₙ))`, neither f- nor g-edge for `N>0`, so it
  breaks `BuiltFrom` and the next stage's `collision_f_source`/`escape_exists` can't fire.
  Re-labelling the whole chased chain into f-edges restores the invariant.
- `augPath_matchingCorr` — each `f`-edge corresponds via `hfpq` directly (no anchor, no `isGFree`).
- `augPath_isMatching` — valid matching given orbit-prefix distinctness `hdist`.
- `augPath_isMatching_of_chase` — `hdist` is automatic in the collision context
  (`a ∉ mDom L`, `oₖ ∈ mDom L` for `1≤k≤N`) via `fwdOrbit_prefix_distinct`; this is the
  form the scheduler invokes.

**Main `myhill_isomorphism` → sorry UNCHANGED (still open).** What remains is the
*splice*: `keptL := L` minus the `N` re-labelled `g`-edges `(oₖ, f o_{k-1})` (filter
domain ∉ `{o_1..o_N}`), then `IsMatching (augPath ++ keptL)` via `List.Nodup.append`.
Ingredients located:
1. **Minimal escape depth** via `Nat.find` (pred decidable — `mRan L` membership), so
   `∀ k<N, f oₖ ∈ mRan L` (collision) ⇒ by `collision_f_source` the g-edge `(o_{k+1}, f oₖ) ∈ L`.
2. **Domain disjointness**: `mDom augPath = {a} ∪ {o_1..o_N}`; `a ∉ mDom L` (fresh) and
   `o_1..o_N` are exactly the removed g-edge domains ⇒ disjoint from `mDom keptL`.
3. **Range disjointness**: `mRan augPath = {f o_0..f o_N}`; `f o_0..f o_{N-1}` are the
   removed g-edge ranges (unique per range value by `matching_cofunctional`), and `f o_N`
   is the escape point `∉ mRan L` (`escape_exists`) ⇒ disjoint from `mRan keptL`.
Then the stage recursion (increasing chain of `BuiltFrom` matchings) + coverage via
`firstMissing` + reading off the computable `ℕ ≃ ℕ`.

**Infra notes.** Build loop that works this session: the `.loom/worktrees/researcher-4`
worktree was REAPED mid-session (again — the recurring hazard). Durable worktree at
`/Users/rwalters/lg-r4-sb` (outside `.loom/worktrees` and `/private/tmp`, both of which
get reaped) survived. `proofs/.lake` on the MAIN repo now carries Mathlib oleans on disk,
so compile a worktree file with
`cd <REPO_ROOT>/proofs && LAKE_UNSAFE=1 lake env lean /Users/rwalters/lg-r4-sb/proofs/Proofs/SchroederBernsteinOQ03.lean`
(~30s warm). GOTCHA: `lake env lean Proofs/...` from `REPO_ROOT/proofs` compiles the
MAIN-repo file, NOT the worktree — pass the absolute worktree path. `List.nodup_range`
takes `n` IMPLICIT (`List.nodup_range.map_on`, not `(List.nodup_range (N+1))`).

## Session 2026-07-02 (researcher-9): augmenting-path splice — the BuiltFrom-preserving domain step is now TOTAL and iterable [VERIFIED, 0-axiom]

Added **Section 4k** `augment_domain_step` (1 theorem, ~180 lines; host `lake env lean`
v4.26.0, EXIT 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no `ofReduceBool`). File 1539→1718 lines. This closes the exact "list-surgery splice" that r4
named as the genuine remaining work: it turns the augmenting-path *object* (Section 4j) into an
actual **invariant-preserving, iterable even-stage move**.

**Statement.** For a fresh anchor `a ∉ mDom L` in a matching `L` with `IsMatching`,
`MatchingCorr p q`, `BuiltFrom f g`, there is `L'` with all three invariants preserved, `a ∈
mDom L'`, and *monotone* on both sides: `∀ x ∈ mDom L, x ∈ mDom L'` and `∀ y ∈ mRan L, y ∈ mRan
L'`. (Only the `f`-reduction `hfpq` is needed — `hgpq` dropped; the augmenting edges are all
`f`-edges.)

**Construction.** `L' := augPath f g a N ++ keptL` where `N` is the *minimal* escape depth
(`Nat.find` on `f (fwdOrbit f g a N) ∉ mRan L`, so `∀ j<N, f oⱼ ∈ mRan L`) and
`keptL := L.filter (·.1 ∉ mDom (augPath f g a N))` drops exactly the pairs whose domain point
lies on the re-labelled orbit prefix.

**The four invariant proofs (all discharged):**
- `BuiltFrom` / `MatchingCorr`: `augPath` supplies them (all `f`-edges; `augPath_builtFrom`,
  `augPath_matchingCorr`), `keptL ⊆ L` inherits (`hmemKept.1` into `hB`/`hC`).
- `IsMatching` **domain Nodup**: `mDom augPath` distinct (`augPath_isMatching_of_chase` via
  `chase_gedge_chain`→`hchase`), `mDom keptL` a `Sublist`-inherited Nodup, and disjoint *by the
  filter itself* — a kept pair has `.1 ∉ mDom augPath`.
- `IsMatching` **range Nodup**: `mRan augPath = {f o_0..f o_N}` distinct; disjoint from `mRan
  keptL` by cases on the aug index `k`: for `k<N`, `f oₖ` is the range value of the removed
  `g`-edge `(o_{k+1}, f oₖ)` (from `hgedges`), so any kept pair sharing it would, by
  `matching_cofunctional`, have domain `o_{k+1} ∈ mDom augPath` — contradicting the filter; for
  `k=N`, `f o_N ∉ mRan L` (`escape_exists`).
- **monotonicity**: every removed `g`-edge endpoint is re-added by `augPath` — domains
  `o_1..o_N ⊆ {o_0..o_N}`, ranges `f o_0..f o_{N-1} ⊆ {f o_0..f o_N}`; and functionality pins a
  kept pair with domain `oₖ (k≥1)` to range `f o_{k-1} ∈ mRan augPath` (`k=0` ⇒ `a ∈ mDom L`,
  impossible).

**Significance (honest).** This is the crux structural step, not the whole theorem. `main
myhill_isomorphism → sorry UNCHANGED`. What remains is genuinely the *outer* recursion: iterate
`augment_domain_step` and its `Prod.swap` dual (odd/range stage, Section 4e) over stages
`0,1,2,…`, using `firstMissing` to pick the anchor at each stage, take the union/limit matching,
and read off the computable `ℕ ≃ ℕ` via `mLookup` (proving totality on both sides from
monotonicity + coverage, injectivity from `mLookup_injOn`/`mLookup_stable`, and computability of
the stage function). Every atomic ingredient the recursion consumes now exists and is verified;
the assembly (well-founded stage function + its computability + the bijection read-off) is the
remaining work.

**GOTCHAS (v4.26.0 / this file):**
- The `<+` Sublist notation did NOT parse here (tokenised as `<` then `+`); use explicit
  `List.Sublist a b`. Sublist→Nodup transfer is `hNodup.sublist hSub` (`List.Nodup.sublist`).
- `List.nodup_append` yields the **pairwise** third component `∀ a∈l₁, ∀ b∈l₂, a ≠ b`, NOT
  `List.Disjoint` — `rw [List.disjoint_left]` fails; `intro a ha b hb hne` directly.
- `List.filter_sublist` takes p,l **implicit** (`exact List.filter_sublist`, not `… L`).
- `fwdOrbit f g a 0 = a` is NOT closed by `rw`'s trailing rfl (fwdOrbit is a plain def, not
  reducible); use `exact`-at-defeq (`rw [hk0] at hk; exact hk`) or an explicit `rfl` tactic.
- Destructure list pairs to `⟨u,w⟩` and capture clean equalities (`have hwy : w = y := hab2`)
  so later `rw` sees `w`, not the stuck projection `(u,w).2`.

## Session 2026-07-03 (researcher-14): edge preservation (pairs) — Section 4k f-edge / 4l g-edge [VERIFIED 0-axiom]

Strengthened both stage moves to expose **pair-level edge preservation**, the ingredient the
limit read-off actually needs (see the sharpened obstruction below). Host `lake env lean`
v4.26.0, EXIT 0; `#print axioms augment_domain_step` = `#print axioms augment_range_step` =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `ofReduceBool`. File 1773→1811
lines, 75→84 theoremCount (meta leanFile synced). Main `myhill_isomorphism` → sorry UNCHANGED.

- `augment_domain_step` (Section 4k): added conjunct `(∀ ab ∈ L, ab.2 = f ab.1 → ab ∈ L')`.
  I.e. the even-stage splice **preserves every existing `f`-edge as an actual pair**, not just
  its domain/range membership. Proof: `keptL` drops only pairs whose domain lies on the orbit
  prefix `mDom (augPath) = {o₀,…,o_N}`; an `f`-edge `(x, f x)` with `x = oₖ` forces (via the
  stale `g`-edge `(oₖ, f o_{k-1}) ∈ L` + `matching_functional`) `f oₖ = f o_{k-1}`, hence
  (`f` inj) `oₖ = o_{k-1}`, contradicting `fwdOrbit_prefix_distinct`; `k=0` gives `x = a ∈ mDom L`
  against freshness. So `x ∉ mDom (augPath)`, thus `(x, f x) ∈ keptL ⊆ L'`.
- `augment_range_step` (Section 4l): dual conjunct `(∀ ab ∈ L, ab.1 = g ab.2 → ab ∈ L')` — the
  odd-stage move **preserves every existing `g`-edge**. Free from the `Prod.swap` duality: a
  `g`-edge `(u,w)` (`u = g w`) is a swapped-world `f`-edge `(w,u)`, preserved by
  `augment_domain_step` in the swapped problem, then swapped back (`List.mem_map.mpr ⟨·,·,rfl⟩`).

**SHARPENED OBSTRUCTION (correcting prior "Next Steps").** Prior sessions' plan — "read off the
limit `σ n` via `mLookup` at any stage past the one where `n` enters `mDom`" — tacitly assumes
`mLookup` is *stable* along the chain. But `mLookup_stable` (Section 4f-bis) requires
`∀ x ∈ L₁, x ∈ L₂` (**every pair preserved**), and the rerouting augment step *violates this*: a
domain step **removes** the stale `g`-edges `(oₖ, f o_{k-1})` and re-adds `f`-edges `(oₖ, f oₖ)`,
so the partner of a domain point genuinely *changes* between stages. Hence the read-off value is
**not** monotone/eventually-constant for free. The real remaining crux is a **finite-injury
stabilization** argument (recursion-theoretic): each point is rerouted only finitely often
(a domain point survives as an `f`-edge across all *domain* steps — this session's
`augment_domain_step` f-edge conjunct — but can be flipped to a `g`-edge by a *range* step, and
vice versa), so `mLookup (stage s) n` stabilizes as `s → ∞`. Bounding the number of flips per
point (priority/injury count) is the genuine open work; `mLookup_stable` as stated is *too weak*
to close the limit and should not be cited as if the read-off were mechanical.

### Next Steps (revised — supersedes the earlier "read off via mLookup" step)
1. **Do NOT** assume monotone pair-preservation across a full stage. State and prove a
   *stabilization* lemma: for each `n`, `∃ S, ∀ s ≥ S, mLookup (stage s) n = mLookup (stage S) n`.
   The edge-preservation conjuncts added this session are the base: an `f`-edge at `n` is immune
   to all future *domain* steps; only *range* steps can disturb it (and dually). Bound the
   disturbances (finite injury) to get stabilization.
2. Alternatively, investigate an **extension-only reformulation** of the scheduler (pairs never
   removed) so `mLookup_stable` applies directly — this trades the rerouting splice for a
   cleverer anchor choice (classical Rogers §7.4 back-and-forth extends without revising). If
   feasible this sidesteps finite injury entirely and is likely the shorter path to closing.
3. Only after stabilization: coverage (`firstMissing_le_length`) + read off `ℕ ≃ ℕ` +
   computability of the (now explicit) stage function.

## Session 2026-07-03 (researcher-14): the termination↔stability trade-off is the crux — extension-only stalls on `escape_exists`'s `BuiltFrom` hypothesis, NOT anchor choice [ANALYSIS; build unavailable]

No verified Lean this session: host disk 3.9 GiB free, `lean-mathlib-cache` volume cold
(0 Mathlib oleans), a build container already running — a fresh `lake exe cache get` would
saturate disk (the recurring blocker). Contribution is a sharpening of the frontier that
supersedes the vague "Option B = cleverer anchor choice" line in the prior session's Next Steps.

**The two per-stage moves already in the file are the two horns of the dilemma:**

- `domain_step_exists` (Section 4i) returns `∃ b, IsMatching ((a,b)::L) ∧ MatchingCorr p q ((a,b)::L)`
  — a **cons** (extension-only, nothing removed). Along a chain of conses `mLookup_stable` applies
  *directly* (`L₁ ⊆ (a,b)::L₁`), so the read-off value of every placed point is **immutable** →
  the limit `e n` is eventually constant *for free*, no finite injury. This IS the "extension-only
  reformulation" (Rogers §7.4 back-and-forth) the prior session hoped for — it already exists.
- `augment_domain_step` (Section 4k) returns `augPath f g a N ++ keptL` with
  `keptL = L.filter (·.1 ∉ mDom (augPath …))` — it **removes** the stale g-edges `(oₖ, f o_{k-1})`.
  This is what breaks `mLookup_stable` (a placed domain point `oₖ` is re-partnered), forcing the
  finite-injury stabilization argument.

**Why can't we just use the cons move (`domain_step_exists`) everywhere and keep the free read-off?**
Because the chase **termination certificate `escape_exists` requires `hB : BuiltFrom f g L` on its
input**, and *both* step lemmas consume it (`domain_step_exists` calls `escape_exists` to get `N`).
A cons of the chase anchor `(a, chaseTarget f g a N)` with `N > 0` is neither an f-edge `(x, f x)`
nor a g-edge `(g y, y)`, so the resulting `(a,b)::L` is **not** `BuiltFrom` → `escape_exists` **cannot
be invoked on it** → the *next* domain stage has no bound on its chase. So the extension-only path
does not stall on *anchor choice* (as the prior Next Steps implied); it stalls because **the cons
destroys the `BuiltFrom` hypothesis that `escape_exists` needs to terminate the following chase.**
`augment_domain_step`'s rerouting exists precisely to *restore* `BuiltFrom` so the chase is
re-runnable — trading stability for termination. That is the whole trade-off:

  cons (`domain_step_exists`)      : stable read-off ✓, breaks `BuiltFrom` ✗ (next chase unbounded)
  reroute (`augment_domain_step`)  : `BuiltFrom` ✓ (chase re-runnable), breaks stability ✗ (finite injury)

**The decisive open question, now sharp:** *Can `escape_exists` be reproved from an invariant that a
`(a,b)::L` cons preserves?* If yes → an extension-only scheduler closes the theorem with a monotone
read-off and no finite injury (much shorter). If provably no → finite injury is mathematically
necessary and Path A is the only route.

**BuiltFrom-free skeleton of `escape_exists` (the reduction to attempt).** Termination is really a
pigeonhole fact: if `f (fwdOrbit f g a k) ∈ mRan L` for all `k ≤ (mRan L).length`, then two of the
`(mRan L).length + 1` values `f(orbit_k)` collide, so (f inj) `orbit_i = orbit_j` (i<j), so (g∘f inj)
**a is periodic under g∘f**. Thus the chase escapes within `|mRan L|+1` steps *unless* a lies on a
finite g∘f-cycle all of whose f-images are already occupied ("trapped cycle"). Currently `BuiltFrom`
excludes the trapped cycle structurally: `chase_gedge_chain` forces each `orbit_k` (k≥1) into `mDom L`
as the g-edge `(orbit_k, f o_{k-1})`, then `fwdOrbit_chase_length_le` bounds the run by `|mDom L|`.
So the minimal cons-preserved invariant needed is: **"every occupied range point `f(orbit_k)` on the
forward orbit of a fresh anchor sits on a g-edge, so its domain partner is the next orbit point"** —
weaker than full `BuiltFrom` (which asserts this for *all* pairs), but strong enough for the
pigeonhole/no-trapped-cycle argument. Whether such an invariant survives a `(a, chaseTarget)` cons
(the anchor pair is not a g-edge, but it need not lie on any *later* fresh anchor's orbit) is the
concrete next lemma to test — it is the difference between a short extension-only proof and a long
finite-injury one.

**Recommended next action (revises prior Next Steps items 1–2):** Before investing in the full
finite-injury machinery (Path A), spend one focused session testing the reduction above:
state a predicate `OrbitGEdged f g L` ("for every fresh `a` and every `k` with `f(orbit_k) ∈ mRan L`,
the pair witnessing it is the g-edge `(orbit_{k+1}, f(orbit_k))`") and check (a) it implies
`escape_exists`'s conclusion by the pigeonhole above (BuiltFrom-free), and (b) it is preserved by a
`domain_step_exists` cons of `(a, chaseTarget f g a N)`. If (b) fails with a concrete counterexample,
that is the proof that finite injury is unavoidable — record it and commit to Path A. Either outcome
resolves the strategic fork that has been open across the last several sessions.

## Session 2026-07-03 (researcher-4): FORK RESOLVED — the extension-only (cons) scheduler IS viable; `escape_exists` follows from a cons-preserved **cycle-balance** invariant, no finite injury [ANALYSIS; build env hostile — verification deferred]

No verified Lean this session (worktrees deleted within seconds in both `.loom/worktrees`
and `/tmp`; host default toolchain elan `v4.31.0` ≠ project `v4.26.0`; a foreign
`lean-build-*` container was already running against a 2.5 GiB-free disk). Contribution is a
**decision** on the strategic fork that r14 left explicitly open ("the decisive open question,
now sharp: can `escape_exists` be reproved from an invariant that a `(a,b)::L` cons
preserves?"). The answer is **yes**, and the cons-preserved invariant is *not* r14's
`OrbitGEdged` (which fails preservation — see below) but a global **cycle-count balance**.

### The clean dynamical picture (why the trap cannot form)

`g∘f : ℕ→ℕ` is injective (f, g inj). An injective self-map of ℕ has **no ρ-shaped orbits**:
if a tail `a, g f a, …, (gf)^{k}a = c` entered a cycle `C` at `c` (minimal `k≥1`, `a∉C`),
then `c` would have two distinct `gf`-preimages — the tail point `(gf)^{k-1}a ∉ C` and the
cycle predecessor of `c` in `C` — contradicting injectivity. Hence **every forward orbit is
either (i) all-distinct (infinite) or (ii) a pure cycle containing its anchor** (a repeat
`orbit_i = orbit_j`, `i<j`, forces `a = orbit_{j-i}` by injectivity of `(gf)^i`, so `a` is on
the cycle — no tail).

### The cons-preserved invariant

For a finite `g∘f`-cycle `C` (so `f↾C` is injective onto `f(C)`, `|f(C)| = |C|`), define

    Balanced L  :≡  ∀ cycle C,  (C ∩ mDom L).card  =  (f(C) ∩ mRan L).card.

**Claim A (Balanced ⟹ escape, BuiltFrom-free).** Let `a ∉ mDom L` be a fresh domain anchor.
- If `a`'s forward orbit is **infinite**: the values `f(orbit_k)` are pairwise distinct
  (f inj + orbit distinct), so among any `|mRan L|+1` of them one lies outside the finite set
  `mRan L` — the chase escapes in `≤ |mRan L|+1` steps. *(This case never touches `Balanced`.)*
- If `a` lies on a **cycle** `C` (`|C| = m`): since `a ∉ mDom L`, `(C ∩ mDom L).card ≤ m-1`,
  so by `Balanced`, `(f(C) ∩ mRan L).card ≤ m-1 < m = |f(C)|`. Hence some `f(orbit_k) ∈ f(C)`
  is **not** in `mRan L` — the chase escapes. ∎

This *replaces* the `BuiltFrom` hypothesis of `escape_exists` with `Balanced`. It is exactly
the "no trapped cycle" content that `BuiltFrom` supplied via `chase_gedge_chain` +
`fwdOrbit_chase_length_le`, but stated as a **counting** fact rather than an edge-labelling
fact — and counting is what survives a cons.

**Claim B (Balanced is preserved by BOTH cons steps).** Fix a cycle `C`, `|C| = m`.
- **Domain step** `domain_step_exists`: conses `(a, chaseTarget f g a N) = (a, f(orbit^a_N))`.
  - If `a ∈ C`: `orbit^a_N ∈ C` (cycle is `gf`-closed), and the escape target `f(orbit^a_N)`
    is **fresh** (`∉ mRan L`, from escape) while `a` is **fresh** (`∉ mDom L`). So both
    `(C ∩ mDom)` and `(f(C) ∩ mRan)` gain exactly one new element ⟹ balance preserved.
  - If `a ∉ C`: `a`'s orbit is a *different* component, so `orbit^a_N ∉ C` ⟹ (f inj)
    `f(orbit^a_N) ∉ f(C)`, and `a ∉ C`. Neither side of `C`'s balance changes. *(Uses
    `f(orbit^a_N) ∈ f(C) ⟹ orbit^a_N ∈ C ⟹ a ∈ C`, valid because cycles are gf-invariant
    both ways under injectivity — no tails.)*
- **Range step** (dual, `augment_range_step`'s cons analogue): conses `(g c, c)` for a fresh
  range target `c`. If `c = f(o_j) ∈ f(C)`: adds `c` to `mRan` (`f(C)`-side +1) and
  `g c = g(f o_j) = o_{j+1} ∈ C` to `mDom` (`C`-side +1) ⟹ balance preserved. If `c ∉ f(C)`:
  `g c ∈ C ⟺ c ∈ f(C)` (g inj), so neither side changes. ∎

**Corollary (fork resolved).** A scheduler that uses *only* conses — even domain step
(`domain_step_exists`, already in the file, returns a cons `(a,b)::L`) and odd range step (its
dual) — maintains `Balanced` from `Balanced []` (vacuous), so every stage's `escape_exists`
obligation is discharged **without `BuiltFrom`**. Because nothing is ever removed,
`mLookup_stable` (Section 4f-bis, needs `L₁ ⊆ L₂`) applies **directly** along the whole chain:
each placed point's partner is immutable ⟹ the limit `e n = mLookup (stage s) n` is eventually
constant *for free*. **No finite-injury / stabilization argument is needed.** This is the
"short path" (Path B / Rogers §7.4 extend-only back-and-forth) the last several sessions hoped
for; the obstruction the r14 analysis identified (cons destroys `BuiltFrom` needed by
`escape_exists`) dissolves because `escape_exists` never needed `BuiltFrom` — only the weaker,
cons-stable `Balanced`.

### Why r14's `OrbitGEdged` failed preservation but `Balanced` does not

`OrbitGEdged` demanded that *the pair witnessing* each occupied `f(orbit_k)` be the **g-edge**
`(orbit_{k+1}, f(orbit_k))`. A cons of the anchor pair `(a, f(orbit^a_N))` adds a range point
`f(orbit^a_N)` whose witnessing pair is `(a, f(orbit^a_N))` — an **f-edge-like anchor pair,
not a g-edge** — so if a later fresh anchor's orbit reaches `orbit^a_N`, `OrbitGEdged` is
violated at `L'`. `Balanced` sidesteps this entirely: it never asks *which* pair occupies a
range point, only *how many* cycle points/images are occupied. The anchor pair `(a, ·)` still
contributes `+1` to both sides (a enters `mDom`, `f(orbit^a_N)` enters `f(C)∩mRan`), so the
*count* stays balanced even though no g-edge is present. **Balance is the right abstraction;
edge-identity is too rigid.**

### Lean-ready decomposition (for the next build-capable session)

A ready-to-paste scaffold is saved at
`research/problems/schroeder-bernstein-oq-03/cycle_balance_scaffold.lean`. Target lemmas:

1. `def OnCycle (f g : ℕ→ℕ) (a : ℕ) : Prop := ∃ m, 1 ≤ m ∧ fwdOrbit f g a m = a`  (a is gf-periodic).
2. `theorem escape_of_infinite_orbit` — pigeonhole; the `¬OnCycle` case; no invariant. *(Easiest;
   reuses `fwdOrbit_prefix_distinct`-style injectivity + `List.length` pigeonhole. Do this first.)*
3. `def Balanced` via a `Finset` of a cycle, OR — to dodge cycle-set machinery — the **local
   surrogate** `BalancedLocal L :≡ ∀ y ∈ mRan L, (∃ x ∈ mDom L, y = f x) ∨ y is an f-edge target`
   … (the cleanest Lean encoding is still open; the counting proof above is the spec).
4. `theorem escape_of_balanced` — Claim A, cycle case, from `Balanced` + `a ∉ mDom L`.
5. `theorem balanced_cons_domain` / `balanced_cons_range` — Claim B.
6. Re-derive `escape_exists` as `escape_of_infinite_orbit`/`escape_of_balanced` dichotomy; drop
   `BuiltFrom` from the scheduler; assemble the extension-only stage function; read off via
   `mLookup` + `mLookup_stable`; prove `.Computable`; discharge the `myhill_isomorphism` sorry.

**Honest status:** this is a *paper* resolution of the strategic fork, not machine-checked. The
counting argument is elementary and I am confident in it, but the Lean encoding of "cycle" and
its cardinality (step 3) is the one place that could bite — a `Finset`-of-orbit-with-`Nat.find`-
period is likely needed, or a reformulation avoiding explicit cycles. The `myhill_isomorphism`
sorry is UNCHANGED this session (0→0 sorries closed); the deliverable is the decision + scaffold.

### Next Steps (supersede all prior)
1. Formalize `escape_of_infinite_orbit` first (self-contained pigeonhole, no `Balanced`).
2. Choose the Lean encoding of `Balanced`; prove `balanced_cons_domain/range` (Claim B).
3. Prove `escape_of_balanced` (Claim A, cycle case); merge into a `BuiltFrom`-free `escape_exists'`.
4. Build the extension-only scheduler on `domain_step_exists` + dual; read off with
   `mLookup_stable`; close the theorem. **Do NOT re-open the fork — it is decided (Path B).**

## Session 2026-07-03 (researcher-16) — scaffold step 1 DONE: `escape_of_infinite_orbit` VERIFIED

Discharged the FIRST scaffold item (the easy, `Balanced`-free, `BuiltFrom`-free half of the
extension-only scheduler's escape obligation). Added to `SchroederBernsteinOQ03.lean` a new
**Section 4i-bis** (before `escape_exists`), all machine-checked against v4.26.0:

- `def OnCycle f g a := ∃ m, 1 ≤ m ∧ fwdOrbit f g a m = a` — anchor is `g∘f`-periodic. Under
  injective `g∘f` this is the exact complement of an infinite (injective) forward orbit (no
  ρ-tails).
- `fwdOrbit_injective_of_not_onCycle` — **VERIFIED 0-axiom** (`#print axioms` = {propext,
  Quot.sound}; no sorryAx/ofReduceBool). `¬OnCycle f g a → Injective (fwdOrbit f g a)`. Proof:
  a repeat `fwdOrbit a i = fwdOrbit a j` (`i<j`) cancels the shared injective prefix
  `(g∘f)^[i]` (via `Function.Injective.iterate` on `hT := fun x y h => hf (hg h)`) to give
  `a = (g∘f)^[j-i] a = fwdOrbit a (j-i)`, `1 ≤ j-i` — i.e. exactly `OnCycle`, contradiction.
  Mirrors the local `fwdOrbit_prefix_distinct` but is GLOBAL (all of ℕ, no chase predicate `D`).
- `escape_of_infinite_orbit` — **VERIFIED 0-axiom** (`#print axioms` = {propext, Classical.choice,
  Quot.sound}). `¬OnCycle f g a → ∃ N ≤ (mRan L).length, f (fwdOrbit f g a N) ∉ mRan L`. Proof:
  `by_contra`+`push_neg` ⟹ all `(mRan L).length+1` stages `f(fwdOrbit a N)` land in `mRan L`;
  `hf.comp horb` makes `f ∘ fwdOrbit f g a` injective, so `Finset.card_le_card_of_injOn` embeds
  `Finset.range ((mRan L).length+1)` into `(mRan L).toFinset` (card `≤ (mRan L).length` via
  `List.toFinset_card_le`) ⟹ `len+1 ≤ len`, `omega`. Same pigeonhole shape as the existing
  `fwdOrbit_chase_length_le`.

Signatures match the scaffold `cycle_balance_scaffold.lean` exactly (drop-in). File 1811→1892
lines, +2 theorems +1 def, ZERO new sorries/warnings; the only sorry remains `myhill_isomorphism`
(line 1805, shifted +81). Baseline compiled clean before the edit to confirm the environment.

**Build note (works, contra prior "hostile env" sessions):** self-contained (Mathlib-only imports).
Compile the worktree copy with the MAIN repo's prebuilt oleans:
`LEAN_PATH=<main>/proofs/.lake/build/lib/lean:<each pkg>/.lake/build/lib/lean \
   elan run leanprover/lean4:v4.26.0 lean proofs/Proofs/SchroederBernsteinOQ03.lean`
(mathlib oleans live under `proofs/.lake/packages/mathlib/.lake/build/lib/lean/`). NO Docker,
NO `lake build`. This is a reliable verify path for this self-contained file.

**Remaining (scaffold steps 2–6, UNCHANGED):** the periodic half `escape_of_balanced` needs the
`Balanced` encoding (still the open modelling choice — `Finset`-of-cycle via `Nat.find` period, or
a cycle-free surrogate); then `balanced_cons_domain/range` (Claim B), `escape_exists'` by the
`OnCycle` dichotomy (my `escape_of_infinite_orbit` is the `¬OnCycle` arm, ready to plug in),
scheduler assembly on `domain_step_exists`, read-off via `mLookup_stable`, `.Computable`, close
the `myhill_isomorphism` sorry. Do NOT re-open the fork — Path B decided.

### Addendum (same session, researcher-16) — cycle-period infrastructure for the OnCycle arm

Also added (same PR, all VERIFIED; `orbitPeriod_pos`/`fwdOrbit_orbitPeriod`/`orbitPeriod_min`
depend on NO axioms; `fwdOrbit_injOn_range_period`/`orbitCycle_card` on {propext, Classical.choice,
Quot.sound}):

- `def orbitPeriod f g (h : OnCycle f g a) : ℕ := Nat.find h` — least positive period; COMPUTABLE
  (OnCycle's predicate `1 ≤ m ∧ fwdOrbit a m = a` is DecidablePred: `≤` + Nat `DecidableEq`).
- `orbitPeriod_pos` (`1 ≤ period`), `fwdOrbit_orbitPeriod` (`fwdOrbit a period = a`),
  `orbitPeriod_min` (`1 ≤ m < period → fwdOrbit a m ≠ a`) — the `Nat.find` spec/min repackaged.
- `fwdOrbit_injOn_range_period` — the first `period` orbit points are pairwise distinct (same
  prefix-cancel argument as `fwdOrbit_injective_of_not_onCycle`, but bounded, using minimality
  instead of `¬OnCycle`).
- `orbitCycle_card` — `((range period).image (fwdOrbit f g a)).card = period`. This IS the cycle
  cardinal the `Balanced` counting compares against `mDom`/`mRan` occupancy.

So scaffold step 3's `Balanced` encoding now has a verified period/cardinality substrate:
whichever "cycle" encoding is chosen, `(Finset.range (orbitPeriod …)).image (fwdOrbit f g a)` is a
ready-made finite cycle with known card. **This is the recommended encoding for `Balanced`** —
avoids inventing new cycle-set machinery. Next: state `Balanced` over `orbitCycle a := (range
(orbitPeriod h)).image (fwdOrbit f g a)` (needs a total `OnCycle`-or-not case split, or phrase
`Balanced` per-anchor guarded by `OnCycle`), then `balanced_cons_*`.

### Addendum (same session, researcher-16) — Balanced invariant + full escape dichotomy CLOSED

Section **4i-ter** added (same PR #34114), all VERIFIED 0-axiom ({propext, Classical.choice,
Quot.sound}; NO sorryAx, NO Lean.ofReduceBool). Host `elan run leanprover/lean4:v4.26.0 lean`
with LEAN_PATH→main oleans, EXIT 0, only pre-existing warnings (myhill sorry + 2 unused `he` far
below the edit region).

- `def orbitCycle f g (h : OnCycle f g a) : Finset ℕ := (range (orbitPeriod f g h)).image
  (fwdOrbit f g a)` — named the recommended cycle encoding.
- `self_mem_orbitCycle` (`a ∈ orbitCycle`, stage 0), `mem_orbitCycle_iff`
  (`x ∈ orbitCycle ↔ ∃ k < period, fwdOrbit a k = x`). `orbitCycle_card` restated over the def.
- `def Balanced f g L := ∀ {a} (h : OnCycle f g a), (orbitCycle f g h ∩ (mDom L).toFinset).card =
  ((orbitCycle f g h).image f ∩ (mRan L).toFinset).card`. **Per-anchor, guarded by `OnCycle`** —
  the anchor is an IMPLICIT arg; supply the `OnCycle` proof to instantiate. No total case-split
  needed; the ¬OnCycle escape arm never consults `Balanced`.
- `balanced_nil` — `mDom []=mRan []=[]`, both `.toFinset=∅`, `inter_empty`, `card_empty`. Trivial.
- `escape_of_balanced` (Claim A, periodic arm) — the crux. Structure:
  1. `hInterDom`: `a∈C ∧ a∉mDom ⟹ C∩(mDom).toFinset ⊆ C.erase a ⟹ card ≤ C.card-1 = m-1`
     (`Finset.card_erase_of_mem`, `card_le_card`).
  2. balance (`hbal hac`) transports: `(C.image f ∩ (mRan).toFinset).card = (C∩mDom).card ≤ m-1`.
  3. `(C.image f).card = m` via `card_image_of_injOn (hf.injOn)` (f GLOBALLY inj ⟹ injOn C).
  4. `card(inter) ≤ m-1 < m = card(image) ⟹ ¬(image ⊆ mRan.toFinset)` (else `inter_eq_left`
     collapses to `image`, contradicting the strict `<`). `Finset.not_subset` gives fresh
     `y ∈ image, y ∉ mRan.toFinset`; unpack `y = f (fwdOrbit a k)`, `k<m` via `mem_orbitCycle_iff`.
  5. Least escaping stage `N := Nat.find hex` (`hex : ∃ N, f(fwdOrbit a N) ∉ mRan L`).
     `Nat.find_min'` ⟹ `N ≤ k < m`; `Nat.find_min` ⟹ earlier stages collide (∈ mRan).
     `f ∘ fwdOrbit` inj on `range N ⊆ range m` (via `fwdOrbit_injOn_range_period` + `hf`) ⟹
     `card_le_card_of_injOn` ⟹ `N ≤ (mRan).toFinset.card ≤ (mRan L).length`. Same pigeonhole
     tail as `escape_of_infinite_orbit`.
- `escape_exists'` — `by_cases OnCycle f g a`: OnCycle→`escape_of_balanced`, ¬OnCycle→
  `escape_of_infinite_orbit`. `BuiltFrom`-free, `Balanced`-hypothesised. **Drop-in for
  `escape_exists`**; the extension-only scheduler carries `Balanced` instead of `BuiltFrom`.

GOTCHAS worth recording (v4.26):
- Introduce `have hbalance := hbal hac` BEFORE the `set m`/`set C` folds, so `set` rewrites its
  `orbitCycle`/`orbitPeriod` occurrences to `C`/`m` (else `rw [← hbalance]` fails to unify with C).
- `mem_orbitCycle_iff` yields `k < orbitPeriod f g hac`; `rw [← hm] at hk` folds it back to `m`
  (set doesn't touch hyps created after it).
- `omega` closes the `i < m` membership subgoals for `fwdOrbit_injOn_range_period` using the
  in-context `hm : m = orbitPeriod …` equality between the two nat atoms.

**Remaining (scaffold step 3+):** `balanced_cons_domain`/`balanced_cons_range` (Claim B, cons-
preservation — the HARDEST piece: affected cycle both counts +1, other cycles inert via
injectivity/no-tails; key sub-lemma `b=f(fwdOrbit a N) ⟹ b∈f''C_a ∧ b∉f''C'` for other cycles);
then scheduler assembly on `domain_step_exists` carrying `Balanced` via `balanced_cons_*` and
discharging escape via `escape_exists'`; read-off; `.Computable`; close `myhill_isomorphism`.
Do NOT re-open the fork — Path B decided.

### Proof plan for `balanced_cons_domain` (Claim B) — worked out, NOT yet formalized (r16)

Goal: `Balanced f g L → a∉mDom L → b∉mRan L → (∃ N, b = f(fwdOrbit f g a N)) → Balanced f g ((a,b)::L)`.
Fix an arbitrary cycle anchor `c` (`h : OnCycle f g c`), let `C = orbitCycle f g h`. Note
`mDom ((a,b)::L)).toFinset = insert a (mDom L).toFinset`, likewise `insert b` on the range side.
Two cases on `a ∈ C`:

- **Case a∈C (the affected cycle).** `a∉(mDom L).toFinset` (fresh) ⟹
  `C ∩ insert a (mDom).toFinset = insert a (C ∩ (mDom).toFinset)`, card `= 1 + (C∩mDom).card`
  (`Finset.card_insert_of_not_mem`, `a∉C∩mDom`). Symmetrically `b∈C.image f` (KEY sub-lemma:
  `a∈C ⟹ fwdOrbit f g a N ∈ C`, i.e. the cycle is closed under the forward orbit — because
  `a∈C` makes `a` periodic and `C=C_a`, and `fwdOrbit a N` stays on `a`'s cycle) and `b∉mRan L`
  (fresh) ⟹ RHS card `= 1 + (C.image f ∩ mRan).card`. hbal for `c` equates the two `+1`-shifted
  cards.
- **Case a∉C (inert cycle).** LHS unchanged (`a∉C ⟹ C∩insert a … = C∩…`). RHS also unchanged,
  needs `b∉C.image f`: if `b=f(fwdOrbit a N)∈C.image f` then (f inj) `fwdOrbit a N∈C`, which is
  periodic, forcing (KEY sub-lemma, no-tails: `(g∘f)^[N] a` periodic ⟹ `a` periodic via
  injectivity of `(g∘f)^[N]`) `a` periodic with `C_a=C` (cycles sharing a point are equal),
  i.e. `a∈C` — contradiction. So `b∉C.image f`, RHS unchanged. Both sides unchanged ⟹ hbal.

Supporting lemmas to prove first:
1. `orbitCycle_closed_fwd`: `a∈orbitCycle f g h → fwdOrbit f g a N ∈ orbitCycle f g h`. (a on the
   cycle ⟹ periodic; forward orbit cycles back within one period; `fwdOrbit_add`/mod-period.)
2. `onCycle_of_fwdOrbit_onCycle` (no-tails): `OnCycle f g (fwdOrbit f g a N) → OnCycle f g a`.
   From `(g∘f)^[N+p] a = (g∘f)^[N] a` and `Function.Injective.iterate hT N` ⟹ `(g∘f)^[p] a = a`.
3. `orbitCycle_eq_of_mem` (disjoint-or-equal): `a∈orbitCycle f g h₁ (for c₁)` and same point on
   `c₂`'s cycle ⟹ the two `Finset`s are equal — OR phrase Case 2 purely via lemma 2 to avoid it.
`balanced_cons_range` is the `Prod.swap`/`(q,p,g,f)` dual. Both are pure Finset+orbit algebra,
0-axiom-friendly; no new sorries anticipated.

### CLAIM B CLOSED (r16, 2026-07-03) — `balanced_cons_domain`/`_range` VERIFIED 0-axiom

Section 4i-quater added (~150 lines). `balanced_cons_domain` proven **directly** (not via the
disjoint-or-equal lemma 3, which was avoided per the plan's "OR phrase Case 2 via lemma 2"). The
foreign-cycle-exclusion `mem_orbitCycle_of_fwdOrbit_mem` replaced lemma 3: from
`fwdOrbit a N ∈ C_c` and `OnCycle a`, reach `c` from `a` (`exists_fwdOrbit_eq_anchor` +
`fwdOrbit_add`), then close back `a` from `c` at step `p_a·(m/p_a+1) − m` via `fwdOrbit_mul_period`,
so `a ∈ C_c`. Orbit-algebra tower proved first: `fwdOrbit_add` (= `iterate_add_apply`),
`fwdOrbit_add_period`, `fwdOrbit_add_mul_period` (induction), `fwdOrbit_mul_period`,
`fwdOrbit_mod_period` (`Nat.mod_add_div` + add_mul_period). Membership: `mem_orbitCycle_of_reach`
(wrap mod period), `onCycle_of_mem_orbitCycle`, `fwdOrbit_mem_orbitCycle` (closure),
`onCycle_of_fwdOrbit` (no-tails via `hT.iterate N`).

Card argument: `mDom((a,b)::L)).toFinset = insert a (mDom L).toFinset` (`List.toFinset_cons`).
Case `a∈C`: `Finset.inter_insert_of_mem` twice (needs `a∈C` and `b∈C.image f` from
`fwdOrbit a N ∈ C`), `card_insert_of_notMem` twice (freshness), then `hbal hc`. Case `a∉C`:
`Finset.inter_insert_of_notMem` twice (needs `a∉C` and `b∉C.image f`; the latter is the exclusion
contrapositive), then `hbal hc`. GOTCHAS: `Finset.inter_insert_of_mem (h : a∈s₁) : s₁∩insert a s₂
= insert a (s₁∩s₂)` — membership is about the LEFT set; `card_insert_of_not_mem` is DEPRECATED →
use `card_insert_of_notMem`; `inter_insert_of_notMem` (camelCase) is current, `_not_mem` deprecated.

`balanced_cons_range` = `balanced_cons_domain hg hf` on the swapped problem `(g, f, L.map swap)`,
preserving `Balanced g f (L.map Prod.swap)` after `simp only [List.map_cons, Prod.swap_prod_mk]`;
freshness via `mDom_map_swap`/`mRan_map_swap`. Truly free — the `f∘g` cycles are the reverse orbits.

`#print axioms balanced_cons_domain` = `#print axioms balanced_cons_range` =
`[propext, Classical.choice, Quot.sound]` (no sorryAx/ofReduceBool). Verified via
`cd REPO/proofs && LAKE_UNSAFE=1 lake env lean <worktree abs path>/...SchroederBernsteinOQ03.lean`
(~17s warm), and a temp copy appending `open MyhillIsomorphism in #print axioms ...`.

**Remaining step-4 obligation surfaced: CROSS-PRESERVATION.** The scheduler must carry BOTH
`Balanced f g L` and `Balanced g f (L.map swap)` (each gives one direction's escape via
`escape_exists'`). `balanced_cons_domain` preserves the FORMER under a domain cons; the domain step
must ALSO preserve the swapped balance (and dually for the range step). Each is the same
foreign-cycle-exclusion argument applied on the OTHER dynamics: a domain cons `(a, f(fwdOrbit f g a
N))` adds `a` to mDom and `b` to mRan; for the `g∘f`-*reverse* (`f∘g`) cycles counted by the
swapped balance, `a` lands on some `f∘g`-cycle iff `b` does — provable but not yet formalized.

## Session 2026-07-03 (researcher-14): cross-preservation closed — Section 4i-quinquies (VERIFIED 0-axiom)

Closed the single remaining step-4 blocker before scheduler assembly: **cross-preservation** of
`Balanced`. The extension-only scheduler alternates a domain (even) and range (odd) step, and each
step's escape obligation is discharged on a *different* side — the domain step's `escape_exists'`
needs `Balanced f g L`, the range step's needs the swapped `Balanced g f (L.map swap)`. So the
scheduler must carry BOTH balances and each atomic move must preserve BOTH. `balanced_cons_domain`
(r16, #34114) already preserves `Balanced f g L` under a domain cons; the missing "cross" half was
that a domain cons ALSO preserves `Balanced g f (L.map swap)`.

Added **Section 4i-quinquies** to `SchroederBernsteinOQ03.lean` (3 decls, all VERIFIED 0-axiom —
`#print axioms` = {propext, Classical.choice, Quot.sound} for the main lemma; {propext} for the two
helpers; no sorryAx, no ofReduceBool). File 2460→2559 lines. Main `myhill_isomorphism` → sorry
UNCHANGED (still open).

- `fwdOrbit_swap_apply : fwdOrbit g f (f x) j = f (fwdOrbit f g x j)` — the `g∘f` and `f∘g`
  iterations are conjugate by `f`; the engine that relocates the escaped green image
  `b = f (fwdOrbit f g a N)` onto the swapped `f∘g`-orbit. 2-line induction.
- `onCycle_of_onCycle_apply : Injective f → OnCycle g f (f x) → OnCycle f g x` — periodicity
  transports across `f` (cancel the shared injective `f`).
- `balanced_swap_cons_domain` (main): a domain cons `(a,b)` with `b = f (fwdOrbit f g a N)` fresh
  preserves `Balanced g f (L.map swap)`.

**Key point — why this is NOT `balanced_cons_range`.** `balanced_cons_range` needs the placed pair
to satisfy `a = g (fwdOrbit g f b N')` (an `f∘g`-orbit relation between `a` and `b`). Computing
`g (fwdOrbit g f b j) = fwdOrbit f g a (N+j+1)`, so `a = g(fwdOrbit g f b j)` requires
`fwdOrbit f g a (N+j+1) = a`, i.e. `a` returns to itself — possible ONLY when `a`'s `g∘f`-orbit is
a finite cycle. When the orbit is infinite there is NO such `N'`, yet the swapped balance is still
preserved (both intersections inert on every `f∘g`-cycle). `balanced_swap_cons_domain` handles both
uniformly via a single `by_cases` on `b ∈ orbitCycle g f hc` — the dichotomy that actually controls
the invariant, rather than the periodic/infinite split at the top level:
  * `b ∈ C`: `b` periodic ⟹ (via `onCycle_of_onCycle_apply` + `onCycle_of_fwdOrbit`) `a` is
    `g∘f`-periodic with period `m`; the witness `y := fwdOrbit g f b (m*(N+2) − (N+1))` lands in `C`
    (closure, `fwdOrbit_mem_orbitCycle`) and `g y = fwdOrbit f g a (m*(N+2)) = a`
    (`fwdOrbit_mul_period`). So `a ∈ C.image g`; both sides gain one fresh point.
  * `b ∉ C`: if `a = g y` with `y ∈ C` then `b = fwdOrbit g f y (N+1) ∈ C` (closure) — contradiction.
    So `a ∉ C.image g`; both sides inert.

The clean direction (`b ∉ C`) needs no modular arithmetic; only the `b ∈ C` witness does, and it is
purely mechanical given the existing orbit-algebra tower (`fwdOrbit_add`, `fwdOrbit_mul_period`,
`fwdOrbit_swap_apply`, `fwdOrbit_succ`).

### Next Steps (updated)
1. **Range-step dual:** `balanced_cons_range` (swapped) + the analogous `balanced_swap_cons_range`
   (a range cons preserves `Balanced f g L`) — obtainable for free from `balanced_swap_cons_domain`
   by the `Prod.swap` duality (apply to `(g, f, L.map swap)`), mirroring how `balanced_cons_range`
   reuses `balanced_cons_domain`. This completes "carry BOTH balances across BOTH steps".
2. Build the extension-only stage function on `domain_step_exists` (cons; escape via
   `escape_exists'`) carrying the pair `(Balanced f g L, Balanced g f (L.map swap))`, preserved by
   `balanced_cons_domain` + `balanced_swap_cons_domain` (even) and the two range duals (odd).
3. Read off `e` via `mLookup` + `mLookup_stable` (pair-monotone since cons-only), prove `.Computable`,
   discharge the `myhill_isomorphism` sorry. NOTE: the current Section 4m `stageSeq` is built on the
   *splicing* `augment_*_step` (removes/relabels g-edges ⟹ NOT pair-monotone ⟹ `mLookup_stable` does
   not apply). The decided Path B rebuilds `stageSeq` on the cons steps above; do NOT read off the
   existing splicing `stageSeq`.

**Build/verify:** r16's non-Docker path confirmed working this session — the file is self-contained
on Mathlib, so `LEAN_PATH` → main repo's prebuilt package oleans
(`$MAIN/proofs/.lake/packages/*/.lake/build/lib/lean` + `$MAIN/proofs/.lake/build/lib/lean`) with
`elan run leanprover/lean4:v4.26.0 lean Proofs/SchroederBernsteinOQ03.lean`. Full file compiles in
~30s (oleans cached); only warning is the expected `myhill_isomorphism` sorry. No Docker, no lake build.

## Session (researcher-4, 2026-07-03) — CROSS-PRESERVATION 2×2 MATRIX COMPLETE

Added `balanced_swap_cons_range` (Section 4i-quinquies, right after `balanced_swap_cons_domain`),
the missing fourth cell of the balance-preservation matrix. VERIFIED 0-axiom
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no sorryAx/ofReduceBool). File
2575→2632 lines, +1 theorem. The `myhill_isomorphism` sorry is UNCHANGED (infrastructure, not
closure).

**Why this was the next step.** The extension-only scheduler alternates a domain (even) and a
range (odd) cons, and the two sides' *escape* obligations consume different invariants: the domain
escape (`escape_of_balanced`/`escape_exists'`) needs `Balanced f g L`, the range escape needs the
swapped `Balanced g f (L.map Prod.swap)`. So the scheduler must carry BOTH and each atomic step
must preserve BOTH — a 2×2 matrix of lemmas:

|                | preserves `Balanced f g L` | preserves `Balanced g f (L.map swap)` |
|----------------|----------------------------|----------------------------------------|
| **domain step**| `balanced_cons_domain`     | `balanced_swap_cons_domain`            |
| **range step** | `balanced_swap_cons_range` ← NEW | `balanced_cons_range`            |

The two off-diagonal ("swap") cells are the genuinely-new cross-preservation obligations flagged in
state.md. `balanced_swap_cons_domain` was merged by r16 (PR #34114 line); `balanced_swap_cons_range`
was still missing. It is NOT an instance of `balanced_cons_domain`: the domain-cons pair `(a,b)` in a
range step does not satisfy the `f∘g`-orbit relation `b = f (fwdOrbit f g a N')` unless `a`'s orbit
is a finite cycle, so a uniform `by_cases` on cycle membership is required.

**Proof.** Exact `f ↔ g` mirror of `balanced_swap_cons_domain`. Range cons `(a,b)`, `b` fresh range
anchor, `a = g (fwdOrbit g f b N)` the escaped `g`-image; preserve un-swapped `Balanced f g L`. Fix
a `g∘f`-cycle anchor `c`, `C = orbitCycle f g hc`. `by_cases a ∈ C`:
- `a ∈ C`: show `b ∈ C.image f`. `a` periodic ⇒ (`onCycle_of_onCycle_apply hg` on `a =
  g(fwdOrbit g f b N)`, then `onCycle_of_fwdOrbit hg hf`) `b` is `f∘g`-periodic; take the witness
  `fwdOrbit f g a (p_b·(N+2) − (N+1))` (`p_b = orbitPeriod g f hob`), on `C` by
  `fwdOrbit_mem_orbitCycle`, and `f`-mapping to `b` via `fwdOrbit_swap_apply` + `fwdOrbit_succ` +
  `fwdOrbit_add` + `fwdOrbit_mul_period` (the `nlinarith`/`omega` period arithmetic is identical to
  the domain lemma). Both intersections gain one fresh point (`inter_insert_of_mem` ×2 +
  `card_insert_of_notMem` ×2), then `hbal hc`.
- `a ∉ C`: show `b ∉ C.image f`. If `b = f y`, `y ∈ C`, then `a = fwdOrbit f g y (N+1)` (via
  `fwdOrbit_swap_apply` + `simp [fwdOrbit]`) is on `C` (`fwdOrbit_mem_orbitCycle`) — contradiction.
  Both intersections inert (`inter_insert_of_notMem` ×2), then `hbal hc`.

Reused the two helper lemmas `balanced_swap_cons_domain` introduced: `fwdOrbit_swap_apply`
(`fwdOrbit g f (f x) j = f (fwdOrbit f g x j)`, orbit conjugation by the head map) and
`onCycle_of_onCycle_apply` (`OnCycle g f (f x) → OnCycle f g x`, periodicity transports across an
injective `f`). No new orbit-algebra lemmas were needed — the diagonal from `balanced_swap_cons_domain`
already supplies everything.

**Verify path (r16's, confirmed working under disk pressure):** the file is self-contained on
Mathlib, so from `REPO/proofs`: `LAKE_UNSAFE=1 lake env lean <worktree-abs>/…/SchroederBernsteinOQ03.lean`
against the main repo's prebuilt oleans (no Docker, no `lake build`). Only warnings emitted are the
pre-existing `myhill_isomorphism` sorry and two pre-existing `unused variable he` linter notes.

**ENVIRONMENT NOTE (07-03):** host disk is at 100% (≈2–6 GB free, fluctuating). Unlocked worktrees
under `.loom/worktrees/` are being deleted by a cleanup daemon — even mid-command. Workaround that
survived: create the worktree under `/tmp` with `git worktree add --lock` (locked worktrees are not
pruned; other agents' `/private/tmp/*` worktrees show `locked`). Do NOT thrash `.loom/worktrees`.

**Remaining critical path (unchanged in kind):** assemble the extension-only scheduler on
`domain_step_exists` + the dual range cons, carrying both balances via the (now-complete) cons matrix
and discharging escape via `escape_exists'` (both sides); read off `e` with `mLookup` +
`mLookup_stable`; prove `.Computable`; close the `myhill_isomorphism` `→` sorry. Coverage
(`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`) follows. Do NOT re-open the Path-B fork.

## Session 2026-07-03 (researcher-11): PATH B ASSEMBLED — cons scheduler + limit bijection VERIFIED 0-axiom

**Major advance.** Built the entire extension-only (Path B) scheduler and read off the limit
bijection. `myhill_isomorphism` is now reduced from "everything open" to **computability only**:
the bijection `sigmaEquivB : ℕ ≃ ℕ` with `∀ n, p n ↔ q (sigmaEquivB n)` is VERIFIED. File
2718→2980 lines, +6 defs +17 theorems, new **Section 5·B**. All new decls 0-axiom
(`#print axioms` = {propext, Classical.choice, Quot.sound}; NO sorryAx, NO ofReduceBool). Host
`LAKE_UNSAFE=1 lake env lean` v4.26.0 against main-repo oleans, EXIT 0; only the pre-existing
`myhill_isomorphism` sorry + two pre-existing unused-`he` warnings.

**What was built (Section 5·B):**
- `StageInvB p q f g L := IsMatching L ∧ MatchingCorr p q L ∧ Balanced f g L ∧ Balanced g f (L.map swap)`
  — the cons-preserved invariant (carries BOTH balances instead of `BuiltFrom`).
- `domain_consStep` / `range_consStep` — the atomic Path-B moves. A fresh domain anchor `a`
  (resp. range anchor `b`) is placed by a *pure cons* `(a, chaseTarget f g a N) :: L` (resp.
  `(chaseTarget g f b N, b) :: L`), preserving all four invariants. Escape via `escape_exists'`
  (Balanced, `BuiltFrom`-free); balances via the 2×2 matrix (`balanced_cons_domain`,
  `balanced_swap_cons_domain` for even; `balanced_swap_cons_range`, `balanced_cons_range` for odd);
  correspondence via `matching_step_chase` (even) / `chaseTarget_corr … |>.symm` (odd, swapped).
- `stageStepB` / `stageSeqB` — the sequence (subtype carrying `StageInvB`), even `s` targets
  domain `s/2`, odd targets range `s/2`, keep-if-covered else cons.
- **`stageStepB_pair_subset` / `stageSeqB_pair_subset`** — THE property Path A (splicing) lacked:
  every recorded PAIR survives to every later stage (cons never removes). This is exactly the
  `L₁ ⊆ L₂` hypothesis of `mLookup_stable`.
- `stageSeqB_covers_dom` / `_covers_ran` — `k` covered by stage `2k+1` (dom) / `2k+2` (ran).
- **Read-off (`section ReadOff`):** `entryStageDomB n := Nat.find …`, `sigmaB n := mLookup
  (stageSeqB (entryStageDomB n)).1 n`, `sigmaB_eq_of_mem_dom` (stability via
  `mLookup_stable` + `stageSeqB_pair_subset` — NO finite injury), `sigmaB_corr`
  (`p n ↔ q (σ n)` from `MatchingCorr`), `sigmaB_injective` (evaluate both at a common stage,
  `mLookup_injOn`), `sigmaB_surjective` (from range exhaustion), and
  `sigmaEquivB := Equiv.ofBijective sigmaB ⟨inj, surj⟩` + `sigmaEquivB_corr`.

**Why this closes the strategic arc.** The fork r4/r14 debated (termination↔stability) was
decided Path B; r16/r14/r4 proved all four balance-preservation cells; but the FILE's `stageSeq`
was still the splicing Path-A version (not pair-monotone), so no read-off was possible. This
session actually *assembled* the cons scheduler the decision called for, and the read-off went
through mechanically because pair-monotonicity makes `mLookup_stable` apply directly. The
mathematics of Myhill's hard direction (the computable-injections ⟹ bijection-with-correspondence)
is now COMPLETE and verified as a plain bijection.

**The SOLE remaining gap: computability.** `stageSeqB` is `noncomputable` (built via
`Classical.choose`/`.choose` on the `domain_consStep`/`range_consStep` existentials), so
`sigmaEquivB` is not yet a `Computable` permutation and `myhill_isomorphism`'s `e.Computable`
conjunct cannot be discharged — the `sorry` remains. Residual work (well-scoped):
1. Replace the escape `.choose N` with the bounded `Nat.rfind`/`Nat.find` search over
   `fun N => decide (chaseTarget f g a N ∉ mRan L)` — this is computable because `escape_exists'`
   bounds `N ≤ (mRan L).length`, `chaseTarget` is computable (`chaseTarget_computable`), and
   `mRan L` membership is decidable. Likewise the range side.
2. Rebuild a computable parallel `stageSeqBComp : ℕ → List (ℕ × ℕ)` (explicit cons recursion,
   no `.choose`), prove it equals `(stageSeqB …).1` (or re-prove the read-off lemmas on it), and
   establish `Computable (fun n => mLookup (stageSeqBComp (entryStageDomB n)) n)` via
   `mLookup_computable` + computability of the stage recursion (the escape `rfind` is `Partrec`,
   total by `escape_exists'`, hence `Computable`) + `entryStageDomB` computable (bounded search
   over the computable coverage predicate).
3. Read off `e.Computable ∧ e.symm.Computable` (the inverse is the range-side `mLookup` on
   `(stageSeqBComp …).map swap`); discharge the `myhill_isomorphism` sorry.

This is genuinely the last mile: no new mathematics, only a computable re-encoding of the already
-verified construction. Estimated ~150–250 lines.

**Build/verify path (works, disk at ~90 GiB free this session — not the 100%-full crisis of
prior sessions):** file self-contained on Mathlib; from `REPO/proofs`:
`LAKE_UNSAFE=1 lake env lean /tmp/lg-r11-sb/proofs/Proofs/SchroederBernsteinOQ03.lean` against the
main-repo prebuilt oleans (`proofs/.lake/...`). ~30s warm. For fast iteration, build the module
olean once (`lake env lean -o .lake/build/lib/lean/Proofs/SchroederBernsteinOQ03.olean Proofs/...`)
then a scratch file `import Proofs.SchroederBernsteinOQ03; open MyhillIsomorphism` compiles new
lemmas in ~5–20s.

**WORKTREE HAZARD (recurred):** the assigned `.loom/worktrees/researcher-11` was CLOBBERED
(reset to HEAD) mid-session — edits silently reverted. Recovered by working in a LOCKED `/tmp`
worktree (`git worktree add --lock /tmp/lg-r11-sb -b … origin/main`); locked worktrees survive the
cleanup daemon. All verified content was staged in `/tmp/sb_scratch.lean` (outside the reaped tree)
so it survived the clobber. Commit+push immediately from the locked worktree.
