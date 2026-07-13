# Knowledge Base: friendship-theorem-oq-04

**Friendship Theorem for infinite graphs** — where does the finite proof break,
and what extra condition restores the conclusion?

---

## Problem Understanding

Finite Friendship Theorem (Erdős–Rényi–Sós 1966): in a *finite* simple graph in
which every two distinct vertices have **exactly one** common neighbor, some
vertex is adjacent to all others (a "politician"); the graph is a windmill
`W_k` (k triangles sharing a center, `2k+1` vertices).

OQ-04 asks the infinite analogue: pin down (i) that the theorem **fails** for
infinite graphs, (ii) *exactly which step* of the finite proof breaks, and
(iii) what extra hypothesis brings the conclusion back.

The gallery's finite proof (`proofs/Proofs/FriendshipTheorem.lean`) is a clean
two-step reduction:
- `friendship_has_universal_or_regular` (FriendshipTheorem.lean:179) — dichotomy:
  universal vertex **or** the graph is `k`-regular. (A³-commutativity gives
  "non-adjacent ⟹ equal degree"; complement-connectivity propagates it.)
- `friendship_regular_implies_universal` (FriendshipTheorem.lean:193) — the
  **spectral / eigenvalue-integrality** argument forcing `k = 2`.

---

## Insights (Session 1, 2026-06-15 — ORIENT)

### 1. Counterexample exists (theorem fails for infinite graphs)
Chvátal–Kotzig–Rosenberg–Davies (Canad. Math. Bull. 19(4), 1976: *"There are
2^ℵ_α friendship graphs of cardinal ℵ_α"*). Standard construction = **C₅ free
amalgamation**: start from the 5-cycle; repeatedly add a brand-new private
common neighbor to every pair that currently has none. The countable limit is a
friendship graph with **no universal vertex**.

I verified the construction's correctness invariant myself (not just cited):
adding a fresh `w` adjacent to exactly a zero-common-neighbor pair `{u,v}`
**preserves** the "linear" property (no pair has ≥2 common neighbors), because
any other vertex `x` is adjacent to at most one of `{u,v}` (else `x` would
already be a common neighbor of `u,v`, contradicting zero). So every new pair
`{w,x}` gets ≤1. Hence the closure converges to a genuine friendship graph.
`verify_infinite_friendship.py` confirms max-common-neighbors stays = 1 across 4
rounds (|V| up to 3695), the original C₅ vertices reach exactly-one pairwise, and
**max degree strictly grows** `[4,5,13,83]` ⟹ the limit is **locally infinite**.

### 2. Diameter ≤ 2 — the lemma that SURVIVES infinity
For **every** friendship graph (finite or infinite) and any vertex `v`:

    V = {v} ∪ N(v) ∪ ⋃_{x ∈ N(v)} N(x).

Reason: any non-neighbor `u ≠ v` has a unique common neighbor `x` with `v`;
`x ∈ N(v)` and `u ∈ N(x)`. This is purely local — no finiteness used. Verified
on windmills `W_1..W_8` and on the amalgamation graph.

### 3. RESTORING CONDITION = local finiteness (sharp)
From the diameter-2 covering: if **every degree is finite**, then `V` is a finite
union (`N(v)` finite, each `N(x)` finite) of finite sets ⟹ `V` finite ⟹ (by ERS)
windmill ⟹ universal vertex. So:

> **A locally finite friendship graph is finite (a windmill); the obstruction to
> the infinite theorem is *precisely* the existence of an infinite-degree
> vertex.** Every infinite friendship graph has all (or at least one — in fact,
> by the covering, infinitely many) vertices of infinite degree.

This is a *more elementary* route than the spectral argument: it bypasses
eigenvalues entirely (a 2-ball covering bound). Verified the bound
`|V| ≤ 1 + deg(v) + Σ_{x∈N(v)} deg(x)` on `W_1..W_13`.

### 4. WHERE the finite proof breaks (bearer-pinned)
- **Dichotomy** `friendship_has_universal_or_regular`
  (FriendshipTheorem.lean:179): the "non-adjacent ⟹ equal degree" bijection
  survives only as a **cardinality** statement. When degrees are infinite all
  are equal (= ℵ₀), so the dichotomy's "regular" branch becomes *vacuous* — it
  carries no finite arithmetic content. (The C₅-amalgam counterexample is
  neither universal nor regular, so the dichotomy itself is *false* infinitely.)
- **Spectral step** `friendship_regular_implies_universal`
  (FriendshipTheorem.lean:193) — the **hard break**. Its OQ01 engine is entirely
  finite-matrix algebra:
  - `adjMatrix_sq_eq`: `A² = (k-1)I + J` (FriendshipTheoremOQ01.lean:363)
  - `adjMatrix_trace_zero`: `tr A = 0` (OQ01:362)
  - `trace_adjMatrix_sq`: `tr A² = nk` (OQ01:367) — uses finite `n`
  - `k_sub_one_is_perfect_square` (OQ01:328) and `k_eq_two_no_axiom` (OQ01:330):
    integer eigenvalue multiplicities `m₊,m₋` with `k + (m₊−m₋)s = 0` force
    `k−1 = s²` then `k = 2`.
  None of trace, finite multiplicities, or eigenvalue integrality has an infinite
  analogue. This is the irreducible finiteness in the ERS proof.

---

## Lean target (for a future ACT session, build-gated)

The cleanly formalizable infinite-side results, in order of tractability:

1. `friendship_diameter_two`: `∀ v u, u ≠ v → u ∈ N(v) ∨ ∃ x ∈ N(v), u ∈ N(x)`
   — no `[Fintype V]` needed; pure unfolding of `IsFriendshipGraph` + `ncard=1`.
2. `locally_finite_friendship_is_finite`: with `[LocallyFinite G]` (each
   `neighborSet` finite), `Set.Finite (univ : Set V)` via the covering of (1) as
   a finite union of finite sets (`Set.Finite.biUnion`).
3. Corollary: combine (2) with the existing finite `friendship_theorem`
   (needs bridging `Set.Finite` → `Fintype`) to get a universal vertex under
   local finiteness — the "conclusion restored" statement.

(1)+(2) are `< 150` lines and **finiteness-light**; good Aristotle/ACT targets
once the build backend is available.

---

## Session 2 (2026-06-15 — ACT, build-pending)

Transcribed the ORIENT plan into Lean: **`proofs/Proofs/FriendshipTheoremOQ04.lean`**
(new file, namespace `FriendshipTheoremOQ04`, unregistered in `Proofs.lean` while
the build backend is down — registering a possibly-erroring file into the
auto-merged aggregator would break `main` for everyone).

Contents (all spectral-free, finiteness-light):
- `IsFriendshipGraph` — the `ncard (commonNeighbors) = 1` property *without*
  `[Fintype V]`; definitionally equal to `FriendshipTheorem.IsFriendshipGraph`.
- `exists_common_neighbor` — `ncard = 1 ⟹` a witness via `Set.ncard_eq_one`.
- `friendship_diameter_two` — `u ≠ v ⟹ G.Adj v u ∨ ∃ x, G.Adj v x ∧ G.Adj x u`.
- `univ_subset_two_ball` — `univ ⊆ {v} ∪ N(v) ∪ ⋃_{x∈N(v)} N(x)`.
- `univ_finite_of_locallyFinite` / `locally_finite_is_finite` — local finiteness
  `⟹ (univ).Finite ⟹ Finite V`, via `Set.Finite.biUnion` over the covering.
- `locally_finite_friendship_has_universal` — capstone: bridge `Finite → Fintype`
  (`Fintype.ofFinite`), card `≥ 3` from three distinct vertices
  (`Finset.card_eq_three` + `Finset.card_le_univ`), then apply the finite
  `FriendshipTheorem.friendship_theorem`. Coercion of the friendship hypothesis is
  the identity lambda (definitional equality of the two `IsFriendshipGraph`s).

**Verification status**: NOT machine-checked — Docker build host and Aristotle
backend both unavailable this session (Aristotle `prove` returns 404; `docker info`
times out). Proofs were written for high static compile-confidence and audited by
hand against in-repo lemma usages. Names to re-confirm at build time:
`Set.finite_univ_iff`, `Set.univ_eq_empty_iff`, `Set.Finite.biUnion` arity.

This is the **positive half** of OQ-04 (sharp restoring condition). The negative
half (formalizing the C₅-amalgamation infinite counterexample) remains open.

## Dead Ends / Non-starters
- Trying to recover the theorem via *regularity* alone fails: infinite degrees
  are all "equal" as cardinals, so regularity is vacuously satisfiable without a
  universal vertex (the amalgam is a witness).
- The spectral argument has no salvageable infinite generalization (no trace).

---

## References
- P. Erdős, A. Rényi, V. T. Sós, *On a problem of graph theory*, Studia Sci.
  Math. Hungar. 1 (1966).
- V. Chvátal, A. Kotzig, I. G. Rosenberg, R. O. Davies, *There are 2^ℵ_α
  friendship graphs of cardinal ℵ_α*, Canad. Math. Bull. 19(4) (1976) 431–433.
- *Degrees of vertices in a friendship graph*, Canad. Math. Bull. (1976).

## Session 3 (researcher-4, 2026-06-15) — audit S2 file + sharp-obstruction corollary

**Mode**: REVISIT · **Outcome**: progress (audit + 1 new theorem). Docker down
(`docker info` timeout), so build-free; the file stays UNREGISTERED.

### Audited the S2 build-pending file `FriendshipTheoremOQ04.lean`
Confirmed the riskiest step — the capstone `locally_finite_friendship_has_universal`
calls `FriendshipTheorem.friendship_theorem G (fun u v h => hF u v h) h3`. Verified:
- `FriendshipTheorem.IsFriendshipGraph` (FriendshipTheorem.lean:79) is **literally
  identical** to the OQ04 def (`∀ u v, u ≠ v → (commonNeighbors u v).ncard = 1`), so
  the coercion lambda is definitional — sound.
- `G` is an **explicit** `variable (G : SimpleGraph V)` (FriendshipTheorem.lean:112),
  and the internal call `friendship_theorem G hF h` (line 230) confirms the arg order
  `friendship_theorem G <friendshipHyp> <card≥3>` — so the capstone's call form is
  correct (a `friendship_theorem <hyp> h3` form would have been a bug). `[DecidableRel
  G.Adj]`/`[DecidableEq V]` are supplied by `classical`; `[Fintype V]` by `Fintype.ofFinite`.
- The S2-flagged Mathlib names all check out: `not_finite (α)[Infinite][Finite]:False`
  (Finite/Defs.lean:160), `Set.finite_univ_iff`, `Set.univ_eq_empty_iff`,
  `Set.Finite.biUnion`, `Set.ncard_eq_one`, `SimpleGraph.mem_commonNeighbors`.
  High-confidence buildable; safe to register next Docker session.

### New theorem: `infinite_friendship_has_infinite_degree`
Added the **sharp obstruction** (contrapositive of `locally_finite_is_finite`): every
*infinite* friendship graph has a vertex of infinite degree. `[Infinite V] ⟹ ∃ w,
(neighborSet w).Infinite`, by `by_contra` + `Set.not_infinite.mp` + the finiteness
theorem + `not_finite V`. This is the direct OQ-04 "where the proof breaks" headline —
the obstruction is *precisely* an infinite-degree vertex (the defining feature of the
C₅-amalgam counterexample). Spectral-free, ~6 lines.

### Still open
The **negative half** — formalizing the C₅ free-amalgamation infinite counterexample
(an explicit friendship graph with no universal vertex) — remains open; it needs an
infinite inductive-limit construction, not build-safe-tractable under blackout.

---

## Session: registration (researcher-4)

### Registered `FriendshipTheoremOQ04.lean` in the build manifest
The file had landed on `main` (8 theorems, 0 sorry, 0 axiom) but was **absent from
`proofs/Proofs.lean`** — the explicit import manifest. The three siblings
(`FriendshipTheorem`, `…OQ01`, `…OQ02`, `…OQ03`) were all imported; OQ04 was the lone
gap, so its "0 sorry / 0 axiom" status was inspection-only — Lean never built it.

Added the single line `import Proofs.FriendshipTheoremOQ04`. Re-confirmed before
shipping (build-free, Docker blackout still live — `docker ps` exit 124):
- `friendship_theorem` takes `G` **explicitly** (`variable (G : SimpleGraph V)` at
  `FriendshipTheorem.lean:112`); the in-file caller `friendship_theorem G hF h`
  (lines 232/255) fixes the arg order, matching the capstone's
  `friendship_theorem G (fun u v h => hF u v h) h3`.
- All Mathlib names in the file resolve in the pinned toolchain (see audit entry above).

Registration is **deployer-gated**: if the build fails, the PR is blocked and `main`
stays clean — safe to ship under blackout. The deployer's build now machine-checks the
positive OQ-04 result.

### Still open (unchanged)
Negative half — the C₅ free-amalgamation infinite counterexample — still needs an
inductive-limit construction; not build-safe-tractable under blackout.

---

## Session (researcher-6, 2026-06-15) — finiteness-free infinite windmill structure

**Mode**: REVISIT (RICH) · **Outcome**: progress (2 new theorems). Docker down
(`docker info` timeout); build-pending. Worked in a fresh `.claude/worktrees`
worktree off `origin/main` (loom worktree resets mid-session).

### Added to `FriendshipTheoremOQ04.lean` (2 theorems, still 0 sorry / 0 axiom)
- `universal_noncentral_neighborSet`: in a friendship graph with a universal vertex
  `c` (finite **or** infinite), every non-centre `u` satisfies `G.neighborSet u =
  {c, w}` for a unique partner `w ≠ c` — i.e. the **infinite windmill** structure.
- `universal_noncentral_ncard_two`: corollary `(G.neighborSet u).ncard = 2`.

**Why this is new (not a dup of the finite proof):** the gallery's finite
`FriendshipTheorem.friendship_noncentral_degree` (FriendshipTheorem.lean:135) proves
`G.degree u = 2` — `G.degree` is a `Fintype` notion, so that lemma is unusable on
infinite vertex types. The *set* equality `N(u) = {c, w}` underlying it needs **no
finiteness**; this session states it directly, completing the "conclusion restored"
side of OQ-04 by showing the recovered graph is genuinely a windmill even infinitely.

**Verification (build-free).** The proof is a near-verbatim port of the compiling
finite proof (FriendshipTheorem.lean:138–163), swapping `neighborFinset`→`neighborSet`
and `Finset.mem_insert`/`Finset.card_pair`→`Set.mem_insert_iff`/`Set.ncard_pair`.
All bearers in use already in this repo: `Set.ncard_eq_one`,
`SimpleGraph.mem_commonNeighbors`, `SimpleGraph.mem_neighborSet`, `Set.ncard_pair`
(e.g. Erdos157Problem.lean:72), `G.loopless`, `G.symm`. High static confidence;
machine-check deferred to the next Docker-up deployer build (deployer-gated, so a
compile error blocks the PR rather than reaching `main`).

### Still open (unchanged)
Negative half — the C₅ free-amalgamation infinite counterexample — still needs an
inductive-limit construction; not build-safe-tractable under blackout.

## Session (researcher-2, 2026-06-15) — unique infinite-degree hub (sharp count)

**Mode**: REVISIT (RICH) · **Outcome**: progress (3 new theorems, still 0 sorry / 0
axiom). Docker reachable but **8 concurrent lean-build containers** on the 7.65GiB VM
⟹ a local build would OOM all peers (see [[project-docker-7gb-vm-is-the-real-oom-constraint]]),
so build-pending → deployer-gated machine-check. File already registered in
`proofs/Proofs.lean`. Aristotle still 404.

### Added to `FriendshipTheoremOQ04.lean` (3 theorems)
Sharpens the obstruction `infinite_friendship_has_infinite_degree` ("≥1 infinite-degree
vertex") to an *exact count* in the conclusion-restored (universal-vertex) case:
- `infinite_degree_vertex_eq_universal`: in ANY friendship graph with universal `c`,
  every infinite-degree vertex equals `c` (no `[Infinite V]`). Proof: a non-centre
  vertex has `ncard N = 2` (`universal_noncentral_ncard_two`), but an infinite set has
  `ncard = 0` (`Set.Infinite.ncard`); `omega` on `0 = 2`.
- `universal_vertex_infinite_degree`: `[Infinite V]` + universal `c` ⟹ `c` itself has
  infinite degree. Proof: `infinite_friendship_has_infinite_degree` yields some
  infinite-degree `w`; the previous lemma forces `w = c`; `rwa`.
- `unique_infinite_degree_vertex` (capstone iff): `[Infinite V]` + universal `c` ⟹
  `(G.neighborSet w).Infinite ↔ w = c`. The infinite windmill has a **single** hub of
  infinite degree, every other vertex degree two — "as infinite as the finite theorem
  permits."

**Why new (not cosmetic):** `infinite_friendship_has_infinite_degree` only bounds the
infinite-degree set below by 1; this pins it to exactly 1 (in the universal case) and
identifies it with the hub. Structural sharp-boundary result, theory-level.

**Verification (build-free).** Each proof is a 3–5 line composition of already-compiling
in-file lemmas (`universal_noncentral_ncard_two`, `infinite_friendship_has_infinite_degree`)
plus `Set.Infinite.ncard` (used in `Erdos152ProblemAPN.lean:247`). High static confidence.

### Still open (unchanged)
Negative half — the C₅ free-amalgamation infinite counterexample (an explicit friendship
graph with no universal vertex) — still needs an inductive-limit / colimit construction;
not build-safe-tractable in one session, and confirmed so across S1–S6.

## Session (researcher-8, 2026-06-16) — regularity lemma (finiteness-free)

**Mode**: REVISIT (RICH) · **Outcome**: progress (1 new theorem, still 0 sorry / 0
axiom). Docker **GREEN** — `✔ [7745/7745] Built Proofs.FriendshipTheoremOQ04` (cold
`.lake`, shared cache volume; 6 GB cap). Aristotle still 404.

### Added to `FriendshipTheoremOQ04.lean` (1 theorem)
`nonadjacent_neighborSet_equinum`: in *any* friendship graph, two **non-adjacent**
vertices `u`, `v` have a bijection `N(u) → N(v)` — the map `w ↦` (unique common
neighbour of `w` and `v`). Stated as `∃ f, Set.BijOn f (G.neighborSet u) (G.neighborSet v)`
so it carries content on infinite neighbourhoods (`ncard` collapses to 0 there). No
`[Fintype V]` / `[Infinite V]`.

**Why this matters (negative half).** This is the finiteness-free analogue of the step
the *finite* proof uses inside `FriendshipTheorem.friendship_has_universal_or_regular`
("non-adjacent ⟹ equal degree", there derived via A³-commutativity / matrix algebra).
Here it is purely combinatorial. Consequence: a friendship graph with **no** universal
vertex necessarily contains a non-adjacent pair, hence is *regular* — so the C₅
free-amalgamation counterexample is ℵ₀-regular. This pins down the structure any
counterexample must have, complementing the positive results (`infinite_friendship_has_infinite_degree`,
`unique_infinite_degree_vertex`).

**Proof.** `choose` a common-neighbour function (total via a `w = v` dummy branch).
MapsTo/InjOn/SurjOn each reduce to the friendship singleton (`Set.ncard_eq_one`):
injectivity uses that two preimages are common neighbours of `(f w₁, u)` with `f w₁ ≠ u`
(since `f w₁ ∈ N(v)` and `u ∉ N(v)`); surjectivity inverts via the common neighbour of
`(y, u)`. No spectral input.

### Still open (unchanged)
Negative half **construction** — the explicit C₅ free-amalgamation friendship graph with
no universal vertex (now known to be ℵ₀-regular) — still needs an inductive-limit /
colimit build; not single-session-tractable, confirmed across S1–S7.

## Session (researcher-11, 2026-06-18) — local windmill: edge ⟹ unique triangle

**Mode**: REVISIT (RICH) · **Outcome**: progress (2 new theorems, still 0 sorry / 0
axiom). Docker **blackout** (`docker info` rc=124, overloaded 7GB VM); build-free,
deployer-gated. Aristotle still 404. Fresh worktree off `origin/main`.

### Context first (avoided a near-duplicate)
On entry, `origin/main`'s `FriendshipTheoremOQ04.lean` was already 414 lines (newer than
knowledge.md): the **regularity engine** I had planned —
`neighborSet_equinum_of_common_nonneighbor` (compose `N(u)≃N(z)≃N(v)` for a common
non-neighbour `z`) plus the dichotomy wrapper
`neighborSet_equinum_of_nonadj_or_common_nonneighbor` — was landed by a prior session
(#25865-era). Re-scoped to a non-overlapping increment.

### Added to `FriendshipTheoremOQ04.lean` (2 theorems)
- `common_neighbor_unique`: every two **distinct** vertices have *exactly one* common
  neighbour, as the reusable `∃!` form (the file previously had only existence via
  `exists_common_neighbor`). Direct from `Set.ncard_eq_one` + `mem_commonNeighbors`,
  mirroring the existing `exists_common_neighbor` pattern (lines 90–96).
- `edge_unique_triangle`: for an adjacent pair `u, v`, a **unique** `w` adjacent to
  both — every edge lies in exactly one triangle. Equivalently **`N(u)` induces a
  perfect matching** (each neighbour of `u` has exactly one neighbour inside `N(u)`,
  the triangle apex). One-line corollary of `common_neighbor_unique` via `huv.ne`.

**Why this is on-theme (not cosmetic).** The result is *unconditional* — it needs
neither a universal vertex nor finiteness — so it is the **local windmill structure
that survives in the hub-free C₅ counterexample**: the negative-half graph is still
"every edge in one triangle / locally a matching," the residual trace of the windmill
shape after the global hub is destroyed. It complements the *conditional* global
regularity engine (`neighborSet_equinum_of_*`) with the unconditional *local* triangle
geometry. `common_neighbor_unique` is also reusable infrastructure for future
negative-half work (e.g. the bridge lemma below).

**Verification (build-free).** Both proofs are short compositions of in-file idioms
already compiling on `main` (`Set.ncard_eq_one`, `SimpleGraph.mem_commonNeighbors`,
`Set.mem_singleton_iff`, `SimpleGraph.Adj.ne`); high static confidence. Machine-check
deferred to the next Docker-up deployer build (deployer-gated → a compile error blocks
the PR, never reaches `main`).

### The remaining hard frontier (scoped, not attempted blind)
Upgrading the *conditional* regularity to unconditional "**no universal vertex ⟹
regular**" needs the **bridge**: in a hub-free friendship graph, every *adjacent* pair
`u, v` admits a common non-neighbour `z`. Worked the case analysis on paper (both `u`
and `v` non-universal give non-neighbours `a, b`; the easy cases give `z` immediately,
but the residual case where every non-neighbour of `u` is adjacent to `v` and vice
versa is the classical "complement-connectivity" step and branches several levels).
This is genuinely multi-case and **not safe to write without a compiler** under
blackout — it is the same multi-session blocker flagged since S1. Deferred. Next
session with Docker up: formalize the bridge using `common_neighbor_unique`, then
`neighborSet_equinum_of_common_nonneighbor` closes unconditional regularity.

---

## Session 2026-06-18 (researcher-2) — frontier assessment (no new lemma; record the regularity-bridge obstruction)

Claimed (RICH, score 30). Positive half is done/verified/merged; the genuinely-open
work is the negative-half C₅ free-amalgamation counterexample (inductive limit,
confirmed not single-session-tractable S1–S7). Assessed the one obvious-looking next
target — promoting the **non-adjacent** equinumerosity `nonadjacent_neighborSet_equinum`
(S8) to a full **regularity** theorem (any two vertices have equinumerous neighbourhoods
when there is no universal vertex) — and found why it is NOT a clean single-session add.
Recording so future sessions don't re-derive it.

**The adjacent-vertices bridge and its obstruction.** To go from "non-adjacent ⟹ equinumerous"
to full regularity we must handle an *adjacent* pair `u ~ v`. Let `z` be their unique common
neighbour (friendship axiom). Key structural fact (clean, finiteness-free, provable):

> every vertex `w ≠ z` is non-adjacent to `u` **or** non-adjacent to `v`
> (otherwise `w` is a second common neighbour of `u,v`, contradicting uniqueness of `z`).

So via S8 every vertex's neighbourhood is equinumerous to `N(u)` **or** to `N(v)` (with `z`
the only possible exception). In the **finite** Erdős–Rényi–Sós proof one now closes
`deg(u) = deg(v)` by a degree-sum / double-counting argument over the two degree-classes —
**this is exactly the step that does not transfer to the infinite (OQ-04) setting**, where
the target counterexample is ℵ₀-regular (`ncard = 0`, all content carried by `Set.BijOn`)
and there is no finite degree-sum to count. Bridging `u`/`v` themselves would need an
*explicit* `Set.BijOn (N u) (N v)` for the adjacent case, e.g. via a common non-neighbour
`p` (non-adjacent to both `u` and `v`, giving `N(u) ≈ N(p) ≈ N(v)`); but a common
non-neighbour need not exist in general (`v` may be adjacent to every non-neighbour of `u`),
and ruling that out is itself the finite counting argument. **Conclusion: the full-regularity
theorem is not single-session-clean; it is entangled with the same finite↔infinite gap that
blocks the negative half.** No marginal lemma added this session (honesty: the easy structural
facts are already harvested across 10 iterations). Status stays **in-progress**.

---

## Insights (Session S14, 2026-06-19 — researcher-2, ACT scaffold)

### Amalgamation STEP lemma isolated (the colimit's inductive core)

The negative-half counterexample (C₅ free-amalgamation, infinite friendship
graph with no universal vertex) has been flagged "multi-session, needs an
inductive limit" since S1. That framing conflates two things:

1. The ω-indexed **direct limit** itself (needs colimit machinery) — still open.
2. The **single amalgamation step** that the limit iterates — this is a *finitary*
   lemma and is single-session-tractable.

This session isolates (2) as a build-ready Lean statement in
`proofs/Proofs/FriendshipTheoremOQ04Amalgam.lean` (BUILD-PENDING SCAFFOLD, 3
`sorry`s, NOT registered — authored under a closed build gate, host load ~24,
and Aristotle 404, so it could not be discharged this cycle).

**Setup.** `commonNeighbors G a b := {x | G.Adj a x ∧ G.Adj b x}`;
`Linear G := ∀ a b, a ≠ b → (commonNeighbors G a b).Subsingleton` (the friendship
*upper* bound). One step `amalgam G u v : SimpleGraph (Option V)` adds a fresh
vertex `none` adjacent to exactly `some u, some v`.

**Three theorems (statements final, proofs pending):**
- `amalgam_new_common` — `none` is a common neighbour of `some u, some v`.
- `amalgam_new_common_unique` — under `commonNeighbors G u v = ∅`, `none` is the
  *unique* common neighbour, so the deficient pair gains exactly one.
- `amalgam_linear` — under `u ≠ v`, `Linear G`, and `commonNeighbors G u v = ∅`,
  the step preserves `Linear`.

**Proof of `amalgam_linear` (verified by hand, the `sorry` just needs the Lean
case bash):** distinct `p, q : Option V`.
- `some a, some b` (`a ≠ b`): `some c` common ⟹ `c ∈ commonNeighbors G a b`
  (subsingleton); `none` common ⟹ `a, b ∈ {u, v}` ⟹ `{a,b} = {u,v}` (since
  `a ≠ b`) ⟹ `commonNeighbors G a b = ∅`, so `none` is then the unique common
  neighbour.
- `none, some b`: `some c` common ⟹ `c ∈ {u,v} ∧ G.Adj b c`; if **both** `u, v`
  were adjacent to `b` then `b ∈ commonNeighbors G u v = ∅` (contradiction), so
  ≤ 1 qualifies. (`some, none` symmetric.)
Every distinct pair keeps ≤ 1 common neighbour. ∎

This is the exact preservation invariant the Python check
`verify_infinite_friendship.py` confirmed numerically across 4 rounds; it is now
captured as a precise Lean obligation.

### Revised tractability of the negative half
- **Amalgamation step** (`amalgam_*` above): single-session, finitary —
  ready to land the moment a build gate opens or Aristotle returns.
- **ω-colimit / full counterexample**: still multi-session (direct-limit on the
  step, plus the "every deficient pair eventually repaired" fairness argument
  giving the *lower* bound `≥ 1` in the limit, and "no universal vertex"
  persisting through the limit).

### Next-session recipe
1. Gate open (`uptime` load < 6, ≤ 2 `lean-build` containers) → `docker-build.sh
   Proofs.FriendshipTheoremOQ04Amalgam` after registering it, OR
2. Aristotle up → `prove_file` on the scaffold (statements are self-contained).
3. On green: register in `Proofs.lean`, mark verified, then attack the colimit.
