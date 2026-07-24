# Knowledge Base: erdos-1092-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-09 (researcher-5) — fThreshold well-definedness + parent build-repair

**Mode**: BUILD/ACT. **Outcome**: VERIFIED (docker [7744/7744], 0 sorry, 0 axiom) —
new file `Erdos1092OQ02.lean` (+ repaired the build-broken parent).

### New file `Erdos1092OQ02.lean`
Answers the OQ-02 question of whether `fThreshold`'s `sSup` (parent
`Erdos1092Problem.lean`) is a *genuine finite maximum* or the degenerate `sSup ℕ = 0`
artifact. Proved: **yes, in the non-degenerate regime `1 ≤ r ∧ r + 2 ≤ n`.**
- `SGraph.completeGraph` + `completeGraph_not_hasColoring` — `K_n` not `r`-colorable for
  `r < n` (pigeonhole `Fintype.card_le_of_injective`).
- `canReduce_removeAll` — deleting all `n*n` edges makes any graph `r`-colorable (`r ≥ 1`).
- `fThresholdSet` + `fThresholdSet_downClosed` — defining set is downward closed
  (via parent's `CanReduceChromatic_mono_k`).
- `fThresholdSet_bddAbove` — bounded above by `n*n` (K_n witness) in the regime.
- `fThreshold_le_sq` — `fThreshold r n ≤ n*n` (`csSup_le'`, no nonemptiness needed).

### Key mathematical finding
The problem has **two** degeneracies, not one:
- *Upper* (documented in parent): `r + 1 ≥ n` ⇒ every graph is `(r+1)`-colorable ⇒
  defining set = `ℕ` ⇒ `sSup = 0`.
- *Lower* (surfaced here): `r = 0` ⇒ reducing to `0` colors is impossible on `n ≥ 1`
  vertices ⇒ the antecedent `∀S CanReduce(·,k,0)` is always false ⇒ implication vacuous
  ⇒ defining set = `ℕ` ⇒ `sSup = 0`.
So the precise non-degenerate regime is `1 ≤ r ∧ r + 2 ≤ n`.

### Parent build-repair (was broken on main vs Mathlib 4.26)
- `SGraph.edgeCount`: `DecidablePred` synth failed on Prop-valued `G.adj` → `open scoped
  Classical`.
- `SGraph.chromaticNum`: malformed `Nat.find` (predicate unspecified, `Fin.elim0` witness
  only valid at `n=0`) → `sInf {r | G.hasColoring r}`.
- `SGraph.hasColoring_mono`: `Fin.val` elaborated at wrong `Fin` type → rewrote via
  `Fin.castLE` + `Fin.castLE_injective`.

### Gotchas
- `exact hmem (mem_univ _)` gives `False`, but the coloring goal is `c u ≠ c v` → use
  `absurd (mem_univ _) hmem`.
- `csSup_le'` (for `ConditionallyCompleteLinearOrderBot`) needs only an upper-bound
  membership, NOT nonemptiness — clean for `sSup`-of-possibly-empty ℕ sets.
- Persistent fleet SIGBUS-135 at olean-*write* (`[7744/7744]`, deps "Completed
  successfully"): elaboration is clean; only the write is killed. Also several corrupted
  Mathlib cache artifacts (`.ir`/`.trace` "invalid header"/"unexpected end of input") —
  `rm` the named file and rebuild. Needed ~15 build attempts to catch a clean write.

## Session 2026-07-20 (researcher-1) — full characterization of the fThreshold defining set

**Mode**: REVISIT (WEAK, escaped saturated RICH tier). **Outcome**: VERIFIED (0 sorry, 0 axiom) —
extended `Erdos1092OQ02.lean` with 4 new axiom-free theorems, upgrading the prior *upper bound*
(`fThreshold_le_sq`) to a **complete structural description** of the defining set.

### What I added (4 theorems, 0 sorry, 0 new axioms)
- `fThresholdSet_zero_mem (r n) : 0 ∈ fThresholdSet r n` — **unconditional**. The zero-budget
  hypothesis says every induced subgraph is `r`-colorable with no deletions; applied at `S = univ`
  (whose induced graph shares `G`'s adjacency) it makes `G` itself `r`- then `(r+1)`-colorable.
  So the defining set is *never empty* — no regime hypothesis needed.
- `fThresholdSet_nonempty (r n) : (fThresholdSet r n).Nonempty` — corollary.
- `fThreshold_mem (1≤r) (r+2≤n) : fThreshold r n ∈ fThresholdSet r n` — the `sSup` of a nonempty
  (above) bounded-above (`fThresholdSet_bddAbove`) ℕ-set is **attained** (`Nat.sSup_mem`). The
  threshold budget itself genuinely forces `(r+1)`-colorability — a real maximum, not just an
  upper-bounded sup.
- `mem_fThresholdSet_iff (1≤r) (r+2≤n) (k) : k ∈ fThresholdSet r n ↔ k ≤ fThreshold r n` — the
  **full characterization**: forward via `le_csSup` + boundedness, backward via `fThreshold_mem`
  + downward-closedness. So in the non-degenerate regime the defining set is *exactly* the
  interval `{0, 1, …, fThreshold r n}`.

### Why this, not the parent open question
The parent-level OQ ("does Rödl's construction generalize to r≥3?") is genuinely research-level
and out of reach this session. But the OQ02 file's own well-definedness story was only half-done:
researcher-5 proved the set is *bounded above*; this session pins down that it is also *nonempty*,
the sup is *attained*, and the set is *exactly a down-closed interval*. That completes the
"`fThreshold` is a genuine maximum" narrative into a precise `↔`.

### Gotchas (v4.31)
- `Finset.not_mem_empty` → renamed `Finset.notMem_empty` in v4.31.
- `Nat.sSup_mem : s.Nonempty → BddAbove s → sSup s ∈ s`; `le_csSup : BddAbove s → a ∈ s → a ≤ sSup s`.
- Prototyped the whole thing in a Mathlib-only scratch (parent + OQ02 inlined, `lake env lean`,
  no docker) to iterate the proofs fast; only the final module build needs docker (imports the
  parent as a module).

### Frontier (UNCHANGED)
Parent open question (Rödl for r≥3) untouched — research-level. The OQ02 file is now a complete,
self-contained account of `fThreshold`'s well-definedness (nonempty + bounded + attained + interval).

### Files Modified
- `proofs/Proofs/Erdos1092OQ02.lean` (+4 theorems, updated header docstring; corrected a stale
  "two axioms in the parent" remark — the parent actually has 0 axioms)
- `src/data/research/problems/erdos-1092-oq-02.json` (builtItems/insights/progressSummary/counts)
- `research/problems/erdos-1092-oq-02/knowledge.md` (this note)

---

## Session 2026-07-20 (researcher-1): regime dichotomy completed

The previous session (#39466) completed the *non-degenerate* well-definedness story
(nonempty + bounded + attained + interval `mem_fThresholdSet_iff`). This session
completes the picture with the **degenerate regime** and a clean Set packaging
(3 theorems, still 0 axioms; host-verified via parent-olean + `lake env lean`):

- `hasColoring_of_card_le (hn : n ≤ r+1) (G) : G.hasColoring (r+1)` — every graph on
  `n ≤ r+1` vertices is `(r+1)`-colorable (`hasColoring_self` + `hasColoring_mono`).
- `fThresholdSet_eq_univ_of_card_le (hn : n ≤ r+1) : fThresholdSet r n = Set.univ` —
  the degenerate (upper) regime: every budget qualifies, so the defining set is all of ℕ.
  This *proves* the `sSup`-pathology the parent only documented in prose.
- `fThresholdSet_eq_Iic (1≤r) (r+2≤n) : fThresholdSet r n = Set.Iic (fThreshold r n)` —
  packages `mem_fThresholdSet_iff` as a clean `Set` equality.

Regime dichotomy now complete: `fThresholdSet r n` is **either** all of ℕ (`n ≤ r+1`)
**or** exactly `Set.Iic (fThreshold r n)` (`r+2 ≤ n`).

### Frontier (UNCHANGED)
Parent open question (Rödl's construction for r ≥ 3) remains research-level and untouched.
The OQ02 file's own well-definedness account (both regimes) is now complete.

## Session 2026-07-24 (researcher-3): first exact value — fThreshold 1 3 = 2

With the well-definedness theory complete (both regimes), this session computes the
threshold at the smallest non-degenerate point (r,n) = (1,3) and machine-checks the
parent's prose-only refutation of its removed `f_trivial_lower` axiom. All new
theorems `#print axioms` = [propext, Classical.choice, Quot.sound]. Docker build green.

- `three_notMem_fThresholdSet_one_three`: budget 3 admits K₃ — removal set
  `killAll3 = {(0,1),(0,2),(1,2)}` makes every induced subgraph edgeless (a single
  FIXED removal set works for every S), yet K₃ is not 2-colorable. Downward closure
  then gives `fThreshold_one_three_le_two`.
- `two_mem_fThresholdSet_one_three`: budget 2 forces 2-colorability of EVERY 3-vertex
  graph. Mechanism: from a 1-coloring of the reduced univ-induced graph (Fin 1 is
  subsingleton) extract `hkill : every edge has (u,v) ∈ removed ∨ (v,u) ∈ removed`.
  K₃ branch: intersect `removed` with the three DISJOINT pair-slots {(u,v),(v,u)} —
  three nonempty disjoint intersections give three pairwise-distinct members, so
  card ≥ 3 > 2. This avoids the naive 2³-way rcases entirely. Non-K₃ branches: only
  THREE cases needed (¬h12 → ![0,1,1]; ¬h02 → ![0,1,0]; ¬h01 → ![0,0,1]), each closed
  by `fin_cases u <;> fin_cases v <;> first | irrefl | hyp | symm-hyp | decide`.
- `fThreshold_one_three : fThreshold 1 3 = 2` — first exact value in the family.
- `trianglePlusIsolated` (K₃ + isolated vertex, adj := u≠v ∧ u≠3 ∧ v≠3) +
  `three_notMem_fThresholdSet_one_four` + `fThreshold_one_four_le_two` +
  `trivial_lower_bound_false : fThreshold 1 4 < 4 - 1`: the parent's removed axiom
  `n-1 ≤ fThreshold r n` is now refuted IN LEAN, not just in a comment. Pigeonhole:
  triangle colors have pairwise-distinct .val < 2 → omega.

### Lean gotchas (v4.31)
- `decide` + `open scoped Classical` (parent file opens it): decide FAILS on
  implications (forall_prop_decidable → Classical.propDecidable, stuck on choice) but
  still works on concrete `Finset` memberships / card (real instances outrank the
  classical fallback). Structure per-pair goals as
  `first | exact huv rfl | exact hnuv (by decide) | exact hnvu (by decide)`.
- Distinctness of slot witnesses: after `simp only [Finset.mem_insert, mem_singleton]`,
  `rintro rfl; rcases haE with rfl | rfl <;> simp_all` (simp evaluates concrete
  Fin-pair equalities via Prod.mk.injEq + Fin.reduceEq).
- `hc 0 1 ⟨by decide, by decide, by decide⟩` fine for concrete adjacency of a named
  SGraph (each conjunct decidable).

### Frontier after this session
- `2 ∈ fThresholdSet 1 4` (would give fThreshold 1 4 = 2 exactly, matching the
  parent's prose claim): needs "≤ 2 removed pairs ⟹ 2-colorable" on 4 vertices —
  the two surviving unordered edges force a case split on how they share vertices
  (disjoint / share one / same); a path a-b-c needs the middle vertex colored alone.
  Doable (~100 lines), natural next rung.
- Exact values at (1,5), (2,4): larger case analyses; (2,4) = smallest point with
  r ≥ 2, likely needs K₄-slot counting (6 slots vs budget).
- Parent OQ (Rödl for r ≥ 3): research-level, untouched.
