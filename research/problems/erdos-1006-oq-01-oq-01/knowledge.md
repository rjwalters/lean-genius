# Knowledge Base: erdos-1006-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: prove `cover_graph_characterization` (Pretzel-Brightwell 1985) without
axioms — a finite graph admits a robustly acyclic orientation iff it is a cover
graph (Hasse diagram) of some poset. File: `proofs/Proofs/Erdos1006OQ01.lean`.

---

## Insights

- **The goal is achieved (merged PR #27222).** `cover_graph_characterization`
  is a proved `theorem`, 0 sorry.
- **Winning construction — the reachability order.** For a robust orientation
  `O`, take `reachOrder`: `a ≤ b` iff `Relation.ReflTransGen O.arc a b`.
  Acyclicity (a strictly-monotone `rank : V → ℕ`) gives antisymmetry, so this is
  a `PartialOrder`. Then `G` is exactly its cover graph:
  - `a < b ↔ TransGen O.arc a b` (proved from the rank witness).
  - Each edge is a covering pair precisely because "no dependent arc" means
    there is no alternate directed path — an intermediate `w` with `u < w < v`
    would give a dependent arc, contradicting `hNoDep`.
- **Key helper lemmas** (reusable for any acyclic-orientation reasoning):
  - `rank_le_of_rtg` / `rank_lt_of_tg`: rank is weakly/strictly monotone along
    `ReflTransGen`/`TransGen` paths.
  - `lift_below` / `lift_above`: a path whose ranks stay strictly below `rank v`
    (resp. strictly above `rank u`) never uses the arc `(u,v)`, so it lifts to a
    path in the arc relation with `(u,v)` excluded. These bridge "path in `O`"
    and "path avoiding the reversed arc" for the dependent-arc definition.
- **The `hasDependentArc` reachability definition (S3, PR #27154)** is what made
  the whole thing tractable: `∃ u v, O.arc u v ∧ TransGen (fun a b => O.arc a b ∧
  (a,b) ≠ (u,v)) u v`. It replaced a backwards rank inequality that was
  vacuously false and collapsed `isRobustlyAcyclic ≡ isAcyclic`.

---

## Dead Ends

- **Rank-`<` fix for `hasDependentArc`** (S2): sound, but forces a
  Szpilrajn / linear-extension construction for `cover_graph_admits_robust`.
  Superseded by the reachability definition, which makes the robustness
  obligations elementary `TransGen` inductions.
- **The two remaining axioms are NOT tractable de-axiomatization targets:**
  `chromatic_lt_girth_implies_robust` (Fisher-FLW 1997) and
  `nesetril_rodl_counterexample` (Nesetril-Rodl 1978) each need 1000+ lines of
  probabilistic / explicit extremal-graph machinery absent from Mathlib. They
  are out of scope for the `cover_graph_characterization` problem.

## Soundness fix (this session)

- **`nesetril_rodl_counterexample` was UNSOUND as originally stated.** Its
  hypothesis phrased "girth ≥ g" as *"every closed walk has length 0 or ≥ g"*.
  But any edge `u ~ v` gives the length-2 closed walk `u → v → u`, so for `g ≥ 3`
  that condition forces the graph to be **edgeless** — and edgeless graphs admit
  a robustly acyclic orientation. So no graph satisfied both the walk-girth
  hypothesis and `¬admitsRobust`: the axiom asserted a *false existential*
  (an inconsistent assumption, like the earlier `bringRadical_not_in_radicals`
  removal, #35878).
- **Fix (VERIFIED, this session):**
  - proved `edgeless_admits_robust` — any graph with no edges admits a robust
    orientation (generalises `empty_graph_robust` from `⊥`);
  - proved `closedWalk_girth_formulation_unsound` — the closed-walk phrasing has
    NO witness (case split: edgeless ⇒ robust; else a length-2 backtrack breaks
    the walk bound). Documents *why* the old axiom was unsound;
  - re-stated BOTH axioms using `SimpleGraph.egirth` (length of shortest
    **cycle**, `⊤` if acyclic) — the correct girth invariant. The corrected
    `nesetril_rodl_counterexample` is genuinely true & deep (high girth + high
    chromatic number), so it stays axiomatized. `triangle_not_robust` still
    discharges its `g = 3` base case (`K₃` has `egirth = 3`).
- **Takeaway:** closed-walk length is the WRONG proxy for girth in Lean — it
  counts backtracking. Use `egirth`/`girth` (cycles) for "no short cycles".

## Session 2026-07-10 (researcher-1) — BUILD REPAIR: induction motive-mismatch (Mathlib drift)

Entry marked phase=COMPLETED (last session claimed VERIFIED via docker). Verifying
`Erdos1006OQ01.lean` (692 L, Mathlib-only, 2 egirth axioms) via lean-elab
([[reference-docker-down-lean-elab-verification-path]]) found it **does NOT build** vs the
current pin: `admitsRobust_mono` line 570 `error: Type mismatch when assigning motive`.

ROOT CAUSE: the "no dependent arc" bullet lifts a `Relation.TransGen (restricted arc) u v`
path to the `O`-arc TransGen via `induction hpath with | single | tail`. Mathlib's `induction`
motive-generalization heuristics drifted — with `harc : O.arc u v` (the fixed endpoint `v`) in
context, the auto-computed motive `fun v hpath => O.arc u v → H.Adj u v → …` no longer
typechecks (the restricted-arc struct fields leak into the motive as antecedents).

FIX (drift-proof): replace the whole `induction` with `Relation.TransGen.mono` — a per-arc
map is exactly what's needed: `exact hpath.mono (fun a b hr => ⟨hr.1.1, hr.2⟩)`
(`Relation.TransGen.mono (h : ∀ a b, r a b → p a b) : TransGen r a b → TransGen p a b`).
Whole file re-elaborated: EXIT 0, 0 errors/warnings.

★LESSON: `induction` on `Relation.TransGen` (or any indexed relation) with the endpoint fixed
in a sibling hypothesis is FRAGILE across Mathlib `induction`-heuristic changes → prefer
`Relation.TransGen.mono` / `.head_induction_on` for path-lifting/mapping. Fifth
verification-found breakage this session. (Research json sorryCount=1 is a docstring FP —
"no sorry" — file is genuinely 0-sorry.)
