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
