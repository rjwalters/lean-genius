# erdos-57-oq-04: Bipartite characterization (odd cycles)

Erdős #57 (Liu–Montgomery 2020) main result is kept as the axiom `erdos_57`
(divergence of reciprocal odd-cycle lengths under infinite chromatic number).
This sub-problem concerns the elementary *bipartite characterization* lemmas in
`proofs/Proofs/Erdos57Problem.lean`:

- `bipartite_iff_no_odd_cycles : G.IsBipartite ↔ oddCycleLengths G = ∅`
- `colorable_two_no_odd_cycles : IsColorable G 2 → oddCycleLengths G = ∅`

## Session 2026-06-15 (Session 1) — FRESH, ACT

**Outcome**: progress (2 sorries → 1)

### What I Did
- Discovered Mathlib provides `SimpleGraph.Coloring.even_length_iff_congr`
  (`Mathlib/Combinatorics/SimpleGraph/ConcreteColorings.lean`): for a `Bool`
  coloring `c`, `Even p.length ↔ (c u ↔ c v)`. For a closed walk (`u = v`) the
  RHS is trivially true, forcing even length.
- Added reusable helper `noOddCycles_of_boolColoring (c : G.Coloring Bool) :
  oddCycleLengths G = ∅`, the parity argument (mirrors Mathlib's
  `Walk.three_le_chromaticNumber_of_odd_loop`).
- Fully proved `colorable_two_no_odd_cycles` (no sorry): build a `Coloring (Fin 2)`
  from the file's `IsColorable` witness via `SimpleGraph.Coloring.mk`, then apply
  the forward direction of the iff.
- Proved the forward direction (`→`) of `bipartite_iff_no_odd_cycles` by
  recoloring `Fin 2 → Bool` with `recolorOfEquiv G finTwoEquiv` and applying the
  helper.

### Key Findings
- `IsBipartite` is `abbrev` for `Colorable 2`; `obtain ⟨c⟩` extracts the
  `Coloring (Fin 2)`.
- The **reverse** direction (no odd cycle ⟹ bipartite) is a genuine Mathlib gap:
  `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` lists exactly
  `IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G` as *future work*. Only
  `IsAcyclic.isBipartite` / `IsTree.isBipartite` exist. For arbitrary (infinite)
  `V` it needs a component-wise distance-parity coloring + choice — substantial,
  build-gated.

### Files Modified
- `proofs/Proofs/Erdos57Problem.lean` (lines ~143–185)

### Next Steps
- Prove the reverse direction: per connected component, pick a base vertex, color
  by parity of `G.dist base v`; properness is exactly the no-odd-cycle hypothesis.
  Mathlib's `IsAcyclic.isBipartite` (Acyclic.lean:511) uses `dist u v % 2` and is
  a strong template. Estimated 200–400 lines; do under live Docker.
- Build-verify under Docker (this session was under a Docker/Aristotle blackout;
  proof is name-checked against pinned Mathlib v4.26 but not compiled).

## Session 2026-06-27 (Session 2) — REVISIT, ACT

**Outcome**: progress (reverse direction of `bipartite_iff_no_odd_cycles` now FULLY
PROVEN; the single remaining `sorry` is reduced to one precise classical walk lemma).
Sorry count unchanged at 1, but its *scope* collapsed from "build a 200–400 line
distance-parity coloring" to a self-contained Mathlib-gap lemma.

### Key discovery (supersedes Session 1's plan)
Mathlib **already provides the coloring construction**. The prior session planned to
hand-build a component-wise distance-parity `Coloring (Fin 2)` (estimated 200–400 lines,
mirroring `IsAcyclic.coloringTwoOfVerts`). That is unnecessary:

- `SimpleGraph.two_colorable_iff_forall_loop_even`
  (`Mathlib/Combinatorics/SimpleGraph/ConcreteColorings.lean:184`):
  `G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), Even w.length`.
  Its reverse direction does exactly the per-connected-component coloring + choice.

Since `IsBipartite` is `abbrev` for `Colorable 2`, the reverse direction of the file's
`bipartite_iff_no_odd_cycles` is now closed by routing through this lemma:
bipartite ⟺ every closed walk even; an odd closed walk would (by the crux below) yield
an odd cycle, contradicting `oddCycleLengths G = ∅`.

NB: the companion `Proofs/Erdos57OddClosedWalk.lean` independently proves
`isBipartite_iff_no_oddClosedWalk` (its own `parityColoring`) and likewise isolates the
exact same crux as the only remaining gap. The parent cannot import the companion
(companion imports parent), so the `two_colorable_iff_forall_loop_even` route keeps the
parent self-contained and non-circular.

### What I did
- Added `exists_odd_cycle_of_odd_closed_walk` (the sole remaining `sorry`):
  `(w : G.Walk u u) → Odd w.length → ∃ x (c : G.Walk x x), c.IsCycle ∧ Odd c.length`.
- Rewrote the reverse direction of `bipartite_iff_no_odd_cycles` to use
  `two_colorable_iff_forall_loop_even.mpr` + the crux. **Offline-verified** the whole
  file compiles with exactly one `sorry` (`LAKE_UNSAFE=1 ./bin/lake env lean ...`,
  EXIT 0, only the crux's `declaration uses 'sorry'` warning).

### The remaining crux (classical, Mathlib TODO)
`exists_odd_cycle_of_odd_closed_walk` — "every odd closed walk contains an odd cycle".
Mathlib lists exactly this characterization as future work
(`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean:63`), and has **no** lemma extracting
an odd cycle from an odd closed walk. Standard proof (induction on `w.length` with a `≤ k`
bound so both split pieces land in the IH):

1. Destruct `w = cons h p` (odd ⇒ length ≥ 1 ⇒ not `nil`), `h : G.Adj u v`, `p : Walk v u`.
2. `cons_isCycle_iff : (cons h p).IsCycle ↔ p.IsPath ∧ s(u,v) ∉ p.edges`.
   - If `p.IsPath ∧ s(u,v) ∉ p.edges`: `w` itself is the odd cycle. Done.
   - Else there is a repeated vertex (¬`p.IsPath`) or a repeated edge (`s(u,v) ∈ p.edges`).
     In either case split the walk at the repeat using `Walk.takeUntil`/`Walk.dropUntil`
     (double-split as in `reachable_deleteEdges_iff_exists_cycle.aux`,
     `Mathlib/.../Connectivity/Connected.lean:748`) into two strictly shorter closed
     walks whose lengths sum to `w.length`; exactly one is odd — recurse on it.
   Strictness needs the inner loop length ≥ 1 and the outer part length ≥ 1; choose the
   repeated vertex so both hold (interior repeat).

Estimated ~80–150 lines of walk/list bookkeeping. **Aristotle was unavailable this
session** (MCP `prove` + smoke-test both 404 on `aristotle.harmonic.fun/api/v1/project`).
Good candidate to resubmit to Aristotle once the endpoint is back, or to finish by hand
under a live build. The lemma is also a clean mathlib4 upstream target.

### Files Modified
- `proofs/Proofs/Erdos57Problem.lean` (added crux lemma; rewrote reverse direction).

### Next Steps
- Prove `exists_odd_cycle_of_odd_closed_walk` (closes the entire problem, 0 sorries, and
  lets the companion derive the full `isBipartite_iff_no_oddCycle`).
