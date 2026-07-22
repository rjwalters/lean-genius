# erdos-751-incomplete-01 — session notes

## 2026-07-22 (researcher-1) — sorry elimination + integrity finding

**Problem:** Erdős #751 (cycle lengths in 4-chromatic graphs). `Erdos751Problem.lean`
carried two `sorry`s:
1. A **def-sorry**: `minCycleLengthGap (lengths : Set ℕ) : ℕ := sorry` (Aristotle skips
   definition sorries, so it needed a human).
2. A dependent **theorem-sorry** in `erdos_751`: `minCycleLengthGap (cycleLengths G) ≤ 2`.

**Work done (0 new axioms, host-verified `lake env lean` v4.31, EXIT=0):**
- Gave `minCycleLengthGap` a faithful total definition:
  `sInf {d | ∃ a ∈ S, ∃ b ∈ S, a < b ∧ d = b - a}` — the minimum difference between
  distinct elements, which equals the minimum *consecutive* gap (the closest pair is
  always consecutive). Empty/singleton sets give `sInf ∅ = 0`.
- Added foundational lemma `minCycleLengthGap_le : a ∈ S → b ∈ S → a < b →
  minCycleLengthGap S ≤ b - a` via `Nat.sInf_le`.
- Discharged the `hgap_bound` sorry: from two distinct close cycle lengths
  `m, m'` with `|m − m'| ≤ 2`, `minCycleLengthGap_le` + `omega` give `≤ 2`.
- Added `import Mathlib.Order.Lattice.Nat` (for `Nat.sInf`/`Nat.sInf_le`).

Both file sorries are now gone; gallery meta updated (`sorries` 2→0, `theoremCount`
6→7, `lineCount`, imports, `status` → `axiomatized`, `badge` → `axiom`).

## Integrity finding (for auditor / mechanic)

The pre-existing axiom
`four_chromatic_minDeg (G) : chromaticNumber G = 4 → minDegree G ≥ 3`
is **FALSE as literally stated**. Counterexample: take `K₄` and attach a pendant
vertex (degree 1) to one of its vertices. The graph is still 4-chromatic (contains
`K₄`) but its minimum degree is 1, not ≥ 3. The correct classical fact is that a
4-chromatic graph has a *subgraph* (its 3-core / degeneracy witness) of minimum
degree ≥ 3 — a global min-degree bound does not hold. The headline `erdos_751`
theorem is nonetheless **true**, but it is currently derived through this unsound
axiom. A faithful restatement would either (a) weaken the axiom to
`∃ H ≤ G, minDegree H ≥ 3` and feed Bondy–Vince on `H`, or (b) route through the
degeneracy/3-core, neither of which has ready Mathlib API.

## Open (blocked)

- `bondy_vince_theorem` (δ ≥ 3 ⇒ two cycle lengths differ by ≤ 2) — deep 1998
  result, no Mathlib cycle-length-spectrum API. Left as an axiom.

## 2026-07-22 (researcher-1, session 2) — AXIOM ELIMINATED: chromatic–degeneracy lemma PROVED (2→1 axioms)

**Integrity finding (second round):** the #41481 repair `four_chromatic_subgraph_minDeg`
(`∃ H ≤ G, minDegree H ≥ 3`, H on the SAME vertex type) was STILL false as stated —
`minDegree` is `Finset.min'` over `Finset.univ`, i.e. over **all** of `V`, so for
`K₄ ⊕ isolated-vertex` every `H ≤ G` keeps the isolated vertex at degree 0. The
axiom was instantiable to `False` (V := Fin 5).

**Fix + proof (0 new axioms, host-verified v4.31, EXIT=0):** restated in sound
induced-subgraph form and **proved it from Mathlib** — the file's axiom count
drops 2 → 1 (only the deep `bondy_vince_theorem` remains):

- `four_chromatic_subgraph_minDeg` (now a THEOREM): `χ(G) = 4 → ∃ s : Finset V,
  s.Nonempty ∧ ∀ v ∈ s, 3 ≤ #(s.filter (G.Adj v ·))`.
- Engine: `exists_min_subset_of_not_colorable` — strong induction
  (`Finset.strongInduction`) extracting a vertex-minimal non-3-colorable subset;
  `colorable_of_erase_colorable` — greedy extension: a vertex with < 3 internal
  neighbours gets a colour from `Fin 3` unused by its ≤ 2 neighbours
  (`used.card < 3 → used ≠ univ → ∃ free colour`).
- `not_colorable_three_of_chromaticNumber_four` (via `Colorable.chromaticNumber_le`
  + `ENat.toNat_le_toNat`), `colorable_of_isEmpty`.
- Bridges: `degree_induce_eq_filter_card` (`Finset.card_bij` on `neighborFinset`),
  `minDegree_induce_ge`, `cycleLengths_induce_subset` (embedding
  `(induceUnivIso G).toEmbedding.comp (G.induceHomOfLE (Set.subset_univ s))` +
  `Walk.map_isCycle_iff_of_injective` + `Walk.length_map`).
- Headline theorems rewired: `#print axioms erdos_751` =
  `[propext, Classical.choice, Erdos751.bondy_vince_theorem, Quot.sound]`.

**Idioms (v4.31):** `G.loopless`/`G.symm` are now `Std.Irrefl`/`Std.Symm`
structure instances, NOT functions — use `G.irrefl : ¬G.Adj v v` and
`Adj.symm`; `induceHomOfLE` takes `G` explicitly (`G.induceHomOfLE h`);
`SimpleGraph.mem_neighborFinset.mpr` fails name resolution — use
`by rw [SimpleGraph.mem_neighborFinset]; exact _`; `(G.induce s).Adj` is defeq
`G.Adj` so `have hadj' : G.Adj a b := hadj` avoids all `induce_adj` rewriting;
`DecidableRel (G.induce ↑s).Adj := fun a b => decidable_of_iff (G.Adj a.1 b.1)
induce_adj.symm`.

## Open (blocked, unchanged)

- `bondy_vince_theorem` — deep 1998 result, no Mathlib cycle-length-spectrum API.
