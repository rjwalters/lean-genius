/-
Erdős Problem #816 — structural facts the parent left unproven (OQ-01)

Parent entry `erdos-816` ("Equal-Degree Vertices and Paths of Length 3") states the
Chen–Ma theorem as an axiom and leaves two supporting structural facts as prose:

* **Part V** — *why* the complete bipartite graph `K_{n,n+1}` is the extremal
  counterexample at the `n² + n` edge threshold (it has no equal-degree pair joined
  by a path of length 3), and
* **Part VII** — the degree *pigeonhole* guaranteeing equal-degree pairs exist at all.

This file proves both, axiom-free, on top of the parent's own definitions.

The counterexample mechanism is a clean parity argument: in a bipartite graph a path
of length 3 (an odd path) joins vertices in *opposite* parts, so if the two parts have
distinct degrees, an equal-degree pair must lie in the same part and therefore cannot
be joined by such a path.  This is exactly why `K_{n,n+1}` — bipartite with part
degrees `n+1` and `n` — escapes the property, pinning the threshold.

Main results:
* `hasPath3_opposite_color` — a length-3 path in a bipartite graph joins opposite parts.
* `no_equalDegreePath3_of_bipartition` / `_of_distinctDegrees` — bipartite graphs whose
  parts have distinct degrees have **no** equal-degree path-3 pair (the counterexample).
* `exists_sameDegree_pair` — the degree pigeonhole: any graph on `≥ 2` vertices has two
  distinct vertices of equal degree (so equal-degree pairs always exist).
-/

import Mathlib

namespace Erdos816OQ01

open SimpleGraph

variable {V : Type*}

/-!
## Parent definitions (inlined)

The parent file `Erdos816Problem.lean` does not compile under Lean/Mathlib v4.26.0
(orphan docstrings and a `satisfiesEH816` instance mismatch), so we reproduce the
handful of definitions we need here, keeping this file self-contained and axiom-free.
-/

/-- A path of length 3: four distinct vertices `u - a - b - v` with consecutive
adjacencies. -/
def hasPath3 (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ a b : V, u ≠ a ∧ a ≠ b ∧ b ≠ v ∧
    u ≠ b ∧ a ≠ v ∧ u ≠ v ∧
    G.Adj u a ∧ G.Adj a b ∧ G.Adj b v

/-- Two vertices have the same degree. -/
def sameDegree (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (u v : V) : Prop :=
  G.degree u = G.degree v

/-- `G` has an equal-degree pair joined by a path of length 3. -/
def hasEqualDegreePath3Pair (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∃ u v : V, u ≠ v ∧ sameDegree G u v ∧ hasPath3 G u v

/-- A proper 2-coloring (bipartition) of `G`: adjacent vertices receive opposite colors. -/
def IsBipartition (G : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y

/-- **Parity of length-3 paths.** In a bipartite graph, a path of length 3 joins two
vertices of *opposite* colour: the three edges flip the Boolean colour three times. -/
theorem hasPath3_opposite_color {G : SimpleGraph V} {c : V → Bool}
    (hc : IsBipartition G c) {u v : V} (h : hasPath3 G u v) : c u ≠ c v := by
  obtain ⟨a, b, _, _, _, _, _, _, hua, hab, hbv⟩ := h
  have h1 := hc hua
  have h2 := hc hab
  have h3 := hc hbv
  revert h1 h2 h3
  cases c u <;> cases c a <;> cases c b <;> cases c v <;> simp

/-- **The counterexample mechanism (general form).** If `G` is bipartite via `c` and
every equal-degree pair shares a colour, then `G` has no equal-degree pair joined by a
path of length 3. -/
theorem no_equalDegreePath3_of_bipartition {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {c : V → Bool}
    (hc : IsBipartition G c) (hdeg : ∀ u v, sameDegree G u v → c u = c v) :
    ¬ hasEqualDegreePath3Pair G := by
  rintro ⟨u, v, _, hsame, hpath⟩
  exact hasPath3_opposite_color hc hpath (hdeg u v hsame)

/-- **The counterexample mechanism (vertices of different colour have unequal degree).**
If `G` is bipartite via `c` and any two vertices of opposite colour have different
degrees, then `G` has no equal-degree pair joined by a path of length 3. -/
theorem no_equalDegreePath3_of_distinctDegrees {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {c : V → Bool} (hc : IsBipartition G c)
    (hdist : ∀ u v, c u ≠ c v → G.degree u ≠ G.degree v) :
    ¬ hasEqualDegreePath3Pair G := by
  refine no_equalDegreePath3_of_bipartition hc (fun u v hsame => ?_)
  unfold sameDegree at hsame
  exact not_not.mp (fun h => hdist u v h hsame)

/-- **The counterexample mechanism (distinct part degrees).** If `G` is bipartite via
`c`, every colour-`false` vertex has degree `d₀`, every colour-`true` vertex has degree
`d₁`, and `d₀ ≠ d₁`, then `G` has no equal-degree pair joined by a path of length 3.
This is precisely the situation of `K_{n,n+1}` (part degrees `n+1 ≠ n`). -/
theorem no_equalDegreePath3_of_partDegrees {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {c : V → Bool}
    (hc : IsBipartition G c) {d₀ d₁ : ℕ} (hne : d₀ ≠ d₁)
    (h0 : ∀ v, c v = false → G.degree v = d₀)
    (h1 : ∀ v, c v = true → G.degree v = d₁) :
    ¬ hasEqualDegreePath3Pair G := by
  refine no_equalDegreePath3_of_distinctDegrees hc (fun u v hcuv => ?_)
  rcases Bool.dichotomy (c u) with hu | hu <;> rcases Bool.dichotomy (c v) with hv | hv
  · exact absurd (hu.trans hv.symm) hcuv
  · rw [h0 u hu, h1 v hv]; exact hne
  · rw [h1 u hu, h0 v hv]; exact fun h => hne h.symm
  · exact absurd (hu.trans hv.symm) hcuv

/-- **Degree pigeonhole (Part VII).** Any finite simple graph on at least two vertices
has two distinct vertices of equal degree.  (If all degrees were distinct they would
realize every value `0, …, card-1`, forcing a vertex adjacent to all others to coexist
with an isolated vertex — a contradiction.) -/
theorem exists_sameDegree_pair (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hcard : 2 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ u v, u ≠ v → degree G u ≠ degree G v`, i.e. the degree map is injective.
  have hinj : Function.Injective (fun v => G.degree v) := by
    intro x y hxy
    by_contra hne
    exact hcon x y hne hxy
  -- Package degrees into `Fin (card V)`; injective + equal cardinality ⇒ surjective.
  let f : V → Fin (Fintype.card V) := fun v => ⟨G.degree v, G.degree_lt_card_verts v⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact hinj (by simpa [f, Fin.ext_iff] using hxy)
  have hsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by simp⟩ |>.2
  -- A vertex of full degree `card-1` and an isolated vertex of degree `0` must coexist.
  obtain ⟨w, hw⟩ := hsurj ⟨Fintype.card V - 1, by omega⟩
  obtain ⟨u, hu⟩ := hsurj ⟨0, by omega⟩
  have hdw : G.degree w = Fintype.card V - 1 := by simpa [f] using congrArg Fin.val hw
  have hdu : G.degree u = 0 := by simpa [f] using congrArg Fin.val hu
  have huw : u ≠ w := by
    intro h; rw [h, hdw] at hdu; omega
  -- `w` is adjacent to every other vertex, so to `u`.
  have hsub : G.neighborFinset w ⊆ Finset.univ.erase w := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨fun hxw => ?_, Finset.mem_univ x⟩
    rw [hxw] at hx
    exact (G.notMem_neighborFinset_self w) hx
  have hcardw : (G.neighborFinset w).card = (Finset.univ.erase w).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
    exact hdw
  have heq : G.neighborFinset w = Finset.univ.erase w :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardw.symm)
  have hadj : G.Adj w u := by
    rw [← SimpleGraph.mem_neighborFinset, heq, Finset.mem_erase]
    exact ⟨huw, Finset.mem_univ u⟩
  -- But `u` is isolated: its neighbour finset is empty.
  have hempty : G.neighborFinset u = ∅ := Finset.card_eq_zero.mp hdu
  have hwmem : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hadj.symm
  rw [hempty] at hwmem
  exact (Finset.notMem_empty w) hwmem

end Erdos816OQ01
