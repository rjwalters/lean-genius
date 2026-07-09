/-
Erdős Problem #761: Dichromatic Number and Chromatic Number

Two questions about graph coloring:
(1) Must a graph with large chromatic number have large dichromatic number?
(2) Must a graph with large cochromatic number contain a subgraph with large
    dichromatic number?

Definitions:
- Cochromatic number ζ(G): minimum colors so each color class induces a
  complete or empty graph.
- Dichromatic number δ(G): minimum k such that in every orientation of G,
  there exists a k-coloring with no monochromatic directed cycle.

Axiom reduction: Rebuilt from prior version (deleted in PR #4955 as dead weight).
Original had 8 axioms and 1 sorry. This version has 2 axioms (the open questions)
with 6 formerly-axiom properties proved (including dichrom_mono via orientation
extension + TransGen monotonicity). The IsAcyclicColoring definition was corrected
from "no monochromatic edge" to "no monochromatic directed cycle" using
Relation.TransGen (Neumann-Lara 1982).

Axioms: 2 (erdos_761_question1, erdos_761_question2 — OPEN conjectures)
Sorries: 0

Status: OPEN
Reference: https://erdosproblems.com/761
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

open SimpleGraph

namespace Erdos761

-- ═══════════════════════════════════════════════════════════════════════
-- CORE DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════

/-- An orientation of an undirected graph assigns a direction to each edge.
    For each edge {u,v}, at least one of dir u v or dir v u holds. -/
structure Orientation {V : Type*} (G : SimpleGraph V) where
  dir : V → V → Prop
  covers : ∀ u v, G.Adj u v → dir u v ∨ dir v u
  consistent : ∀ u v, dir u v → G.Adj u v

/-- Directed edge within a color class: both u and v have color i,
    and there is a directed edge from u to v. -/
def colorClassEdge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) (i : Fin k) (u v : V) : Prop :=
  c u = i ∧ c v = i ∧ O.dir u v

/-- A coloring is acyclic if no color class contains a directed cycle.
    A cycle through v in color class i is a TransGen path from v back to v.

    CORRECTED: Prior version used "no monochromatic directed edge" which is
    strictly stronger. The correct definition per Neumann-Lara (1982) is
    "no monochromatic directed cycle". These are NOT equivalent:
    e.g., a directed 3-cycle K₃ can be 2-colored with no monochromatic
    cycles but necessarily has monochromatic edges. -/
def IsAcyclicColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) : Prop :=
  ∀ (i : Fin k) (v : V), ¬Relation.TransGen (colorClassEdge O c i) v v

/-- An orientation admits an acyclic k-coloring. -/
def HasAcyclicColoring {V : Type*} {G : SimpleGraph V}
    (O : Orientation G) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsAcyclicColoring O c

/-- The dichromatic number δ(G): the minimum k such that every orientation
    of G admits an acyclic k-coloring.

    Declared at `_root_` so the `G.dichromNumber` dot notation resolves
    against the global `SimpleGraph` namespace rather than being shadowed
    by the surrounding `Erdos761` namespace (Iter 7 wrapper). -/
noncomputable def _root_.SimpleGraph.dichromNumber {V : Type*}
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ O : Orientation G, HasAcyclicColoring O k}

/-- A cochromatic coloring: each color class induces either a clique
    (all pairs adjacent) or an independent set (no pairs adjacent). -/
def IsCochromatic {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k, (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
               (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): minimum k for a cochromatic partition.

    Declared at `_root_` so the `G.cochromNumber` dot notation resolves
    against the global `SimpleGraph` namespace rather than being shadowed
    by the surrounding `Erdos761` namespace (Iter 7 wrapper). -/
noncomputable def _root_.SimpleGraph.cochromNumber {V : Type*}
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromatic G c}

-- ═══════════════════════════════════════════════════════════════════════
-- BRIDGE LEMMA: connecting the strong and weak acyclicity conditions
-- ═══════════════════════════════════════════════════════════════════════

/-- If no directed edge connects same-color vertices, then no color class
    has a directed cycle. This bridges the old definition (no monochromatic
    edge) to the correct one (no monochromatic cycle).

    All proofs that establish the strong "no monochromatic edge" condition
    automatically satisfy the correct "no monochromatic cycle" condition. -/
theorem isAcyclicColoring_of_no_mono_edge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k)
    (h : ∀ u v, O.dir u v → c u ≠ c v) :
    IsAcyclicColoring O c := by
  intro i v hcycle
  -- Any TransGen cycle must contain at least one edge.
  -- In the single-step case: colorClassEdge gives O.dir v v, but
  -- O.consistent gives G.Adj v v, contradicting SimpleGraph.loopless.
  -- In the multi-step case: the last edge gives O.dir b v with
  -- c b = i = c v, contradicting h b v (c b ≠ c v).
  cases hcycle with
  | single hr => exact absurd (O.consistent v v hr.2.2) (G.loopless v)
  | tail _ hr => exact absurd (hr.1.trans hr.2.1.symm) (h _ v hr.2.2)

-- ═══════════════════════════════════════════════════════════════════════
-- PROVED PROPERTIES (formerly axioms)
-- ═══════════════════════════════════════════════════════════════════════

section ProvedProperties

variable {V : Type*}

private lemma nat_bddBelow (s : Set ℕ) : BddBelow s :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- [Formerly axiom] δ(G) ≤ |V|: the injective coloring (each vertex a
    unique color) is proper, hence acyclic by the bridge lemma. -/
theorem dichrom_le_chrom [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.dichromNumber ≤ Fintype.card V := by
  apply csInf_le (nat_bddBelow _)
  show ∀ O : Orientation G, HasAcyclicColoring O (Fintype.card V)
  intro O
  let e := Fintype.equivFin V
  refine ⟨e, isAcyclicColoring_of_no_mono_edge O e ?_⟩
  intro u v hdir heq
  exact G.ne_of_adj (O.consistent u v hdir) (e.injective heq)

/-- [Formerly axiom] ζ(G) ≤ |V|: the injective coloring gives singleton
    color classes, which vacuously satisfy the cochromatic condition. -/
theorem cochrom_le_chrom [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.cochromNumber ≤ Fintype.card V := by
  apply csInf_le (nat_bddBelow _)
  show ∃ c : V → Fin (Fintype.card V), IsCochromatic G c
  let e := Fintype.equivFin V
  refine ⟨e, fun i => Or.inl (fun u v hu hv huv => ?_)⟩
  -- Singleton color classes: e u = i and e v = i with u ≠ v
  -- contradicts injectivity of e
  exact absurd (e.injective (hu.trans hv.symm)) huv

/-- δ(G) ≤ k whenever G is k-colorable. Any proper k-coloring has no
    monochromatic edges, hence is acyclic for every orientation by the
    bridge lemma. This is the structural form of the well-known inequality
    δ(G) ≤ χ(G) at the level of `SimpleGraph.Colorable`. -/
theorem dichrom_le_of_colorable (G : SimpleGraph V) {k : ℕ}
    (h : G.Colorable k) :
    G.dichromNumber ≤ k := by
  apply csInf_le (nat_bddBelow _)
  show ∀ O : Orientation G, HasAcyclicColoring O k
  intro O
  obtain ⟨c⟩ := h
  exact ⟨c, isAcyclicColoring_of_no_mono_edge O c
    (fun u v hdir => c.valid (O.consistent u v hdir))⟩

/-- ζ(G) ≤ k whenever G is k-colorable. Each color class of a proper
    k-coloring is an independent set, satisfying the cochromatic condition
    via the `¬G.Adj` branch. This is the structural form of ζ(G) ≤ χ(G). -/
theorem cochrom_le_of_colorable (G : SimpleGraph V) {k : ℕ}
    (h : G.Colorable k) :
    G.cochromNumber ≤ k := by
  apply csInf_le (nat_bddBelow _)
  show ∃ c : V → Fin k, IsCochromatic G c
  obtain ⟨c⟩ := h
  refine ⟨c, fun _ => Or.inr (fun u v hu hv _ hadj => ?_)⟩
  exact c.valid hadj (hu.trans hv.symm)

/-- δ(G) ≤ χ(G) lifted from the ℕ-valued `Colorable n` interface to
    Mathlib's ℕ∞-valued `SimpleGraph.chromaticNumber`.

    Mathlib defines `G.chromaticNumber := ⨅ n ∈ {n | G.Colorable n}, (n : ℕ∞)`.
    `le_iInf₂` reduces the goal to: for every `n` with `G.Colorable n`,
    `(G.dichromNumber : ℕ∞) ≤ (n : ℕ∞)`. That follows by casting the ℕ-valued
    `dichrom_le_of_colorable G hcol : G.dichromNumber ≤ n` to ℕ∞.

    The bound is vacuous when `G.chromaticNumber = ⊤` (e.g. infinite
    graphs of unbounded chromatic number); for finite `V` it agrees with
    the natural inequality δ(G) ≤ χ(G). -/
theorem dichrom_le_chromaticNumber (G : SimpleGraph V) :
    (G.dichromNumber : ℕ∞) ≤ G.chromaticNumber := by
  refine le_iInf₂ fun n hcol => ?_
  exact_mod_cast dichrom_le_of_colorable G hcol

/-- ζ(G) ≤ χ(G) lifted to Mathlib's ℕ∞-valued `SimpleGraph.chromaticNumber`.
    Mirror of `dichrom_le_chromaticNumber` via `cochrom_le_of_colorable`. -/
theorem cochrom_le_chromaticNumber (G : SimpleGraph V) :
    (G.cochromNumber : ℕ∞) ≤ G.chromaticNumber := by
  refine le_iInf₂ fun n hcol => ?_
  exact_mod_cast cochrom_le_of_colorable G hcol

/-- [Formerly sorry] Bipartite graphs have δ(G) ≤ 2.
    Direct corollary of `dichrom_le_of_colorable` at k = 2. -/
theorem bipartite_dichrom_le_two (G : SimpleGraph V)
    (hBip : G.Colorable 2) :
    G.dichromNumber ≤ 2 :=
  dichrom_le_of_colorable G hBip

/-- [Formerly axiom] For every orientation, every proper coloring is acyclic.
    Proof: construct any orientation (using a total order from Fintype.equivFin),
    then the bridge lemma gives acyclicity of any proper coloring. -/
theorem acyclic_orientation_exists [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ O : Orientation G, ∀ (c : V → Fin (Fintype.card V)),
      (∀ u v, G.Adj u v → c u ≠ c v) → IsAcyclicColoring O c := by
  -- Any orientation suffices, since the bridge lemma applies to proper colorings.
  -- We construct one using the total order from Fintype.equivFin.
  classical
  let ι := Fintype.equivFin V
  refine ⟨{
    dir := fun u v => G.Adj u v ∧ (ι u).val < (ι v).val
    covers := by
      intro u v hadj
      have hne : (ι u).val ≠ (ι v).val := by
        intro h; exact absurd (ι.injective (Fin.val_injective h)) (G.ne_of_adj hadj)
      by_cases hlt : (ι u).val < (ι v).val
      · left; exact ⟨hadj, hlt⟩
      · right; exact ⟨hadj.symm, by omega⟩
    consistent := fun u v ⟨hadj, _⟩ => hadj
  }, fun c hc => ?_⟩
  apply isAcyclicColoring_of_no_mono_edge
  intro u v ⟨hadj, _⟩
  exact hc u v hadj

/-- [Formerly axiom] δ(H) ≤ δ(G) when H is a subgraph of G.
    Strategy: any H-orientation extends to a G-orientation; a cycle in an
    H-color-class would be a cycle in the corresponding G-color-class. -/
theorem dichrom_mono [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hSub : ∀ u v, H.Adj u v → G.Adj u v) :
    H.dichromNumber ≤ G.dichromNumber := by
  unfold SimpleGraph.dichromNumber
  apply csInf_le_csInf (nat_bddBelow _)
  · -- G-set nonempty: Fintype.card V works for all G-orientations
    exact ⟨Fintype.card V, fun O => by
      let e := Fintype.equivFin V
      exact ⟨e, isAcyclicColoring_of_no_mono_edge O e fun u v hdir heq =>
        G.ne_of_adj (O.consistent u v hdir) (e.injective heq)⟩⟩
  · -- Inclusion: k acyclic for all G-orientations → acyclic for all H-orientations
    intro k hk O_H
    classical
    -- Extend O_H to a G-orientation: keep H-directions, orient non-H edges by index
    let ι := Fintype.equivFin V
    let O_G : Orientation G :=
      { dir := fun u v =>
          (H.Adj u v ∧ O_H.dir u v) ∨
          (G.Adj u v ∧ ¬H.Adj u v ∧ (ι u).val < (ι v).val)
        covers := fun u v hadj => by
          by_cases hH : H.Adj u v
          · rcases O_H.covers u v hH with h | h
            · exact Or.inl (Or.inl ⟨hH, h⟩)
            · exact Or.inr (Or.inl ⟨hH.symm, h⟩)
          · have hne : (ι u).val ≠ (ι v).val :=
              fun h => absurd (ι.injective (Fin.val_injective h)) (G.ne_of_adj hadj)
            by_cases hlt : (ι u).val < (ι v).val
            · exact Or.inl (Or.inr ⟨hadj, hH, hlt⟩)
            · exact Or.inr (Or.inr ⟨hadj.symm, fun h => hH h.symm, by omega⟩)
        consistent := fun u v hdir => by
          rcases hdir with ⟨_, h⟩ | ⟨h, _, _⟩
          · exact hSub u v (O_H.consistent u v h)
          · exact h }
    -- Get acyclic k-coloring for O_G
    obtain ⟨c, hc⟩ := hk O_G
    -- c is also acyclic for O_H: any H-cycle is a G-cycle via TransGen.mono
    exact ⟨c, fun i v hcycle => hc i v (Relation.TransGen.mono
      (fun a b hab => ⟨hab.1, hab.2.1, Or.inl ⟨O_H.consistent a b hab.2.2, hab.2.2⟩⟩)
      hcycle)⟩

-- ═══════════════════════════════════════════════════════════════════════
-- MONOTONICITY IN THE COLOR COUNT + sInf CHARACTERIZATIONS
-- ═══════════════════════════════════════════════════════════════════════

/-- Relabelling colors along any injection `Fin k ↪ Fin k'` preserves acyclicity.
    A monochromatic cycle for `f ∘ c` at color `i` lives entirely in the single
    `c`-class `f⁻¹(i)` (injectivity pins every vertex of the cycle to one preimage),
    so it would be a monochromatic cycle for `c` — contradicting acyclicity of `c`. -/
theorem hasAcyclicColoring_of_injection {G : SimpleGraph V} {O : Orientation G}
    {k k' : ℕ} (f : Fin k → Fin k') (hf : Function.Injective f)
    (h : HasAcyclicColoring O k) : HasAcyclicColoring O k' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => f (c v), ?_⟩
  intro i v hcycle
  -- The cycle's basepoint fixes the color: f (c v) = i.
  have hi : f (c v) = i := by
    cases hcycle with
    | single h => exact h.1
    | tail _ h => exact h.2.1
  -- Push the cycle down to color `c v` for `c` itself, then invoke acyclicity of `c`.
  exact hc (c v) v (Relation.TransGen.mono
    (fun a b hab => ⟨hf (hab.1.trans hi.symm), hf (hab.2.1.trans hi.symm), hab.2.2⟩) hcycle)

/-- Acyclic colorability only improves with more colors: an acyclic `k`-coloring
    lifts to an acyclic `k'`-coloring whenever `k ≤ k'`. -/
theorem hasAcyclicColoring_mono {G : SimpleGraph V} {O : Orientation G}
    {k k' : ℕ} (hle : k ≤ k') (h : HasAcyclicColoring O k) : HasAcyclicColoring O k' :=
  hasAcyclicColoring_of_injection (Fin.castLE hle) (Fin.castLE_injective hle) h

/-- The defining set of `dichromNumber` is upward closed, so `sInf` obeys a clean
    specification: `δ(G) ≤ k` **iff** every orientation admits an acyclic
    `k`-coloring. This upgrades the one-directional `csInf_le` bounds above into a
    usable characterization (both directions). -/
theorem dichromNumber_le_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} :
    G.dichromNumber ≤ k ↔ ∀ O : Orientation G, HasAcyclicColoring O k := by
  unfold SimpleGraph.dichromNumber
  refine ⟨fun hle O => ?_, fun h => Nat.sInf_le h⟩
  have hne : {k | ∀ O : Orientation G, HasAcyclicColoring O k}.Nonempty :=
    ⟨Fintype.card V, fun O => ⟨Fintype.equivFin V, isAcyclicColoring_of_no_mono_edge O _
      (fun u v hdir heq =>
        G.ne_of_adj (O.consistent u v hdir) ((Fintype.equivFin V).injective heq))⟩⟩
  exact hasAcyclicColoring_mono hle (Nat.sInf_mem hne O)

/-- [Lower bound] For a nonempty vertex set, `δ(G) ≥ 1`: the color count `0`
    is impossible since it would require a coloring into the empty type `Fin 0`. -/
theorem dichromNumber_pos [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : 0 < G.dichromNumber := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  obtain ⟨O, _⟩ := acyclic_orientation_exists G
  obtain ⟨c, _⟩ := (dichromNumber_le_iff G).mp (le_of_eq h0) O
  exact (c (Classical.arbitrary V)).elim0

/-- Relabelling colors along any injection `Fin k ↪ Fin k'` preserves the
    cochromatic condition: each color class of `f ∘ c` is either empty (when the
    color is outside the range of `f`) or equal to a color class of `c`. -/
theorem isCochromatic_of_injection {G : SimpleGraph V} {k k' : ℕ}
    (f : Fin k → Fin k') (hf : Function.Injective f)
    {c : V → Fin k} (hc : IsCochromatic G c) : IsCochromatic G (f ∘ c) := by
  intro i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := hi
    rcases hc j with hclq | hind
    · exact Or.inl fun u v hu hv huv => hclq u v (hf hu) (hf hv) huv
    · exact Or.inr fun u v hu hv huv => hind u v (hf hu) (hf hv) huv
  · exact Or.inl fun u v hu _ _ => (hi ⟨c u, hu⟩).elim

/-- The defining set of `cochromNumber` is upward closed, giving the clean
    characterization: `ζ(G) ≤ k` **iff** a cochromatic `k`-coloring exists. -/
theorem cochromNumber_le_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} :
    G.cochromNumber ≤ k ↔ ∃ c : V → Fin k, IsCochromatic G c := by
  unfold SimpleGraph.cochromNumber
  refine ⟨fun hle => ?_, fun h => Nat.sInf_le h⟩
  have hne : {k | ∃ c : V → Fin k, IsCochromatic G c}.Nonempty :=
    ⟨Fintype.card V, Fintype.equivFin V, fun i => Or.inl fun u v hu hv huv =>
      absurd ((Fintype.equivFin V).injective (hu.trans hv.symm)) huv⟩
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  exact ⟨Fin.castLE hle ∘ c,
    isCochromatic_of_injection (Fin.castLE hle) (Fin.castLE_injective hle) hc⟩

/-- [Lower bound] For a nonempty vertex set, `ζ(G) ≥ 1`: a cochromatic coloring
    into `Fin 0` is impossible. -/
theorem cochromNumber_pos [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : 0 < G.cochromNumber := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  obtain ⟨c, _⟩ := (cochromNumber_le_iff G).mp (le_of_eq h0)
  exact (c (Classical.arbitrary V)).elim0

end ProvedProperties

-- ═══════════════════════════════════════════════════════════════════════
-- OPEN CONJECTURES (2 axioms — the actual open questions)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Erdős Problem #761, Question 1** (Erdős–Neumann-Lara):
    Must a graph with large chromatic number have large dichromatic number?
    For every k, there exists f(k) such that χ(G) ≥ f(k) implies δ(G) ≥ k.

    This is OPEN. -/
axiom erdos_761_question1 :
  ∀ k : ℕ, ∃ f : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Colorable f = false → G.dichromNumber ≥ k

/-- **Erdős Problem #761, Question 2** (Erdős–Gimbel):
    Must a graph with large cochromatic number contain a subgraph
    with large dichromatic number?

    This is OPEN. A positive answer implies Question 1 via a bound
    from Erdős Problem #760. -/
axiom erdos_761_question2 :
  ∀ k : ℕ, ∃ g : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.cochromNumber ≥ g →
      ∃ (S : Finset V), (G.induce (↑S : Set V)).dichromNumber ≥ k

end Erdos761
