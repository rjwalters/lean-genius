/-
# Erdős Problem #1092 OQ-02: Well-definedness of the threshold `fThreshold`

The parent entry (`erdos-1092`, `Erdos1092Problem.lean`) defines

  `fThreshold r n = sSup { k | ∀ G : SGraph n,
      (∀ S, CanReduceChromatic (induced S) k r) → G.hasColoring (r+1) }`

using `sSup` over `ℕ`. The parent file *documents* — in prose only — the crucial
caveat that this `sSup` is meaningful **only** when `r + 2 ≤ n`:

  * If `r + 1 ≥ n` then every `n`-vertex graph is already `(r+1)`-colorable
    (`SGraph.hasColoring_self` + monotonicity), so the defining set is **all of `ℕ`**,
    which is unbounded, and `sSup ℕ = 0` in Lean's `ConditionallyCompleteLinearOrderBot`
    — a junk value.
  * The parent's own removed axioms broke precisely because they ignored this.

The open question left implicit there is: **in the good regime `r + 2 ≤ n`, is the
defining set genuinely bounded above, so that `fThreshold` is a real maximum rather than a
`sSup`-of-an-unbounded-set artifact?**

This file answers it **yes**, rigorously and axiom-free:

* `SGraph.completeGraph`   — the complete graph `K_n`.
* `completeGraph_not_hasColoring` — `K_n` is not `r`-colorable when `r < n` (pigeonhole).
* `canReduce_removeAll`   — deleting *every* edge makes any graph `r`-colorable (`r ≥ 1`),
  so the full budget `k = n*n` reduces every induced subgraph.
* `fThresholdSet` + `fThresholdSet_downClosed` — the defining set is downward closed.
* `fThresholdSet_bddAbove` — **the defining set is bounded above by `n*n`** once
  `r + 2 ≤ n` (using `K_n` as the witness graph that fails the conclusion).
* `fThreshold_le_sq` — consequently `fThreshold r n ≤ n * n` in the good regime: the
  `sSup` is a genuine, finite maximum, not the `sSup ℕ = 0` junk value.

It then goes further and pins down the set completely:

* `fThresholdSet_zero_mem` — `0 ∈ fThresholdSet r n` **unconditionally**, so the set is
  never empty (the zero-budget hypothesis already forces `(r+1)`-colorability, via `S = univ`).
* `fThreshold_mem` — in the good regime `fThreshold r n` is *itself* a member of its
  defining set (`Nat.sSup_mem` on a nonempty bounded set): the threshold is an **attained**
  maximum, so the budget `fThreshold r n` genuinely forces `(r+1)`-colorability.
* `mem_fThresholdSet_iff` — the full characterization: in the good regime a budget `k`
  forces the conclusion **iff** `k ≤ fThreshold r n`, i.e. the defining set is exactly the
  interval `{0, …, fThreshold r n}`.

No new axioms; the parent file has 0 axioms and they are untouched (and unused here).
-/

import Mathlib
import Proofs.Erdos1092Problem

namespace Erdos1092OQ02

/-- **The complete graph `K_n`.** Every pair of distinct vertices is adjacent. -/
def SGraph.completeGraph (n : ℕ) : SGraph n where
  adj u v := u ≠ v
  symm _ _ h := h.symm
  irrefl v := by simp

/-- **`K_n` is not `r`-colorable when `r < n`.** A proper coloring of `K_n` must be
injective (distinct vertices are adjacent, hence differently colored); an injection
`Fin n ↪ Fin r` forces `n ≤ r`. -/
theorem completeGraph_not_hasColoring {n r : ℕ} (h : r < n) :
    ¬ (SGraph.completeGraph n).hasColoring r := by
  rintro ⟨c, hc⟩
  -- The coloring is injective on vertices.
  have hinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    exact hc a b hne hab
  -- An injection `Fin n → Fin r` gives `n ≤ r`, contradicting `r < n`.
  have := Fintype.card_le_of_injective c hinj
  simp only [Fintype.card_fin] at this
  omega

/-- **Deleting every edge trivializes the chromatic number.** For any graph `H` on `n`
vertices and any `r ≥ 1`, removing all `n*n` candidate edges leaves the empty graph, which
is `r`-colorable. Hence `H` can have its chromatic number reduced to `≤ r` within the
budget `k = n*n`. -/
theorem canReduce_removeAll {n : ℕ} (H : SGraph n) {r : ℕ} (hr : 1 ≤ r) :
    CanReduceChromatic H (n * n) r := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · -- `|Fin n × Fin n| = n * n`.
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  · -- The reduced graph has no edges (every pair is "removed"), so it is `r`-colorable.
    refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
    rintro u v ⟨_, hmem, _⟩
    exact absurd (Finset.mem_univ _) hmem

/-- The defining set of `fThreshold r n`: budgets `k` for which "every induced subgraph is
`r`-reducible with `≤ k` edge deletions" already forces `(r+1)`-colorability of the whole
graph. This is exactly the set `fThreshold r n = sSup (·)` ranges over. -/
def fThresholdSet (r n : ℕ) : Set ℕ :=
  { k : ℕ | ∀ G : SGraph n,
      (∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ G.adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, G.symm u v h⟩)
          (fun v ⟨_, _, h⟩ => G.irrefl v h)) k r) →
      G.hasColoring (r + 1) }

/-- `fThresholdSet` really is the set `fThreshold` takes its `sSup` over. -/
theorem fThreshold_eq_sSup (r n : ℕ) : fThreshold r n = sSup (fThresholdSet r n) := rfl

/-- **The defining set is downward closed.** If budget `k` already forces the conclusion,
so does any smaller budget `k' ≤ k`: a smaller budget makes the hypothesis *stronger*
(fewer graphs satisfy it), via `CanReduceChromatic_mono_k`. -/
theorem fThresholdSet_downClosed {r n k k' : ℕ} (hk : k' ≤ k)
    (hmem : k ∈ fThresholdSet r n) : k' ∈ fThresholdSet r n := by
  intro G hP'
  -- Upgrade the `k'`-hypothesis to a `k`-hypothesis, then apply `hmem`.
  exact hmem G (fun S => CanReduceChromatic_mono_k _ hk (hP' S))

/-- **The defining set is bounded above by `n*n` in the non-degenerate regime
`1 ≤ r` and `r + 2 ≤ n`.**

Take `K_n` as a witness. With the full budget `k = n*n`, every induced subgraph of `K_n`
is `r`-reducible (`canReduce_removeAll`, which needs `1 ≤ r` — reducing to `0` colors is
impossible on `n ≥ 1` vertices, the *lower* degeneracy of the problem, complementing the
parent file's documented *upper* degeneracy `r + 1 ≥ n`), so `K_n` satisfies the
hypothesis; but `K_n` is *not* `(r+1)`-colorable when `r + 1 < n`
(`completeGraph_not_hasColoring`). Hence `n*n ∉ fThresholdSet`, and by downward-closedness
every element of the set is `< n*n`. -/
theorem fThresholdSet_bddAbove {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    BddAbove (fThresholdSet r n) := by
  -- `n*n` is not in the set: `K_n` witnesses the failure.
  have hnotmem : n * n ∉ fThresholdSet r n := by
    intro hmem
    -- `K_n` satisfies the full-budget hypothesis...
    have hP : ∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph n).adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph n).symm u v h⟩)
          (fun v ⟨_, _, h⟩ => (SGraph.completeGraph n).irrefl v h)) (n * n) r :=
      fun S => canReduce_removeAll _ hr
    -- ...so `hmem` would make `K_n` be `(r+1)`-colorable, which is false.
    exact completeGraph_not_hasColoring (by omega) (hmem (SGraph.completeGraph n) hP)
  -- `n*n` is an upper bound: any element `> n*n` would drag `n*n` into the set.
  refine ⟨n * n, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt   -- `n*n < k`
  exact hnotmem (fThresholdSet_downClosed (le_of_lt hlt) hk)

/-- **`fThreshold` is a genuine, finite maximum in the non-degenerate regime.** For
`1 ≤ r` and `r + 2 ≤ n`, `fThreshold r n ≤ n * n`. This upgrades the parent file's prose
caveat about the `sSup`-pathology into a proved bound: away from *both* degeneracies —
the upper `r + 1 ≥ n` (documented in the parent) and the lower `r = 0` (surfaced here) —
the threshold is a real supremum of a bounded set, not the `sSup ℕ = 0` artifact. -/
theorem fThreshold_le_sq {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThreshold r n ≤ n * n := by
  rw [fThreshold_eq_sSup]
  refine csSup_le' ?_
  -- `n*n` is an upper bound of the defining set (same argument as boundedness).
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hnotmem : n * n ∉ fThresholdSet r n := by
    intro hmem
    have hP : ∀ S : Finset (Fin n), CanReduceChromatic
        (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ (SGraph.completeGraph n).adj u v)
          (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, (SGraph.completeGraph n).symm u v h⟩)
          (fun v ⟨_, _, h⟩ => (SGraph.completeGraph n).irrefl v h)) (n * n) r :=
      fun S => canReduce_removeAll _ hr
    exact completeGraph_not_hasColoring (by omega) (hmem (SGraph.completeGraph n) hP)
  exact hnotmem (fThresholdSet_downClosed (le_of_lt hlt) hk)

/-- **The defining set is nonempty: `0 ∈ fThresholdSet r n` unconditionally.**
The zero-budget hypothesis says every induced subgraph is `r`-colorable with *no* edge
deletions. Applied to `S = univ`, this makes `G` itself `r`-colorable (the induced graph on
`univ` has the same adjacency as `G`), hence `(r+1)`-colorable. Needs no regime hypothesis. -/
theorem fThresholdSet_zero_mem (r n : ℕ) : 0 ∈ fThresholdSet r n := by
  intro G hP
  -- Instantiate the hypothesis at `S = univ`.
  obtain ⟨removed, hcard, c, hc⟩ := hP Finset.univ
  -- A zero budget forces `removed = ∅`.
  rw [Nat.le_zero, Finset.card_eq_zero] at hcard
  subst hcard
  -- `c` is then a proper `r`-coloring of `G`: every `G`-edge is an edge of the reduced
  -- induced-on-`univ` graph, so its endpoints get different colors.
  refine SGraph.hasColoring_mono G (Nat.le_succ r) ⟨c, fun u v hadj heq => ?_⟩
  exact hc u v
    ⟨⟨Finset.mem_univ u, Finset.mem_univ v, hadj⟩,
      Finset.notMem_empty _, Finset.notMem_empty _⟩ heq

/-- The defining set is nonempty. -/
theorem fThresholdSet_nonempty (r n : ℕ) : (fThresholdSet r n).Nonempty :=
  ⟨0, fThresholdSet_zero_mem r n⟩

/-- **The threshold is an attained maximum in the non-degenerate regime.** For `1 ≤ r` and
`r + 2 ≤ n`, `fThreshold r n` is itself a member of its defining set: the `sSup` of a
nonempty (`fThresholdSet_nonempty`), bounded-above (`fThresholdSet_bddAbove`) set of naturals
is attained (`Nat.sSup_mem`). So the budget `fThreshold r n` genuinely forces
`(r+1)`-colorability — the threshold is a real maximum, not merely an upper-bounded `sSup`. -/
theorem fThreshold_mem {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThreshold r n ∈ fThresholdSet r n := by
  rw [fThreshold_eq_sSup]
  exact Nat.sSup_mem (fThresholdSet_nonempty r n) (fThresholdSet_bddAbove hr hn)

/-- **Full structural characterization: the defining set is exactly the interval
`{0, 1, …, fThreshold r n}`.** In the non-degenerate regime a budget `k` forces the
conclusion iff it does not exceed the threshold. Forward: `k ≤ sSup` by `le_csSup` with the
boundedness witness. Backward: `fThreshold r n` itself lies in the set (`fThreshold_mem`) and
the set is downward closed (`fThresholdSet_downClosed`). -/
theorem mem_fThresholdSet_iff {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) (k : ℕ) :
    k ∈ fThresholdSet r n ↔ k ≤ fThreshold r n := by
  constructor
  · intro hk
    rw [fThreshold_eq_sSup]
    exact le_csSup (fThresholdSet_bddAbove hr hn) hk
  · intro hk
    exact fThresholdSet_downClosed hk (fThreshold_mem hr hn)

/-- **The non-degenerate defining set as an interval.** Packaging
`mem_fThresholdSet_iff` as a `Set` equality: for `1 ≤ r`, `r + 2 ≤ n`, the defining set is
exactly `Set.Iic (fThreshold r n) = {0, 1, …, fThreshold r n}`. -/
theorem fThresholdSet_eq_Iic {r n : ℕ} (hr : 1 ≤ r) (hn : r + 2 ≤ n) :
    fThresholdSet r n = Set.Iic (fThreshold r n) := by
  ext k
  rw [Set.mem_Iic]
  exact mem_fThresholdSet_iff hr hn k

/-- Every graph on at most `r + 1` vertices is `(r+1)`-colorable: colour each vertex with
its own index (`hasColoring_self`) and embed into `r + 1` colours (`hasColoring_mono`). -/
theorem hasColoring_of_card_le {r n : ℕ} (hn : n ≤ r + 1) (G : SGraph n) :
    G.hasColoring (r + 1) :=
  SGraph.hasColoring_mono G hn (SGraph.hasColoring_self G)

/-- **The degenerate (upper) regime `n ≤ r + 1`.** Every graph on `n ≤ r + 1` vertices is
already `(r+1)`-colorable, so *every* budget forces the conclusion and the defining set is all
of `ℕ`: `fThresholdSet r n = Set.univ`. This is the `sSup`-pathology the parent file documents
in prose — the degenerate counterpart of the non-degenerate interval characterization
`fThresholdSet_eq_Iic`. (Here `fThreshold r n = sSup Set.univ`, the artifact value.) -/
theorem fThresholdSet_eq_univ_of_card_le {r n : ℕ} (hn : n ≤ r + 1) :
    fThresholdSet r n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro k G _
  exact hasColoring_of_card_le hn G

#check @completeGraph_not_hasColoring
#check @canReduce_removeAll
#check @fThresholdSet_downClosed
#check @fThresholdSet_bddAbove
#check @fThreshold_le_sq
#check @fThresholdSet_zero_mem
#check @fThreshold_mem
#check @mem_fThresholdSet_iff
#check @fThresholdSet_eq_Iic
#check @hasColoring_of_card_le
#check @fThresholdSet_eq_univ_of_card_le

end Erdos1092OQ02
