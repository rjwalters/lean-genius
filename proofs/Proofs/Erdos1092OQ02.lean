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

No new axioms; the two `axiom`s in the parent file are untouched (and unused here).
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

#check @completeGraph_not_hasColoring
#check @canReduce_removeAll
#check @fThresholdSet_downClosed
#check @fThresholdSet_bddAbove
#check @fThreshold_le_sq

end Erdos1092OQ02
